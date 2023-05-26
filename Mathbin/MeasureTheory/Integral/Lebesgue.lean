/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl

! This file was ported from Lean 3 source module measure_theory.integral.lebesgue
! leanprover-community/mathlib commit 4280f5f32e16755ec7985ce11e189b6cd6ff6735
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Dynamics.Ergodic.MeasurePreserving
import Mathbin.MeasureTheory.Function.SimpleFunc
import Mathbin.MeasureTheory.Measure.MutuallySingular

/-!
# Lower Lebesgue integral for `ℝ≥0∞`-valued functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define the lower Lebesgue integral of an `ℝ≥0∞`-valued function.

## Notation

We introduce the following notation for the lower Lebesgue integral of a function `f : α → ℝ≥0∞`.

* `∫⁻ x, f x ∂μ`: integral of a function `f : α → ℝ≥0∞` with respect to a measure `μ`;
* `∫⁻ x, f x`: integral of a function `f : α → ℝ≥0∞` with respect to the canonical measure
  `volume` on `α`;
* `∫⁻ x in s, f x ∂μ`: integral of a function `f : α → ℝ≥0∞` over a set `s` with respect
  to a measure `μ`, defined as `∫⁻ x, f x ∂(μ.restrict s)`;
* `∫⁻ x in s, f x`: integral of a function `f : α → ℝ≥0∞` over a set `s` with respect
  to the canonical measure `volume`, defined as `∫⁻ x, f x ∂(volume.restrict s)`.

-/


noncomputable section

open Set hiding restrict restrict_apply

open Filter ENNReal

open Function (support)

open Classical Topology BigOperators NNReal ENNReal MeasureTheory

namespace MeasureTheory

section MoveThis

variable {α : Type _} {mα : MeasurableSpace α} {a : α} {s : Set α}

include mα

#print MeasureTheory.restrict_dirac' /-
-- todo after the port: move to measure_theory/measure/measure_space
theorem restrict_dirac' (hs : MeasurableSet s) [Decidable (a ∈ s)] :
    (Measure.dirac a).restrict s = if a ∈ s then Measure.dirac a else 0 :=
  by
  ext1 t ht
  classical
    simp only [measure.restrict_apply ht, measure.dirac_apply' _ (ht.inter hs), Set.indicator_apply,
      Set.mem_inter_iff, Pi.one_apply]
    by_cases has : a ∈ s
    · simp only [has, and_true_iff, if_true]
      split_ifs with hat
      · rw [measure.dirac_apply_of_mem hat]
      · simp only [measure.dirac_apply' _ ht, Set.indicator_apply, hat, if_false]
    · simp only [has, and_false_iff, if_false, measure.coe_zero, Pi.zero_apply]
#align measure_theory.restrict_dirac' MeasureTheory.restrict_dirac'
-/

#print MeasureTheory.restrict_dirac /-
-- todo after the port: move to measure_theory/measure/measure_space
theorem restrict_dirac [MeasurableSingletonClass α] [Decidable (a ∈ s)] :
    (Measure.dirac a).restrict s = if a ∈ s then Measure.dirac a else 0 :=
  by
  ext1 t ht
  classical
    simp only [measure.restrict_apply ht, measure.dirac_apply _, Set.indicator_apply,
      Set.mem_inter_iff, Pi.one_apply]
    by_cases has : a ∈ s
    · simp only [has, and_true_iff, if_true]
      split_ifs with hat
      · rw [measure.dirac_apply_of_mem hat]
      · simp only [measure.dirac_apply' _ ht, Set.indicator_apply, hat, if_false]
    · simp only [has, and_false_iff, if_false, measure.coe_zero, Pi.zero_apply]
#align measure_theory.restrict_dirac MeasureTheory.restrict_dirac
-/

end MoveThis

-- mathport name: «expr →ₛ »
local infixr:25 " →ₛ " => SimpleFunc

variable {α β γ δ : Type _}

section Lintegral

open SimpleFunc

variable {m : MeasurableSpace α} {μ ν : Measure α}

#print MeasureTheory.lintegral /-
/-- The **lower Lebesgue integral** of a function `f` with respect to a measure `μ`. -/
irreducible_def lintegral {m : MeasurableSpace α} (μ : Measure α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (g : α →ₛ ℝ≥0∞) (hf : ⇑g ≤ f), g.lintegral μ
#align measure_theory.lintegral MeasureTheory.lintegral
-/

/-! In the notation for integrals, an expression like `∫⁻ x, g ‖x‖ ∂μ` will not be parsed correctly,
  and needs parentheses. We do not set the binding power of `r` to `0`, because then
  `∫⁻ x, f x = 0` will be parsed incorrectly. -/


-- mathport name: «expr∫⁻ , ∂ »
notation3"∫⁻ "(...)", "r:(scoped f => f)" ∂"μ => lintegral μ r

-- mathport name: «expr∫⁻ , »
notation3"∫⁻ "(...)", "r:(scoped f => lintegral volume f) => r

-- mathport name: «expr∫⁻ in , ∂ »
notation3"∫⁻ "(...)" in "s", "r:(scoped f => f)" ∂"μ => lintegral (Measure.restrict μ s) r

-- mathport name: «expr∫⁻ in , »
notation3"∫⁻ "(...)" in "s", "r:(scoped f => lintegral Measure.restrict volume s f) => r

#print MeasureTheory.SimpleFunc.lintegral_eq_lintegral /-
theorem SimpleFunc.lintegral_eq_lintegral {m : MeasurableSpace α} (f : α →ₛ ℝ≥0∞) (μ : Measure α) :
    (∫⁻ a, f a ∂μ) = f.lintegral μ := by
  rw [lintegral]
  exact
    le_antisymm (iSup₂_le fun g hg => lintegral_mono hg <| le_rfl) (le_iSup₂_of_le f le_rfl le_rfl)
#align measure_theory.simple_func.lintegral_eq_lintegral MeasureTheory.SimpleFunc.lintegral_eq_lintegral
-/

/- warning: measure_theory.lintegral_mono' -> MeasureTheory.lintegral_mono' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {{μ : MeasureTheory.Measure.{u1} α m}} {{ν : MeasureTheory.Measure.{u1} α m}}, (LE.le.{u1} (MeasureTheory.Measure.{u1} α m) (Preorder.toHasLe.{u1} (MeasureTheory.Measure.{u1} α m) (PartialOrder.toPreorder.{u1} (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.instPartialOrder.{u1} α m))) μ ν) -> (forall {{f : α -> ENNReal}} {{g : α -> ENNReal}}, (LE.le.{u1} (α -> ENNReal) (Pi.hasLe.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))) f g) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (MeasureTheory.lintegral.{u1} α m ν (fun (a : α) => g a))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {{μ : MeasureTheory.Measure.{u1} α m}} {{ν : MeasureTheory.Measure.{u1} α m}}, (LE.le.{u1} (MeasureTheory.Measure.{u1} α m) (Preorder.toLE.{u1} (MeasureTheory.Measure.{u1} α m) (PartialOrder.toPreorder.{u1} (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.instPartialOrder.{u1} α m))) μ ν) -> (forall {{f : α -> ENNReal}} {{g : α -> ENNReal}}, (LE.le.{u1} (α -> ENNReal) (Pi.hasLe.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))) f g) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (MeasureTheory.lintegral.{u1} α m ν (fun (a : α) => g a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_mono' MeasureTheory.lintegral_mono'ₓ'. -/
@[mono]
theorem lintegral_mono' {m : MeasurableSpace α} ⦃μ ν : Measure α⦄ (hμν : μ ≤ ν) ⦃f g : α → ℝ≥0∞⦄
    (hfg : f ≤ g) : (∫⁻ a, f a ∂μ) ≤ ∫⁻ a, g a ∂ν :=
  by
  rw [lintegral, lintegral]
  exact iSup_mono fun φ => iSup_mono' fun hφ => ⟨le_trans hφ hfg, lintegral_mono (le_refl φ) hμν⟩
#align measure_theory.lintegral_mono' MeasureTheory.lintegral_mono'

/- warning: measure_theory.lintegral_mono -> MeasureTheory.lintegral_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {{f : α -> ENNReal}} {{g : α -> ENNReal}}, (LE.le.{u1} (α -> ENNReal) (Pi.hasLe.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))) f g) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {{f : α -> ENNReal}} {{g : α -> ENNReal}}, (LE.le.{u1} (α -> ENNReal) (Pi.hasLe.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))) f g) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a)))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_mono MeasureTheory.lintegral_monoₓ'. -/
theorem lintegral_mono ⦃f g : α → ℝ≥0∞⦄ (hfg : f ≤ g) : (∫⁻ a, f a ∂μ) ≤ ∫⁻ a, g a ∂μ :=
  lintegral_mono' (le_refl μ) hfg
#align measure_theory.lintegral_mono MeasureTheory.lintegral_mono

/- warning: measure_theory.lintegral_mono_nnreal -> MeasureTheory.lintegral_mono_nnreal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> NNReal} {g : α -> NNReal}, (LE.le.{u1} (α -> NNReal) (Pi.hasLe.{u1, 0} α (fun (ᾰ : α) => NNReal) (fun (i : α) => Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) f g) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (f a))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (g a))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> NNReal} {g : α -> NNReal}, (LE.le.{u1} (α -> NNReal) (Pi.hasLe.{u1, 0} α (fun (ᾰ : α) => NNReal) (fun (i : α) => Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)))) f g) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => ENNReal.some (f a))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => ENNReal.some (g a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_mono_nnreal MeasureTheory.lintegral_mono_nnrealₓ'. -/
theorem lintegral_mono_nnreal {f g : α → ℝ≥0} (h : f ≤ g) : (∫⁻ a, f a ∂μ) ≤ ∫⁻ a, g a ∂μ :=
  lintegral_mono fun a => ENNReal.coe_le_coe.2 (h a)
#align measure_theory.lintegral_mono_nnreal MeasureTheory.lintegral_mono_nnreal

/- warning: measure_theory.supr_lintegral_measurable_le_eq_lintegral -> MeasureTheory.iSup_lintegral_measurable_le_eq_lintegral is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : α -> ENNReal), Eq.{1} ENNReal (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (α -> ENNReal) (fun (g : α -> ENNReal) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace g) (fun (g_meas : Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace g) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (LE.le.{u1} (α -> ENNReal) (Pi.hasLe.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))) g f) (fun (hg : LE.le.{u1} (α -> ENNReal) (Pi.hasLe.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))) g f) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : α -> ENNReal), Eq.{1} ENNReal (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (α -> ENNReal) (fun (g : α -> ENNReal) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace g) (fun (g_meas : Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace g) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (LE.le.{u1} (α -> ENNReal) (Pi.hasLe.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))) g f) (fun (hg : LE.le.{u1} (α -> ENNReal) (Pi.hasLe.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))) g f) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a))
Case conversion may be inaccurate. Consider using '#align measure_theory.supr_lintegral_measurable_le_eq_lintegral MeasureTheory.iSup_lintegral_measurable_le_eq_lintegralₓ'. -/
theorem iSup_lintegral_measurable_le_eq_lintegral (f : α → ℝ≥0∞) :
    (⨆ (g : α → ℝ≥0∞) (g_meas : Measurable g) (hg : g ≤ f), ∫⁻ a, g a ∂μ) = ∫⁻ a, f a ∂μ :=
  by
  apply le_antisymm
  · exact iSup_le fun i => iSup_le fun hi => iSup_le fun h'i => lintegral_mono h'i
  · rw [lintegral]
    refine' iSup₂_le fun i hi => le_iSup₂_of_le i i.Measurable <| le_iSup_of_le hi _
    exact le_of_eq (i.lintegral_eq_lintegral _).symm
#align measure_theory.supr_lintegral_measurable_le_eq_lintegral MeasureTheory.iSup_lintegral_measurable_le_eq_lintegral

/- warning: measure_theory.lintegral_mono_set -> MeasureTheory.lintegral_mono_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {{μ : MeasureTheory.Measure.{u1} α m}} {s : Set.{u1} α} {t : Set.{u1} α} {f : α -> ENNReal}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => f x)) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ t) (fun (x : α) => f x)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {{μ : MeasureTheory.Measure.{u1} α m}} {s : Set.{u1} α} {t : Set.{u1} α} {f : α -> ENNReal}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => f x)) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ t) (fun (x : α) => f x)))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_mono_set MeasureTheory.lintegral_mono_setₓ'. -/
theorem lintegral_mono_set {m : MeasurableSpace α} ⦃μ : Measure α⦄ {s t : Set α} {f : α → ℝ≥0∞}
    (hst : s ⊆ t) : (∫⁻ x in s, f x ∂μ) ≤ ∫⁻ x in t, f x ∂μ :=
  lintegral_mono' (Measure.restrict_mono hst (le_refl μ)) (le_refl f)
#align measure_theory.lintegral_mono_set MeasureTheory.lintegral_mono_set

/- warning: measure_theory.lintegral_mono_set' -> MeasureTheory.lintegral_mono_set' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {{μ : MeasureTheory.Measure.{u1} α m}} {s : Set.{u1} α} {t : Set.{u1} α} {f : α -> ENNReal}, (Filter.EventuallyLE.{u1, 0} α Prop Prop.le (MeasureTheory.Measure.ae.{u1} α m μ) s t) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => f x)) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ t) (fun (x : α) => f x)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {{μ : MeasureTheory.Measure.{u1} α m}} {s : Set.{u1} α} {t : Set.{u1} α} {f : α -> ENNReal}, (Filter.EventuallyLE.{u1, 0} α Prop Prop.le (MeasureTheory.Measure.ae.{u1} α m μ) s t) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => f x)) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ t) (fun (x : α) => f x)))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_mono_set' MeasureTheory.lintegral_mono_set'ₓ'. -/
theorem lintegral_mono_set' {m : MeasurableSpace α} ⦃μ : Measure α⦄ {s t : Set α} {f : α → ℝ≥0∞}
    (hst : s ≤ᵐ[μ] t) : (∫⁻ x in s, f x ∂μ) ≤ ∫⁻ x in t, f x ∂μ :=
  lintegral_mono' (Measure.restrict_mono' hst (le_refl μ)) (le_refl f)
#align measure_theory.lintegral_mono_set' MeasureTheory.lintegral_mono_set'

/- warning: measure_theory.monotone_lintegral -> MeasureTheory.monotone_lintegral is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} (μ : MeasureTheory.Measure.{u1} α m), Monotone.{u1, 0} (α -> ENNReal) ENNReal (Pi.preorder.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (MeasureTheory.lintegral.{u1} α m μ)
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} (μ : MeasureTheory.Measure.{u1} α m), Monotone.{u1, 0} (α -> ENNReal) ENNReal (Pi.preorder.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (MeasureTheory.lintegral.{u1} α m μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.monotone_lintegral MeasureTheory.monotone_lintegralₓ'. -/
theorem monotone_lintegral {m : MeasurableSpace α} (μ : Measure α) : Monotone (lintegral μ) :=
  lintegral_mono
#align measure_theory.monotone_lintegral MeasureTheory.monotone_lintegral

/- warning: measure_theory.lintegral_const -> MeasureTheory.lintegral_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (c : ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => c)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) c (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (Set.univ.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (c : ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => c)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) c (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) (Set.univ.{u1} α)))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_const MeasureTheory.lintegral_constₓ'. -/
@[simp]
theorem lintegral_const (c : ℝ≥0∞) : (∫⁻ a, c ∂μ) = c * μ univ := by
  rw [← simple_func.const_lintegral, ← simple_func.lintegral_eq_lintegral, simple_func.coe_const]
#align measure_theory.lintegral_const MeasureTheory.lintegral_const

/- warning: measure_theory.lintegral_zero -> MeasureTheory.lintegral_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m}, Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m}, Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_zero MeasureTheory.lintegral_zeroₓ'. -/
theorem lintegral_zero : (∫⁻ a : α, 0 ∂μ) = 0 := by simp
#align measure_theory.lintegral_zero MeasureTheory.lintegral_zero

/- warning: measure_theory.lintegral_zero_fun -> MeasureTheory.lintegral_zero_fun is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m}, Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (OfNat.ofNat.{u1} (α -> ENNReal) 0 (OfNat.mk.{u1} (α -> ENNReal) 0 (Zero.zero.{u1} (α -> ENNReal) (Pi.instZero.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => ENNReal.hasZero)))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m}, Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (OfNat.ofNat.{u1} (α -> ENNReal) 0 (Zero.toOfNat0.{u1} (α -> ENNReal) (Pi.instZero.{u1, 0} α (fun (a._@.Mathlib.MeasureTheory.Integral.Lebesgue._hyg.5462 : α) => ENNReal) (fun (i : α) => instENNRealZero))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_zero_fun MeasureTheory.lintegral_zero_funₓ'. -/
theorem lintegral_zero_fun : lintegral μ (0 : α → ℝ≥0∞) = 0 :=
  lintegral_zero
#align measure_theory.lintegral_zero_fun MeasureTheory.lintegral_zero_fun

#print MeasureTheory.lintegral_one /-
@[simp]
theorem lintegral_one : (∫⁻ a, (1 : ℝ≥0∞) ∂μ) = μ univ := by rw [lintegral_const, one_mul]
#align measure_theory.lintegral_one MeasureTheory.lintegral_one
-/

/- warning: measure_theory.set_lintegral_const -> MeasureTheory.set_lintegral_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (s : Set.{u1} α) (c : ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (a : α) => c)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) c (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ s))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (s : Set.{u1} α) (c : ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (a : α) => c)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) c (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) s))
Case conversion may be inaccurate. Consider using '#align measure_theory.set_lintegral_const MeasureTheory.set_lintegral_constₓ'. -/
theorem set_lintegral_const (s : Set α) (c : ℝ≥0∞) : (∫⁻ a in s, c ∂μ) = c * μ s := by
  rw [lintegral_const, measure.restrict_apply_univ]
#align measure_theory.set_lintegral_const MeasureTheory.set_lintegral_const

#print MeasureTheory.set_lintegral_one /-
theorem set_lintegral_one (s) : (∫⁻ a in s, 1 ∂μ) = μ s := by rw [set_lintegral_const, one_mul]
#align measure_theory.set_lintegral_one MeasureTheory.set_lintegral_one
-/

/- warning: measure_theory.set_lintegral_const_lt_top -> MeasureTheory.set_lintegral_const_lt_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : MeasureTheory.FiniteMeasure.{u1} α m μ] (s : Set.{u1} α) {c : ENNReal}, (Ne.{1} ENNReal c (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (a : α) => c)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : MeasureTheory.FiniteMeasure.{u1} α m μ] (s : Set.{u1} α) {c : ENNReal}, (Ne.{1} ENNReal c (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (a : α) => c)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align measure_theory.set_lintegral_const_lt_top MeasureTheory.set_lintegral_const_lt_topₓ'. -/
theorem set_lintegral_const_lt_top [FiniteMeasure μ] (s : Set α) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    (∫⁻ a in s, c ∂μ) < ∞ := by
  rw [lintegral_const]
  exact ENNReal.mul_lt_top hc (measure_ne_top (μ.restrict s) univ)
#align measure_theory.set_lintegral_const_lt_top MeasureTheory.set_lintegral_const_lt_top

/- warning: measure_theory.lintegral_const_lt_top -> MeasureTheory.lintegral_const_lt_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : MeasureTheory.FiniteMeasure.{u1} α m μ] {c : ENNReal}, (Ne.{1} ENNReal c (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => c)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : MeasureTheory.FiniteMeasure.{u1} α m μ] {c : ENNReal}, (Ne.{1} ENNReal c (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => c)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_const_lt_top MeasureTheory.lintegral_const_lt_topₓ'. -/
theorem lintegral_const_lt_top [FiniteMeasure μ] {c : ℝ≥0∞} (hc : c ≠ ∞) : (∫⁻ a, c ∂μ) < ∞ := by
  simpa only [measure.restrict_univ] using set_lintegral_const_lt_top univ hc
#align measure_theory.lintegral_const_lt_top MeasureTheory.lintegral_const_lt_top

section

variable (μ)

/- warning: measure_theory.exists_measurable_le_lintegral_eq -> MeasureTheory.exists_measurable_le_lintegral_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} (μ : MeasureTheory.Measure.{u1} α m) (f : α -> ENNReal), Exists.{succ u1} (α -> ENNReal) (fun (g : α -> ENNReal) => And (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace g) (And (LE.le.{u1} (α -> ENNReal) (Pi.hasLe.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))) g f) (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a)))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} (μ : MeasureTheory.Measure.{u1} α m) (f : α -> ENNReal), Exists.{succ u1} (α -> ENNReal) (fun (g : α -> ENNReal) => And (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace g) (And (LE.le.{u1} (α -> ENNReal) (Pi.hasLe.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))) g f) (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.exists_measurable_le_lintegral_eq MeasureTheory.exists_measurable_le_lintegral_eqₓ'. -/
/-- For any function `f : α → ℝ≥0∞`, there exists a measurable function `g ≤ f` with the same
integral. -/
theorem exists_measurable_le_lintegral_eq (f : α → ℝ≥0∞) :
    ∃ g : α → ℝ≥0∞, Measurable g ∧ g ≤ f ∧ (∫⁻ a, f a ∂μ) = ∫⁻ a, g a ∂μ :=
  by
  cases' eq_or_ne (∫⁻ a, f a ∂μ) 0 with h₀ h₀
  · exact ⟨0, measurable_zero, zero_le f, h₀.trans lintegral_zero.symm⟩
  rcases exists_seq_strictMono_tendsto' h₀.bot_lt with ⟨L, hL_mono, hLf, hL_tendsto⟩
  have : ∀ n, ∃ g : α → ℝ≥0∞, Measurable g ∧ g ≤ f ∧ L n < ∫⁻ a, g a ∂μ :=
    by
    intro n
    simpa only [← supr_lintegral_measurable_le_eq_lintegral f, lt_iSup_iff, exists_prop] using
      (hLf n).2
  choose g hgm hgf hLg
  refine'
    ⟨fun x => ⨆ n, g n x, measurable_iSup hgm, fun x => iSup_le fun n => hgf n x, le_antisymm _ _⟩
  · refine' le_of_tendsto' hL_tendsto fun n => (hLg n).le.trans <| lintegral_mono fun x => _
    exact le_iSup (fun n => g n x) n
  · exact lintegral_mono fun x => iSup_le fun n => hgf n x
#align measure_theory.exists_measurable_le_lintegral_eq MeasureTheory.exists_measurable_le_lintegral_eq

end

/- warning: measure_theory.lintegral_eq_nnreal -> MeasureTheory.lintegral_eq_nnreal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} (f : α -> ENNReal) (μ : MeasureTheory.Measure.{u1} α m), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) (fun (φ : MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (forall (x : α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (coeFn.{succ u1, succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) (fun (_x : MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) => α -> NNReal) (MeasureTheory.SimpleFunc.instCoeFun.{u1, 0} α NNReal m) φ x)) (f x)) (fun (hf : forall (x : α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (coeFn.{succ u1, succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) (fun (_x : MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) => α -> NNReal) (MeasureTheory.SimpleFunc.instCoeFun.{u1, 0} α NNReal m) φ x)) (f x)) => MeasureTheory.SimpleFunc.lintegral.{u1} α m (MeasureTheory.SimpleFunc.map.{u1, 0, 0} α NNReal ENNReal m ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe)))) φ) μ)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} (f : α -> ENNReal) (μ : MeasureTheory.Measure.{u1} α m), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) (fun (φ : MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (forall (x : α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (ENNReal.some (MeasureTheory.SimpleFunc.toFun.{u1, 0} α m NNReal φ x)) (f x)) (fun (hf : forall (x : α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (ENNReal.some (MeasureTheory.SimpleFunc.toFun.{u1, 0} α m NNReal φ x)) (f x)) => MeasureTheory.SimpleFunc.lintegral.{u1} α m (MeasureTheory.SimpleFunc.map.{u1, 0, 0} α NNReal ENNReal m ENNReal.some φ) μ)))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_eq_nnreal MeasureTheory.lintegral_eq_nnrealₓ'. -/
/-- `∫⁻ a in s, f a ∂μ` is defined as the supremum of integrals of simple functions
`φ : α →ₛ ℝ≥0∞` such that `φ ≤ f`. This lemma says that it suffices to take
functions `φ : α →ₛ ℝ≥0`. -/
theorem lintegral_eq_nnreal {m : MeasurableSpace α} (f : α → ℝ≥0∞) (μ : Measure α) :
    (∫⁻ a, f a ∂μ) =
      ⨆ (φ : α →ₛ ℝ≥0) (hf : ∀ x, ↑(φ x) ≤ f x), (φ.map (coe : ℝ≥0 → ℝ≥0∞)).lintegral μ :=
  by
  rw [lintegral]
  refine'
    le_antisymm (iSup₂_le fun φ hφ => _) (iSup_mono' fun φ => ⟨φ.map (coe : ℝ≥0 → ℝ≥0∞), le_rfl⟩)
  by_cases h : ∀ᵐ a ∂μ, φ a ≠ ∞
  · let ψ := φ.map ENNReal.toNNReal
    replace h : ψ.map (coe : ℝ≥0 → ℝ≥0∞) =ᵐ[μ] φ := h.mono fun a => ENNReal.coe_toNNReal
    have : ∀ x, ↑(ψ x) ≤ f x := fun x => le_trans ENNReal.coe_toNNReal_le_self (hφ x)
    exact
      le_iSup_of_le (φ.map ENNReal.toNNReal) (le_iSup_of_le this (ge_of_eq <| lintegral_congr h))
  · have h_meas : μ (φ ⁻¹' {∞}) ≠ 0 := mt measure_zero_iff_ae_nmem.1 h
    refine' le_trans le_top (ge_of_eq <| (iSup_eq_top _).2 fun b hb => _)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, b < n * μ (φ ⁻¹' {∞})
    exact exists_nat_mul_gt h_meas (ne_of_lt hb)
    use (const α (n : ℝ≥0)).restrict (φ ⁻¹' {∞})
    simp only [lt_iSup_iff, exists_prop, coe_restrict, φ.measurable_set_preimage, coe_const,
      ENNReal.coe_indicator, map_coe_ennreal_restrict, simple_func.map_const, ENNReal.coe_nat,
      restrict_const_lintegral]
    refine' ⟨indicator_le fun x hx => le_trans _ (hφ _), hn⟩
    simp only [mem_preimage, mem_singleton_iff] at hx
    simp only [hx, le_top]
#align measure_theory.lintegral_eq_nnreal MeasureTheory.lintegral_eq_nnreal

/- warning: measure_theory.exists_simple_func_forall_lintegral_sub_lt_of_pos -> MeasureTheory.exists_simpleFunc_forall_lintegral_sub_lt_of_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (forall {ε : ENNReal}, (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) (fun (φ : MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) => And (forall (x : α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (coeFn.{succ u1, succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) (fun (_x : MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) => α -> NNReal) (MeasureTheory.SimpleFunc.instCoeFun.{u1, 0} α NNReal m) φ x)) (f x)) (forall (ψ : MeasureTheory.SimpleFunc.{u1, 0} α m NNReal), (forall (x : α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (coeFn.{succ u1, succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) (fun (_x : MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) => α -> NNReal) (MeasureTheory.SimpleFunc.instCoeFun.{u1, 0} α NNReal m) ψ x)) (f x)) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.SimpleFunc.lintegral.{u1} α m (MeasureTheory.SimpleFunc.map.{u1, 0, 0} α NNReal ENNReal m ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe)))) (HSub.hSub.{u1, u1, u1} (MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) (MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) (MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) (instHSub.{u1} (MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) (MeasureTheory.SimpleFunc.instSub.{u1, 0} α NNReal m NNReal.hasSub)) ψ φ)) μ) ε)))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (forall {ε : ENNReal}, (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) (fun (φ : MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) => And (forall (x : α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (ENNReal.some (MeasureTheory.SimpleFunc.toFun.{u1, 0} α m NNReal φ x)) (f x)) (forall (ψ : MeasureTheory.SimpleFunc.{u1, 0} α m NNReal), (forall (x : α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (ENNReal.some (MeasureTheory.SimpleFunc.toFun.{u1, 0} α m NNReal ψ x)) (f x)) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.SimpleFunc.lintegral.{u1} α m (MeasureTheory.SimpleFunc.map.{u1, 0, 0} α NNReal ENNReal m ENNReal.some (HSub.hSub.{u1, u1, u1} (MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) (MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) (MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) (instHSub.{u1} (MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) (MeasureTheory.SimpleFunc.instSub.{u1, 0} α NNReal m NNReal.instSubNNReal)) ψ φ)) μ) ε)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.exists_simple_func_forall_lintegral_sub_lt_of_pos MeasureTheory.exists_simpleFunc_forall_lintegral_sub_lt_of_posₓ'. -/
theorem exists_simpleFunc_forall_lintegral_sub_lt_of_pos {f : α → ℝ≥0∞} (h : (∫⁻ x, f x ∂μ) ≠ ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ φ : α →ₛ ℝ≥0,
      (∀ x, ↑(φ x) ≤ f x) ∧
        ∀ ψ : α →ₛ ℝ≥0, (∀ x, ↑(ψ x) ≤ f x) → (map coe (ψ - φ)).lintegral μ < ε :=
  by
  rw [lintegral_eq_nnreal] at h
  have := ENNReal.lt_add_right h hε
  erw [ENNReal.biSup_add] at this <;> [skip;exact ⟨0, fun x => zero_le _⟩]
  simp_rw [lt_iSup_iff, iSup_lt_iff, iSup_le_iff] at this
  rcases this with ⟨φ, hle : ∀ x, ↑(φ x) ≤ f x, b, hbφ, hb⟩
  refine' ⟨φ, hle, fun ψ hψ => _⟩
  have : (map coe φ).lintegral μ ≠ ∞ := ne_top_of_le_ne_top h (le_iSup₂ φ hle)
  rw [← ENNReal.add_lt_add_iff_left this, ← add_lintegral, ← map_add @ENNReal.coe_add]
  refine' (hb _ fun x => le_trans _ (max_le (hle x) (hψ x))).trans_lt hbφ
  norm_cast
  simp only [add_apply, sub_apply, add_tsub_eq_max]
#align measure_theory.exists_simple_func_forall_lintegral_sub_lt_of_pos MeasureTheory.exists_simpleFunc_forall_lintegral_sub_lt_of_pos

/- warning: measure_theory.supr_lintegral_le -> MeasureTheory.iSup_lintegral_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {ι : Sort.{u2}} (f : ι -> α -> ENNReal), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (iSup.{0, u2} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f i a))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => iSup.{0, u2} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => f i a)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {ι : Sort.{u2}} (f : ι -> α -> ENNReal), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (iSup.{0, u2} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f i a))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => iSup.{0, u2} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => f i a)))
Case conversion may be inaccurate. Consider using '#align measure_theory.supr_lintegral_le MeasureTheory.iSup_lintegral_leₓ'. -/
theorem iSup_lintegral_le {ι : Sort _} (f : ι → α → ℝ≥0∞) :
    (⨆ i, ∫⁻ a, f i a ∂μ) ≤ ∫⁻ a, ⨆ i, f i a ∂μ :=
  by
  simp only [← iSup_apply]
  exact (monotone_lintegral μ).le_map_iSup
#align measure_theory.supr_lintegral_le MeasureTheory.iSup_lintegral_le

/- warning: measure_theory.supr₂_lintegral_le -> MeasureTheory.iSup₂_lintegral_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {ι : Sort.{u2}} {ι' : ι -> Sort.{u3}} (f : forall (i : ι), (ι' i) -> α -> ENNReal), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (iSup.{0, u2} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => iSup.{0, u3} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (ι' i) (fun (j : ι' i) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f i j a)))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => iSup.{0, u2} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => iSup.{0, u3} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (ι' i) (fun (j : ι' i) => f i j a))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {ι : Sort.{u3}} {ι' : ι -> Sort.{u2}} (f : forall (i : ι), (ι' i) -> α -> ENNReal), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (iSup.{0, u3} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => iSup.{0, u2} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (ι' i) (fun (j : ι' i) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f i j a)))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => iSup.{0, u3} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => iSup.{0, u2} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (ι' i) (fun (j : ι' i) => f i j a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.supr₂_lintegral_le MeasureTheory.iSup₂_lintegral_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem iSup₂_lintegral_le {ι : Sort _} {ι' : ι → Sort _} (f : ∀ i, ι' i → α → ℝ≥0∞) :
    (⨆ (i) (j), ∫⁻ a, f i j a ∂μ) ≤ ∫⁻ a, ⨆ (i) (j), f i j a ∂μ :=
  by
  convert(monotone_lintegral μ).le_map_iSup₂ f
  ext1 a
  simp only [iSup_apply]
#align measure_theory.supr₂_lintegral_le MeasureTheory.iSup₂_lintegral_le

/- warning: measure_theory.le_infi_lintegral -> MeasureTheory.le_iInf_lintegral is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {ι : Sort.{u2}} (f : ι -> α -> ENNReal), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => iInf.{0, u2} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => f i a))) (iInf.{0, u2} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f i a)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {ι : Sort.{u2}} (f : ι -> α -> ENNReal), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => iInf.{0, u2} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => f i a))) (iInf.{0, u2} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f i a)))
Case conversion may be inaccurate. Consider using '#align measure_theory.le_infi_lintegral MeasureTheory.le_iInf_lintegralₓ'. -/
theorem le_iInf_lintegral {ι : Sort _} (f : ι → α → ℝ≥0∞) :
    (∫⁻ a, ⨅ i, f i a ∂μ) ≤ ⨅ i, ∫⁻ a, f i a ∂μ :=
  by
  simp only [← iInf_apply]
  exact (monotone_lintegral μ).map_iInf_le
#align measure_theory.le_infi_lintegral MeasureTheory.le_iInf_lintegral

/- warning: measure_theory.le_infi₂_lintegral -> MeasureTheory.le_iInf₂_lintegral is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {ι : Sort.{u2}} {ι' : ι -> Sort.{u3}} (f : forall (i : ι), (ι' i) -> α -> ENNReal), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => iInf.{0, u2} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => iInf.{0, u3} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (ι' i) (fun (h : ι' i) => f i h a)))) (iInf.{0, u2} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => iInf.{0, u3} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (ι' i) (fun (h : ι' i) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f i h a))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {ι : Sort.{u3}} {ι' : ι -> Sort.{u2}} (f : forall (i : ι), (ι' i) -> α -> ENNReal), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => iInf.{0, u3} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => iInf.{0, u2} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (ι' i) (fun (h : ι' i) => f i h a)))) (iInf.{0, u3} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => iInf.{0, u2} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (ι' i) (fun (h : ι' i) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f i h a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.le_infi₂_lintegral MeasureTheory.le_iInf₂_lintegralₓ'. -/
theorem le_iInf₂_lintegral {ι : Sort _} {ι' : ι → Sort _} (f : ∀ i, ι' i → α → ℝ≥0∞) :
    (∫⁻ a, ⨅ (i) (h : ι' i), f i h a ∂μ) ≤ ⨅ (i) (h : ι' i), ∫⁻ a, f i h a ∂μ :=
  by
  convert(monotone_lintegral μ).map_iInf₂_le f
  ext1 a
  simp only [iInf_apply]
#align measure_theory.le_infi₂_lintegral MeasureTheory.le_iInf₂_lintegral

/- warning: measure_theory.lintegral_mono_ae -> MeasureTheory.lintegral_mono_ae is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal} {g : α -> ENNReal}, (Filter.Eventually.{u1} α (fun (a : α) => LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (f a) (g a)) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal} {g : α -> ENNReal}, (Filter.Eventually.{u1} α (fun (a : α) => LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (f a) (g a)) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a)))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_mono_ae MeasureTheory.lintegral_mono_aeₓ'. -/
theorem lintegral_mono_ae {f g : α → ℝ≥0∞} (h : ∀ᵐ a ∂μ, f a ≤ g a) :
    (∫⁻ a, f a ∂μ) ≤ ∫⁻ a, g a ∂μ :=
  by
  rcases exists_measurable_superset_of_null h with ⟨t, hts, ht, ht0⟩
  have : ∀ᵐ x ∂μ, x ∉ t := measure_zero_iff_ae_nmem.1 ht0
  rw [lintegral, lintegral]
  refine' iSup_le fun s => iSup_le fun hfs => le_iSup_of_le (s.restrict (tᶜ)) <| le_iSup_of_le _ _
  · intro a
    by_cases a ∈ t <;> simp [h, restrict_apply, ht.compl]
    exact le_trans (hfs a) (by_contradiction fun hnfg => h (hts hnfg))
  · refine' le_of_eq (simple_func.lintegral_congr <| this.mono fun a hnt => _)
    by_cases hat : a ∈ t <;> simp [hat, ht.compl]
    exact (hnt hat).elim
#align measure_theory.lintegral_mono_ae MeasureTheory.lintegral_mono_ae

/- warning: measure_theory.set_lintegral_mono_ae -> MeasureTheory.set_lintegral_mono_ae is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {f : α -> ENNReal} {g : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace g) -> (Filter.Eventually.{u1} α (fun (x : α) => (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (f x) (g x))) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => f x)) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => g x)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {f : α -> ENNReal} {g : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace g) -> (Filter.Eventually.{u1} α (fun (x : α) => (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (f x) (g x))) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => f x)) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => g x)))
Case conversion may be inaccurate. Consider using '#align measure_theory.set_lintegral_mono_ae MeasureTheory.set_lintegral_mono_aeₓ'. -/
theorem set_lintegral_mono_ae {s : Set α} {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → f x ≤ g x) : (∫⁻ x in s, f x ∂μ) ≤ ∫⁻ x in s, g x ∂μ :=
  lintegral_mono_ae <| (ae_restrict_iff <| measurableSet_le hf hg).2 hfg
#align measure_theory.set_lintegral_mono_ae MeasureTheory.set_lintegral_mono_ae

/- warning: measure_theory.set_lintegral_mono -> MeasureTheory.set_lintegral_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {f : α -> ENNReal} {g : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace g) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (f x) (g x))) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => f x)) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => g x)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α} {f : α -> ENNReal} {g : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace g) -> (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (f x) (g x))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => f x)) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => g x)))
Case conversion may be inaccurate. Consider using '#align measure_theory.set_lintegral_mono MeasureTheory.set_lintegral_monoₓ'. -/
theorem set_lintegral_mono {s : Set α} {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ x ∈ s, f x ≤ g x) : (∫⁻ x in s, f x ∂μ) ≤ ∫⁻ x in s, g x ∂μ :=
  set_lintegral_mono_ae hf hg (ae_of_all _ hfg)
#align measure_theory.set_lintegral_mono MeasureTheory.set_lintegral_mono

#print MeasureTheory.lintegral_congr_ae /-
theorem lintegral_congr_ae {f g : α → ℝ≥0∞} (h : f =ᵐ[μ] g) : (∫⁻ a, f a ∂μ) = ∫⁻ a, g a ∂μ :=
  le_antisymm (lintegral_mono_ae <| h.le) (lintegral_mono_ae <| h.symm.le)
#align measure_theory.lintegral_congr_ae MeasureTheory.lintegral_congr_ae
-/

#print MeasureTheory.lintegral_congr /-
theorem lintegral_congr {f g : α → ℝ≥0∞} (h : ∀ a, f a = g a) : (∫⁻ a, f a ∂μ) = ∫⁻ a, g a ∂μ := by
  simp only [h]
#align measure_theory.lintegral_congr MeasureTheory.lintegral_congr
-/

#print MeasureTheory.set_lintegral_congr /-
theorem set_lintegral_congr {f : α → ℝ≥0∞} {s t : Set α} (h : s =ᵐ[μ] t) :
    (∫⁻ x in s, f x ∂μ) = ∫⁻ x in t, f x ∂μ := by rw [measure.restrict_congr_set h]
#align measure_theory.set_lintegral_congr MeasureTheory.set_lintegral_congr
-/

#print MeasureTheory.set_lintegral_congr_fun /-
theorem set_lintegral_congr_fun {f g : α → ℝ≥0∞} {s : Set α} (hs : MeasurableSet s)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → f x = g x) : (∫⁻ x in s, f x ∂μ) = ∫⁻ x in s, g x ∂μ :=
  by
  rw [lintegral_congr_ae]
  rw [eventually_eq]
  rwa [ae_restrict_iff' hs]
#align measure_theory.set_lintegral_congr_fun MeasureTheory.set_lintegral_congr_fun
-/

/- warning: measure_theory.lintegral_of_real_le_lintegral_nnnorm -> MeasureTheory.lintegral_ofReal_le_lintegral_nnnorm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : α -> Real), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => ENNReal.ofReal (f x))) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (NNNorm.nnnorm.{0} Real (SeminormedAddGroup.toNNNorm.{0} Real (SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real (NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))) (f x))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : α -> Real), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => ENNReal.ofReal (f x))) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => ENNReal.some (NNNorm.nnnorm.{0} Real (SeminormedAddGroup.toNNNorm.{0} Real (SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real (NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))) (f x))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_of_real_le_lintegral_nnnorm MeasureTheory.lintegral_ofReal_le_lintegral_nnnormₓ'. -/
theorem lintegral_ofReal_le_lintegral_nnnorm (f : α → ℝ) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ∫⁻ x, ‖f x‖₊ ∂μ :=
  by
  simp_rw [← ofReal_norm_eq_coe_nnnorm]
  refine' lintegral_mono fun x => ENNReal.ofReal_le_ofReal _
  rw [Real.norm_eq_abs]
  exact le_abs_self (f x)
#align measure_theory.lintegral_of_real_le_lintegral_nnnorm MeasureTheory.lintegral_ofReal_le_lintegral_nnnorm

/- warning: measure_theory.lintegral_nnnorm_eq_of_ae_nonneg -> MeasureTheory.lintegral_nnnorm_eq_of_ae_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> Real}, (Filter.EventuallyLE.{u1, 0} α Real Real.hasLe (MeasureTheory.Measure.ae.{u1} α m μ) (OfNat.ofNat.{u1} (α -> Real) 0 (OfNat.mk.{u1} (α -> Real) 0 (Zero.zero.{u1} (α -> Real) (Pi.instZero.{u1, 0} α (fun (ᾰ : α) => Real) (fun (i : α) => Real.hasZero))))) f) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (NNNorm.nnnorm.{0} Real (SeminormedAddGroup.toNNNorm.{0} Real (SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real (NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))) (f x)))) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => ENNReal.ofReal (f x))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> Real}, (Filter.EventuallyLE.{u1, 0} α Real Real.instLEReal (MeasureTheory.Measure.ae.{u1} α m μ) (OfNat.ofNat.{u1} (α -> Real) 0 (Zero.toOfNat0.{u1} (α -> Real) (Pi.instZero.{u1, 0} α (fun (a._@.Mathlib.Order.Filter.Basic._hyg.21854 : α) => Real) (fun (i : α) => Real.instZeroReal)))) f) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => ENNReal.some (NNNorm.nnnorm.{0} Real (SeminormedAddGroup.toNNNorm.{0} Real (SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real (NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))) (f x)))) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => ENNReal.ofReal (f x))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_nnnorm_eq_of_ae_nonneg MeasureTheory.lintegral_nnnorm_eq_of_ae_nonnegₓ'. -/
theorem lintegral_nnnorm_eq_of_ae_nonneg {f : α → ℝ} (h_nonneg : 0 ≤ᵐ[μ] f) :
    (∫⁻ x, ‖f x‖₊ ∂μ) = ∫⁻ x, ENNReal.ofReal (f x) ∂μ :=
  by
  apply lintegral_congr_ae
  filter_upwards [h_nonneg]with x hx
  rw [Real.nnnorm_of_nonneg hx, ENNReal.ofReal_eq_coe_nnreal hx]
#align measure_theory.lintegral_nnnorm_eq_of_ae_nonneg MeasureTheory.lintegral_nnnorm_eq_of_ae_nonneg

/- warning: measure_theory.lintegral_nnnorm_eq_of_nonneg -> MeasureTheory.lintegral_nnnorm_eq_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> Real}, (LE.le.{u1} (α -> Real) (Pi.hasLe.{u1, 0} α (fun (ᾰ : α) => Real) (fun (i : α) => Real.hasLe)) (OfNat.ofNat.{u1} (α -> Real) 0 (OfNat.mk.{u1} (α -> Real) 0 (Zero.zero.{u1} (α -> Real) (Pi.instZero.{u1, 0} α (fun (ᾰ : α) => Real) (fun (i : α) => Real.hasZero))))) f) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (NNNorm.nnnorm.{0} Real (SeminormedAddGroup.toNNNorm.{0} Real (SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real (NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))) (f x)))) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => ENNReal.ofReal (f x))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> Real}, (LE.le.{u1} (α -> Real) (Pi.hasLe.{u1, 0} α (fun (ᾰ : α) => Real) (fun (i : α) => Real.instLEReal)) (OfNat.ofNat.{u1} (α -> Real) 0 (Zero.toOfNat0.{u1} (α -> Real) (Pi.instZero.{u1, 0} α (fun (a._@.Mathlib.MeasureTheory.Integral.Lebesgue._hyg.9034 : α) => Real) (fun (i : α) => Real.instZeroReal)))) f) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => ENNReal.some (NNNorm.nnnorm.{0} Real (SeminormedAddGroup.toNNNorm.{0} Real (SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real (NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup))) (f x)))) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => ENNReal.ofReal (f x))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_nnnorm_eq_of_nonneg MeasureTheory.lintegral_nnnorm_eq_of_nonnegₓ'. -/
theorem lintegral_nnnorm_eq_of_nonneg {f : α → ℝ} (h_nonneg : 0 ≤ f) :
    (∫⁻ x, ‖f x‖₊ ∂μ) = ∫⁻ x, ENNReal.ofReal (f x) ∂μ :=
  lintegral_nnnorm_eq_of_ae_nonneg (Filter.eventually_of_forall h_nonneg)
#align measure_theory.lintegral_nnnorm_eq_of_nonneg MeasureTheory.lintegral_nnnorm_eq_of_nonneg

/- warning: measure_theory.lintegral_supr -> MeasureTheory.lintegral_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : Nat -> α -> ENNReal}, (forall (n : Nat), Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace (f n)) -> (Monotone.{0, u1} Nat (α -> ENNReal) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (Pi.preorder.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) f) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => iSup.{0, 1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) Nat (fun (n : Nat) => f n a))) (iSup.{0, 1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) Nat (fun (n : Nat) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f n a))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : Nat -> α -> ENNReal}, (forall (n : Nat), Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace (f n)) -> (Monotone.{0, u1} Nat (α -> ENNReal) (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (Pi.preorder.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) f) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => iSup.{0, 1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) Nat (fun (n : Nat) => f n a))) (iSup.{0, 1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) Nat (fun (n : Nat) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f n a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_supr MeasureTheory.lintegral_iSupₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:132:4: warning: unsupported: rw with cfg: { occs := occurrences.pos[occurrences.pos] «expr[ ,]»([1]) } -/
/-- Monotone convergence theorem -- sometimes called Beppo-Levi convergence.

See `lintegral_supr_directed` for a more general form. -/
theorem lintegral_iSup {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, Measurable (f n)) (h_mono : Monotone f) :
    (∫⁻ a, ⨆ n, f n a ∂μ) = ⨆ n, ∫⁻ a, f n a ∂μ :=
  by
  set c : ℝ≥0 → ℝ≥0∞ := coe
  set F := fun a : α => ⨆ n, f n a
  have hF : Measurable F := measurable_iSup hf
  refine' le_antisymm _ (supr_lintegral_le _)
  rw [lintegral_eq_nnreal]
  refine' iSup_le fun s => iSup_le fun hsf => _
  refine' ENNReal.le_of_forall_lt_one_mul_le fun a ha => _
  rcases ENNReal.lt_iff_exists_coe.1 ha with ⟨r, rfl, ha⟩
  have ha : r < 1 := ENNReal.coe_lt_coe.1 ha
  let rs := s.map fun a => r * a
  have eq_rs : (const α r : α →ₛ ℝ≥0∞) * map c s = rs.map c :=
    by
    ext1 a
    exact ennreal.coe_mul.symm
  have eq : ∀ p, rs.map c ⁻¹' {p} = ⋃ n, rs.map c ⁻¹' {p} ∩ { a | p ≤ f n a } :=
    by
    intro p
    rw [← inter_Union, ← inter_univ (map c rs ⁻¹' {p})]
    refine' Set.ext fun x => and_congr_right fun hx => (true_iff_iff _).2 _
    by_cases p_eq : p = 0
    · simp [p_eq]
    simp at hx
    subst hx
    have : r * s x ≠ 0 := by rwa [(· ≠ ·), ← ENNReal.coe_eq_zero]
    have : s x ≠ 0 := by
      refine' mt _ this
      intro h
      rw [h, MulZeroClass.mul_zero]
    have : (rs.map c) x < ⨆ n : ℕ, f n x :=
      by
      refine' lt_of_lt_of_le (ENNReal.coe_lt_coe.2 _) (hsf x)
      suffices : r * s x < 1 * s x
      simpa [rs]
      exact mul_lt_mul_of_pos_right ha (pos_iff_ne_zero.2 this)
    rcases lt_iSup_iff.1 this with ⟨i, hi⟩
    exact mem_Union.2 ⟨i, le_of_lt hi⟩
  have mono : ∀ r : ℝ≥0∞, Monotone fun n => rs.map c ⁻¹' {r} ∩ { a | r ≤ f n a } :=
    by
    intro r i j h
    refine' inter_subset_inter (subset.refl _) _
    intro x hx
    exact le_trans hx (h_mono h x)
  have h_meas : ∀ n, MeasurableSet { a : α | (⇑(map c rs)) a ≤ f n a } := fun n =>
    measurableSet_le (simple_func.measurable _) (hf n)
  calc
    (r : ℝ≥0∞) * (s.map c).lintegral μ = ∑ r in (rs.map c).range, r * μ (rs.map c ⁻¹' {r}) := by
      rw [← const_mul_lintegral, eq_rs, simple_func.lintegral]
    _ = ∑ r in (rs.map c).range, r * μ (⋃ n, rs.map c ⁻¹' {r} ∩ { a | r ≤ f n a }) := by
      simp only [(Eq _).symm]
    _ = ∑ r in (rs.map c).range, ⨆ n, r * μ (rs.map c ⁻¹' {r} ∩ { a | r ≤ f n a }) :=
      (Finset.sum_congr rfl fun x hx => by
        rw [measure_Union_eq_supr (directed_of_sup <| mono x), ENNReal.mul_iSup])
    _ = ⨆ n, ∑ r in (rs.map c).range, r * μ (rs.map c ⁻¹' {r} ∩ { a | r ≤ f n a }) :=
      by
      rw [ENNReal.finset_sum_iSup_nat]
      intro p i j h
      exact mul_le_mul_left' (measure_mono <| mono p h) _
    _ ≤ ⨆ n : ℕ, ((rs.map c).restrict { a | (rs.map c) a ≤ f n a }).lintegral μ :=
      by
      refine' iSup_mono fun n => _
      rw [restrict_lintegral _ (h_meas n)]
      · refine' le_of_eq (Finset.sum_congr rfl fun r hr => _)
        congr 2 with a
        refine' and_congr_right _
        simp (config := { contextual := true })
    _ ≤ ⨆ n, ∫⁻ a, f n a ∂μ := by
      refine' iSup_mono fun n => _
      rw [← simple_func.lintegral_eq_lintegral]
      refine' lintegral_mono fun a => _
      simp only [map_apply] at h_meas
      simp only [coe_map, restrict_apply _ (h_meas _), (· ∘ ·)]
      exact indicator_apply_le id
    
#align measure_theory.lintegral_supr MeasureTheory.lintegral_iSup

/- warning: measure_theory.lintegral_supr' -> MeasureTheory.lintegral_iSup' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : Nat -> α -> ENNReal}, (forall (n : Nat), AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m (f n) μ) -> (Filter.Eventually.{u1} α (fun (x : α) => Monotone.{0, 0} Nat ENNReal (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (fun (n : Nat) => f n x)) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => iSup.{0, 1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) Nat (fun (n : Nat) => f n a))) (iSup.{0, 1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) Nat (fun (n : Nat) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f n a))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : Nat -> α -> ENNReal}, (forall (n : Nat), AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m (f n) μ) -> (Filter.Eventually.{u1} α (fun (x : α) => Monotone.{0, 0} Nat ENNReal (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (fun (n : Nat) => f n x)) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => iSup.{0, 1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) Nat (fun (n : Nat) => f n a))) (iSup.{0, 1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) Nat (fun (n : Nat) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f n a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_supr' MeasureTheory.lintegral_iSup'ₓ'. -/
/-- Monotone convergence theorem -- sometimes called Beppo-Levi convergence. Version with
ae_measurable functions. -/
theorem lintegral_iSup' {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, AEMeasurable (f n) μ)
    (h_mono : ∀ᵐ x ∂μ, Monotone fun n => f n x) : (∫⁻ a, ⨆ n, f n a ∂μ) = ⨆ n, ∫⁻ a, f n a ∂μ :=
  by
  simp_rw [← iSup_apply]
  let p : α → (ℕ → ℝ≥0∞) → Prop := fun x f' => Monotone f'
  have hp : ∀ᵐ x ∂μ, p x fun i => f i x := h_mono
  have h_ae_seq_mono : Monotone (aeSeq hf p) :=
    by
    intro n m hnm x
    by_cases hx : x ∈ aeSeqSet hf p
    · exact aeSeq.prop_of_mem_aeSeqSet hf hx hnm
    · simp only [aeSeq, hx, if_false]
      exact le_rfl
  rw [lintegral_congr_ae (aeSeq.iSup hf hp).symm]
  simp_rw [iSup_apply]
  rw [@lintegral_supr _ _ μ _ (aeSeq.measurable hf p) h_ae_seq_mono]
  congr
  exact funext fun n => lintegral_congr_ae (aeSeq.aeSeq_n_eq_fun_n_ae hf hp n)
#align measure_theory.lintegral_supr' MeasureTheory.lintegral_iSup'

/- warning: measure_theory.lintegral_tendsto_of_tendsto_of_monotone -> MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : Nat -> α -> ENNReal} {F : α -> ENNReal}, (forall (n : Nat), AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m (f n) μ) -> (Filter.Eventually.{u1} α (fun (x : α) => Monotone.{0, 0} Nat ENNReal (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (fun (n : Nat) => f n x)) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (Filter.Eventually.{u1} α (fun (x : α) => Filter.Tendsto.{0, 0} Nat ENNReal (fun (n : Nat) => f n x) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} ENNReal ENNReal.topologicalSpace (F x))) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (Filter.Tendsto.{0, 0} Nat ENNReal (fun (n : Nat) => MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f n x)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} ENNReal ENNReal.topologicalSpace (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => F x))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : Nat -> α -> ENNReal} {F : α -> ENNReal}, (forall (n : Nat), AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m (f n) μ) -> (Filter.Eventually.{u1} α (fun (x : α) => Monotone.{0, 0} Nat ENNReal (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (fun (n : Nat) => f n x)) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (Filter.Eventually.{u1} α (fun (x : α) => Filter.Tendsto.{0, 0} Nat ENNReal (fun (n : Nat) => f n x) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (F x))) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (Filter.Tendsto.{0, 0} Nat ENNReal (fun (n : Nat) => MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f n x)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => F x))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_tendsto_of_tendsto_of_monotone MeasureTheory.lintegral_tendsto_of_tendsto_of_monotoneₓ'. -/
/-- Monotone convergence theorem expressed with limits -/
theorem lintegral_tendsto_of_tendsto_of_monotone {f : ℕ → α → ℝ≥0∞} {F : α → ℝ≥0∞}
    (hf : ∀ n, AEMeasurable (f n) μ) (h_mono : ∀ᵐ x ∂μ, Monotone fun n => f n x)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 <| F x)) :
    Tendsto (fun n => ∫⁻ x, f n x ∂μ) atTop (𝓝 <| ∫⁻ x, F x ∂μ) :=
  by
  have : Monotone fun n => ∫⁻ x, f n x ∂μ := fun i j hij =>
    lintegral_mono_ae (h_mono.mono fun x hx => hx hij)
  suffices key : (∫⁻ x, F x ∂μ) = ⨆ n, ∫⁻ x, f n x ∂μ
  · rw [key]
    exact tendsto_atTop_iSup this
  rw [← lintegral_supr' hf h_mono]
  refine' lintegral_congr_ae _
  filter_upwards [h_mono,
    h_tendsto]with _ hx_mono hx_tendsto using tendsto_nhds_unique hx_tendsto
      (tendsto_atTop_iSup hx_mono)
#align measure_theory.lintegral_tendsto_of_tendsto_of_monotone MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone

/- warning: measure_theory.lintegral_eq_supr_eapprox_lintegral -> MeasureTheory.lintegral_eq_iSup_eapprox_lintegral is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (iSup.{0, 1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) Nat (fun (n : Nat) => MeasureTheory.SimpleFunc.lintegral.{u1} α m (MeasureTheory.SimpleFunc.eapprox.{u1} α m f n) μ)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (iSup.{0, 1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) Nat (fun (n : Nat) => MeasureTheory.SimpleFunc.lintegral.{u1} α m (MeasureTheory.SimpleFunc.eapprox.{u1} α m f n) μ)))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_eq_supr_eapprox_lintegral MeasureTheory.lintegral_eq_iSup_eapprox_lintegralₓ'. -/
theorem lintegral_eq_iSup_eapprox_lintegral {f : α → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ a, f a ∂μ) = ⨆ n, (eapprox f n).lintegral μ :=
  calc
    (∫⁻ a, f a ∂μ) = ∫⁻ a, ⨆ n, (eapprox f n : α → ℝ≥0∞) a ∂μ := by
      congr <;> ext a <;> rw [supr_eapprox_apply f hf]
    _ = ⨆ n, ∫⁻ a, (eapprox f n : α → ℝ≥0∞) a ∂μ :=
      by
      rw [lintegral_supr]
      · measurability
      · intro i j h
        exact monotone_eapprox f h
    _ = ⨆ n, (eapprox f n).lintegral μ := by
      congr <;> ext n <;> rw [(eapprox f n).lintegral_eq_lintegral]
    
#align measure_theory.lintegral_eq_supr_eapprox_lintegral MeasureTheory.lintegral_eq_iSup_eapprox_lintegral

/- warning: measure_theory.exists_pos_set_lintegral_lt_of_measure_lt -> MeasureTheory.exists_pos_set_lintegral_lt_of_measure_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (forall {ε : ENNReal}, (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{1} ENNReal (fun (δ : ENNReal) => Exists.{0} (GT.gt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) δ (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (fun (H : GT.gt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) δ (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) => forall (s : Set.{u1} α), (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ s) δ) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => f x)) ε)))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (forall {ε : ENNReal}, (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{1} ENNReal (fun (δ : ENNReal) => And (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) δ (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (forall (s : Set.{u1} α), (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) s) δ) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => f x)) ε)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.exists_pos_set_lintegral_lt_of_measure_lt MeasureTheory.exists_pos_set_lintegral_lt_of_measure_ltₓ'. -/
/-- If `f` has finite integral, then `∫⁻ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. This lemma states states this fact in terms of `ε` and `δ`. -/
theorem exists_pos_set_lintegral_lt_of_measure_lt {f : α → ℝ≥0∞} (h : (∫⁻ x, f x ∂μ) ≠ ∞) {ε : ℝ≥0∞}
    (hε : ε ≠ 0) : ∃ δ > 0, ∀ s, μ s < δ → (∫⁻ x in s, f x ∂μ) < ε :=
  by
  rcases exists_between hε.bot_lt with ⟨ε₂, hε₂0 : 0 < ε₂, hε₂ε⟩
  rcases exists_between hε₂0 with ⟨ε₁, hε₁0, hε₁₂⟩
  rcases exists_simple_func_forall_lintegral_sub_lt_of_pos h hε₁0.ne' with ⟨φ, hle, hφ⟩
  rcases φ.exists_forall_le with ⟨C, hC⟩
  use (ε₂ - ε₁) / C, ENNReal.div_pos_iff.2 ⟨(tsub_pos_iff_lt.2 hε₁₂).ne', ENNReal.coe_ne_top⟩
  refine' fun s hs => lt_of_le_of_lt _ hε₂ε
  simp only [lintegral_eq_nnreal, iSup_le_iff]
  intro ψ hψ
  calc
    (map coe ψ).lintegral (μ.restrict s) ≤
        (map coe φ).lintegral (μ.restrict s) + (map coe (ψ - φ)).lintegral (μ.restrict s) :=
      by
      rw [← simple_func.add_lintegral, ← simple_func.map_add @ENNReal.coe_add]
      refine' simple_func.lintegral_mono (fun x => _) le_rfl
      simp only [add_tsub_eq_max, le_max_right, coe_map, Function.comp_apply, simple_func.coe_add,
        simple_func.coe_sub, Pi.add_apply, Pi.sub_apply, WithTop.coe_max]
    _ ≤ (map coe φ).lintegral (μ.restrict s) + ε₁ :=
      by
      refine' add_le_add le_rfl (le_trans _ (hφ _ hψ).le)
      exact simple_func.lintegral_mono le_rfl measure.restrict_le_self
    _ ≤ (simple_func.const α (C : ℝ≥0∞)).lintegral (μ.restrict s) + ε₁ :=
      (add_le_add (simple_func.lintegral_mono (fun x => coe_le_coe.2 (hC x)) le_rfl) le_rfl)
    _ = C * μ s + ε₁ := by
      simp only [← simple_func.lintegral_eq_lintegral, coe_const, lintegral_const,
        measure.restrict_apply, MeasurableSet.univ, univ_inter]
    _ ≤ C * ((ε₂ - ε₁) / C) + ε₁ := (add_le_add_right (mul_le_mul_left' hs.le _) _)
    _ ≤ ε₂ - ε₁ + ε₁ := (add_le_add mul_div_le le_rfl)
    _ = ε₂ := tsub_add_cancel_of_le hε₁₂.le
    
#align measure_theory.exists_pos_set_lintegral_lt_of_measure_lt MeasureTheory.exists_pos_set_lintegral_lt_of_measure_lt

/- warning: measure_theory.tendsto_set_lintegral_zero -> MeasureTheory.tendsto_set_lintegral_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {ι : Type.{u2}} {f : α -> ENNReal}, (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (forall {l : Filter.{u2} ι} {s : ι -> (Set.{u1} α)}, (Filter.Tendsto.{u2, 0} ι ENNReal (Function.comp.{succ u2, succ u1, 1} ι (Set.{u1} α) ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ) s) l (nhds.{0} ENNReal ENNReal.topologicalSpace (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))) -> (Filter.Tendsto.{u2, 0} ι ENNReal (fun (i : ι) => MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (s i)) (fun (x : α) => f x)) l (nhds.{0} ENNReal ENNReal.topologicalSpace (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {ι : Type.{u2}} {f : α -> ENNReal}, (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (forall {l : Filter.{u2} ι} {s : ι -> (Set.{u1} α)}, (Filter.Tendsto.{u2, 0} ι ENNReal (Function.comp.{succ u2, succ u1, 1} ι (Set.{u1} α) ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ)) s) l (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))) -> (Filter.Tendsto.{u2, 0} ι ENNReal (fun (i : ι) => MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (s i)) (fun (x : α) => f x)) l (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.tendsto_set_lintegral_zero MeasureTheory.tendsto_set_lintegral_zeroₓ'. -/
/-- If `f` has finite integral, then `∫⁻ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. -/
theorem tendsto_set_lintegral_zero {ι} {f : α → ℝ≥0∞} (h : (∫⁻ x, f x ∂μ) ≠ ∞) {l : Filter ι}
    {s : ι → Set α} (hl : Tendsto (μ ∘ s) l (𝓝 0)) :
    Tendsto (fun i => ∫⁻ x in s i, f x ∂μ) l (𝓝 0) :=
  by
  simp only [ENNReal.nhds_zero, tendsto_infi, tendsto_principal, mem_Iio, ← pos_iff_ne_zero] at hl⊢
  intro ε ε0
  rcases exists_pos_set_lintegral_lt_of_measure_lt h ε0.ne' with ⟨δ, δ0, hδ⟩
  exact (hl δ δ0).mono fun i => hδ _
#align measure_theory.tendsto_set_lintegral_zero MeasureTheory.tendsto_set_lintegral_zero

/- warning: measure_theory.le_lintegral_add -> MeasureTheory.le_lintegral_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : α -> ENNReal) (g : α -> ENNReal), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f a) (g a)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : α -> ENNReal) (g : α -> ENNReal), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (f a) (g a)))
Case conversion may be inaccurate. Consider using '#align measure_theory.le_lintegral_add MeasureTheory.le_lintegral_addₓ'. -/
/-- The sum of the lower Lebesgue integrals of two functions is less than or equal to the integral
of their sum. The other inequality needs one of these functions to be (a.e.-)measurable. -/
theorem le_lintegral_add (f g : α → ℝ≥0∞) : ((∫⁻ a, f a ∂μ) + ∫⁻ a, g a ∂μ) ≤ ∫⁻ a, f a + g a ∂μ :=
  by
  dsimp only [lintegral]
  refine' ENNReal.biSup_add_biSup_le' ⟨0, zero_le f⟩ ⟨0, zero_le g⟩ fun f' hf' g' hg' => _
  exact le_iSup₂_of_le (f' + g') (add_le_add hf' hg') (add_lintegral _ _).ge
#align measure_theory.le_lintegral_add MeasureTheory.le_lintegral_add

/- warning: measure_theory.lintegral_add_aux -> MeasureTheory.lintegral_add_aux is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal} {g : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace g) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f a) (g a))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal} {g : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace g) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (f a) (g a))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_add_aux MeasureTheory.lintegral_add_auxₓ'. -/
-- Use stronger lemmas `lintegral_add_left`/`lintegral_add_right` instead
theorem lintegral_add_aux {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ a, f a + g a ∂μ) = (∫⁻ a, f a ∂μ) + ∫⁻ a, g a ∂μ :=
  calc
    (∫⁻ a, f a + g a ∂μ) =
        ∫⁻ a, (⨆ n, (eapprox f n : α → ℝ≥0∞) a) + ⨆ n, (eapprox g n : α → ℝ≥0∞) a ∂μ :=
      by simp only [supr_eapprox_apply, hf, hg]
    _ = ∫⁻ a, ⨆ n, (eapprox f n + eapprox g n : α → ℝ≥0∞) a ∂μ :=
      by
      congr ; funext a
      rw [ENNReal.iSup_add_iSup_of_monotone]; · rfl
      · intro i j h
        exact monotone_eapprox _ h a
      · intro i j h
        exact monotone_eapprox _ h a
    _ = ⨆ n, (eapprox f n).lintegral μ + (eapprox g n).lintegral μ :=
      by
      rw [lintegral_supr]
      · congr
        funext n
        rw [← simple_func.add_lintegral, ← simple_func.lintegral_eq_lintegral]
        rfl
      · measurability
      · intro i j h a
        exact add_le_add (monotone_eapprox _ h _) (monotone_eapprox _ h _)
    _ = (⨆ n, (eapprox f n).lintegral μ) + ⨆ n, (eapprox g n).lintegral μ := by
      refine' (ENNReal.iSup_add_iSup_of_monotone _ _).symm <;>
        · intro i j h
          exact simple_func.lintegral_mono (monotone_eapprox _ h) (le_refl μ)
    _ = (∫⁻ a, f a ∂μ) + ∫⁻ a, g a ∂μ := by
      rw [lintegral_eq_supr_eapprox_lintegral hf, lintegral_eq_supr_eapprox_lintegral hg]
    
#align measure_theory.lintegral_add_aux MeasureTheory.lintegral_add_aux

/- warning: measure_theory.lintegral_add_left -> MeasureTheory.lintegral_add_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (forall (g : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f a) (g a))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (forall (g : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (f a) (g a))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_add_left MeasureTheory.lintegral_add_leftₓ'. -/
/-- If `f g : α → ℝ≥0∞` are two functions and one of them is (a.e.) measurable, then the Lebesgue
integral of `f + g` equals the sum of integrals. This lemma assumes that `f` is integrable, see also
`measure_theory.lintegral_add_right` and primed versions of these lemmas. -/
@[simp]
theorem lintegral_add_left {f : α → ℝ≥0∞} (hf : Measurable f) (g : α → ℝ≥0∞) :
    (∫⁻ a, f a + g a ∂μ) = (∫⁻ a, f a ∂μ) + ∫⁻ a, g a ∂μ :=
  by
  refine' le_antisymm _ (le_lintegral_add _ _)
  rcases exists_measurable_le_lintegral_eq μ fun a => f a + g a with ⟨φ, hφm, hφ_le, hφ_eq⟩
  calc
    (∫⁻ a, f a + g a ∂μ) = ∫⁻ a, φ a ∂μ := hφ_eq
    _ ≤ ∫⁻ a, f a + (φ a - f a) ∂μ := (lintegral_mono fun a => le_add_tsub)
    _ = (∫⁻ a, f a ∂μ) + ∫⁻ a, φ a - f a ∂μ := (lintegral_add_aux hf (hφm.sub hf))
    _ ≤ (∫⁻ a, f a ∂μ) + ∫⁻ a, g a ∂μ :=
      add_le_add_left (lintegral_mono fun a => tsub_le_iff_left.2 <| hφ_le a) _
    
#align measure_theory.lintegral_add_left MeasureTheory.lintegral_add_left

/- warning: measure_theory.lintegral_add_left' -> MeasureTheory.lintegral_add_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m f μ) -> (forall (g : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f a) (g a))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m f μ) -> (forall (g : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (f a) (g a))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_add_left' MeasureTheory.lintegral_add_left'ₓ'. -/
theorem lintegral_add_left' {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (g : α → ℝ≥0∞) :
    (∫⁻ a, f a + g a ∂μ) = (∫⁻ a, f a ∂μ) + ∫⁻ a, g a ∂μ := by
  rw [lintegral_congr_ae hf.ae_eq_mk, ← lintegral_add_left hf.measurable_mk,
    lintegral_congr_ae (hf.ae_eq_mk.add (ae_eq_refl g))]
#align measure_theory.lintegral_add_left' MeasureTheory.lintegral_add_left'

/- warning: measure_theory.lintegral_add_right' -> MeasureTheory.lintegral_add_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : α -> ENNReal) {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m g μ) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f a) (g a))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : α -> ENNReal) {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m g μ) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (f a) (g a))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_add_right' MeasureTheory.lintegral_add_right'ₓ'. -/
theorem lintegral_add_right' (f : α → ℝ≥0∞) {g : α → ℝ≥0∞} (hg : AEMeasurable g μ) :
    (∫⁻ a, f a + g a ∂μ) = (∫⁻ a, f a ∂μ) + ∫⁻ a, g a ∂μ := by
  simpa only [add_comm] using lintegral_add_left' hg f
#align measure_theory.lintegral_add_right' MeasureTheory.lintegral_add_right'

/- warning: measure_theory.lintegral_add_right -> MeasureTheory.lintegral_add_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : α -> ENNReal) {g : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace g) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f a) (g a))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : α -> ENNReal) {g : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace g) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (f a) (g a))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_add_right MeasureTheory.lintegral_add_rightₓ'. -/
/-- If `f g : α → ℝ≥0∞` are two functions and one of them is (a.e.) measurable, then the Lebesgue
integral of `f + g` equals the sum of integrals. This lemma assumes that `g` is integrable, see also
`measure_theory.lintegral_add_left` and primed versions of these lemmas. -/
@[simp]
theorem lintegral_add_right (f : α → ℝ≥0∞) {g : α → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ a, f a + g a ∂μ) = (∫⁻ a, f a ∂μ) + ∫⁻ a, g a ∂μ :=
  lintegral_add_right' f hg.AEMeasurable
#align measure_theory.lintegral_add_right MeasureTheory.lintegral_add_right

/- warning: measure_theory.lintegral_smul_measure -> MeasureTheory.lintegral_smul_measure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (c : ENNReal) (f : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (SMul.smul.{0, u1} ENNReal (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.instSMul.{u1, 0} α ENNReal (SMulZeroClass.toHasSmul.{0, 0} ENNReal ENNReal (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (SMulWithZero.toSmulZeroClass.{0, 0} ENNReal ENNReal (MulZeroClass.toHasZero.{0} ENNReal (MulZeroOneClass.toMulZeroClass.{0} ENNReal (MonoidWithZero.toMulZeroOneClass.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))) (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (MulActionWithZero.toSMulWithZero.{0, 0} ENNReal ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (Module.toMulActionWithZero.{0, 0} ENNReal ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))) (Algebra.toModule.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) (IsScalarTower.right.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) m) c μ) (fun (a : α) => f a)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) c (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (c : ENNReal) (f : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (HSMul.hSMul.{0, u1, u1} ENNReal (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.{u1} α m) (instHSMul.{0, u1} ENNReal (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.instSMul.{u1, 0} α ENNReal (Algebra.toSMul.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (IsScalarTower.right.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) m)) c μ) (fun (a : α) => f a)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) c (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_smul_measure MeasureTheory.lintegral_smul_measureₓ'. -/
@[simp]
theorem lintegral_smul_measure (c : ℝ≥0∞) (f : α → ℝ≥0∞) : (∫⁻ a, f a ∂c • μ) = c * ∫⁻ a, f a ∂μ :=
  by simp only [lintegral, iSup_subtype', simple_func.lintegral_smul, ENNReal.mul_iSup, smul_eq_mul]
#align measure_theory.lintegral_smul_measure MeasureTheory.lintegral_smul_measure

/- warning: measure_theory.lintegral_sum_measure -> MeasureTheory.lintegral_sum_measure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {ι : Type.{u2}} (f : α -> ENNReal) (μ : ι -> (MeasureTheory.Measure.{u1} α m)), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.sum.{u1, u2} α ι m μ) (fun (a : α) => f a)) (tsum.{0, u2} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace ι (fun (i : ι) => MeasureTheory.lintegral.{u1} α m (μ i) (fun (a : α) => f a)))
but is expected to have type
  forall {α : Type.{u2}} {m : MeasurableSpace.{u2} α} {ι : Type.{u1}} (f : α -> ENNReal) (μ : ι -> (MeasureTheory.Measure.{u2} α m)), Eq.{1} ENNReal (MeasureTheory.lintegral.{u2} α m (MeasureTheory.Measure.sum.{u2, u1} α ι m μ) (fun (a : α) => f a)) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal ι (fun (i : ι) => MeasureTheory.lintegral.{u2} α m (μ i) (fun (a : α) => f a)))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_sum_measure MeasureTheory.lintegral_sum_measureₓ'. -/
@[simp]
theorem lintegral_sum_measure {m : MeasurableSpace α} {ι} (f : α → ℝ≥0∞) (μ : ι → Measure α) :
    (∫⁻ a, f a ∂Measure.sum μ) = ∑' i, ∫⁻ a, f a ∂μ i :=
  by
  simp only [lintegral, iSup_subtype', simple_func.lintegral_sum, ENNReal.tsum_eq_iSup_sum]
  rw [iSup_comm]
  congr ; funext s
  induction' s using Finset.induction_on with i s hi hs;
  · apply bot_unique
    simp
  simp only [Finset.sum_insert hi, ← hs]
  refine' (ENNReal.iSup_add_iSup _).symm
  intro φ ψ
  exact
    ⟨⟨φ ⊔ ψ, fun x => sup_le (φ.2 x) (ψ.2 x)⟩,
      add_le_add (simple_func.lintegral_mono le_sup_left le_rfl)
        (Finset.sum_le_sum fun j hj => simple_func.lintegral_mono le_sup_right le_rfl)⟩
#align measure_theory.lintegral_sum_measure MeasureTheory.lintegral_sum_measure

/- warning: measure_theory.has_sum_lintegral_measure -> MeasureTheory.hasSum_lintegral_measure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {m : MeasurableSpace.{u1} α} (f : α -> ENNReal) (μ : ι -> (MeasureTheory.Measure.{u1} α m)), HasSum.{0, u2} ENNReal ι (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace (fun (i : ι) => MeasureTheory.lintegral.{u1} α m (μ i) (fun (a : α) => f a)) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.sum.{u1, u2} α ι m μ) (fun (a : α) => f a))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} {m : MeasurableSpace.{u1} α} (f : α -> ENNReal) (μ : ι -> (MeasureTheory.Measure.{u1} α m)), HasSum.{0, u2} ENNReal ι (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal (fun (i : ι) => MeasureTheory.lintegral.{u1} α m (μ i) (fun (a : α) => f a)) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.sum.{u1, u2} α ι m μ) (fun (a : α) => f a))
Case conversion may be inaccurate. Consider using '#align measure_theory.has_sum_lintegral_measure MeasureTheory.hasSum_lintegral_measureₓ'. -/
theorem hasSum_lintegral_measure {ι} {m : MeasurableSpace α} (f : α → ℝ≥0∞) (μ : ι → Measure α) :
    HasSum (fun i => ∫⁻ a, f a ∂μ i) (∫⁻ a, f a ∂Measure.sum μ) :=
  (lintegral_sum_measure f μ).symm ▸ ENNReal.summable.HasSum
#align measure_theory.has_sum_lintegral_measure MeasureTheory.hasSum_lintegral_measure

/- warning: measure_theory.lintegral_add_measure -> MeasureTheory.lintegral_add_measure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} (f : α -> ENNReal) (μ : MeasureTheory.Measure.{u1} α m) (ν : MeasureTheory.Measure.{u1} α m), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (HAdd.hAdd.{u1, u1, u1} (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.{u1} α m) (instHAdd.{u1} (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.instAdd.{u1} α m)) μ ν) (fun (a : α) => f a)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (MeasureTheory.lintegral.{u1} α m ν (fun (a : α) => f a)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} (f : α -> ENNReal) (μ : MeasureTheory.Measure.{u1} α m) (ν : MeasureTheory.Measure.{u1} α m), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (HAdd.hAdd.{u1, u1, u1} (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.{u1} α m) (instHAdd.{u1} (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.instAdd.{u1} α m)) μ ν) (fun (a : α) => f a)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (MeasureTheory.lintegral.{u1} α m ν (fun (a : α) => f a)))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_add_measure MeasureTheory.lintegral_add_measureₓ'. -/
@[simp]
theorem lintegral_add_measure {m : MeasurableSpace α} (f : α → ℝ≥0∞) (μ ν : Measure α) :
    (∫⁻ a, f a ∂μ + ν) = (∫⁻ a, f a ∂μ) + ∫⁻ a, f a ∂ν := by
  simpa [tsum_fintype] using lintegral_sum_measure f fun b => cond b μ ν
#align measure_theory.lintegral_add_measure MeasureTheory.lintegral_add_measure

/- warning: measure_theory.lintegral_finset_sum_measure -> MeasureTheory.lintegral_finset_sum_measure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {m : MeasurableSpace.{u1} α} (s : Finset.{u2} ι) (f : α -> ENNReal) (μ : ι -> (MeasureTheory.Measure.{u1} α m)), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (Finset.sum.{u1, u2} (MeasureTheory.Measure.{u1} α m) ι (MeasureTheory.Measure.instAddCommMonoid.{u1} α m) s (fun (i : ι) => μ i)) (fun (a : α) => f a)) (Finset.sum.{0, u2} ENNReal ι (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) s (fun (i : ι) => MeasureTheory.lintegral.{u1} α m (μ i) (fun (a : α) => f a)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} {m : MeasurableSpace.{u1} α} (s : Finset.{u2} ι) (f : α -> ENNReal) (μ : ι -> (MeasureTheory.Measure.{u1} α m)), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (Finset.sum.{u1, u2} (MeasureTheory.Measure.{u1} α m) ι (MeasureTheory.Measure.instAddCommMonoid.{u1} α m) s (fun (i : ι) => μ i)) (fun (a : α) => f a)) (Finset.sum.{0, u2} ENNReal ι (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) s (fun (i : ι) => MeasureTheory.lintegral.{u1} α m (μ i) (fun (a : α) => f a)))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_finset_sum_measure MeasureTheory.lintegral_finset_sum_measureₓ'. -/
@[simp]
theorem lintegral_finset_sum_measure {ι} {m : MeasurableSpace α} (s : Finset ι) (f : α → ℝ≥0∞)
    (μ : ι → Measure α) : (∫⁻ a, f a ∂∑ i in s, μ i) = ∑ i in s, ∫⁻ a, f a ∂μ i :=
  by
  rw [← measure.sum_coe_finset, lintegral_sum_measure, ← Finset.tsum_subtype']
  rfl
#align measure_theory.lintegral_finset_sum_measure MeasureTheory.lintegral_finset_sum_measure

/- warning: measure_theory.lintegral_zero_measure -> MeasureTheory.lintegral_zero_measure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} (f : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (OfNat.ofNat.{u1} (MeasureTheory.Measure.{u1} α m) 0 (OfNat.mk.{u1} (MeasureTheory.Measure.{u1} α m) 0 (Zero.zero.{u1} (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.instZero.{u1} α m)))) (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} (f : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (OfNat.ofNat.{u1} (MeasureTheory.Measure.{u1} α m) 0 (Zero.toOfNat0.{u1} (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.instZero.{u1} α m))) (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_zero_measure MeasureTheory.lintegral_zero_measureₓ'. -/
@[simp]
theorem lintegral_zero_measure {m : MeasurableSpace α} (f : α → ℝ≥0∞) :
    (∫⁻ a, f a ∂(0 : Measure α)) = 0 :=
  bot_unique <| by simp [lintegral]
#align measure_theory.lintegral_zero_measure MeasureTheory.lintegral_zero_measure

/- warning: measure_theory.set_lintegral_empty -> MeasureTheory.set_lintegral_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (fun (x : α) => f x)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (fun (x : α) => f x)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))
Case conversion may be inaccurate. Consider using '#align measure_theory.set_lintegral_empty MeasureTheory.set_lintegral_emptyₓ'. -/
theorem set_lintegral_empty (f : α → ℝ≥0∞) : (∫⁻ x in ∅, f x ∂μ) = 0 := by
  rw [measure.restrict_empty, lintegral_zero_measure]
#align measure_theory.set_lintegral_empty MeasureTheory.set_lintegral_empty

#print MeasureTheory.set_lintegral_univ /-
theorem set_lintegral_univ (f : α → ℝ≥0∞) : (∫⁻ x in univ, f x ∂μ) = ∫⁻ x, f x ∂μ := by
  rw [measure.restrict_univ]
#align measure_theory.set_lintegral_univ MeasureTheory.set_lintegral_univ
-/

/- warning: measure_theory.set_lintegral_measure_zero -> MeasureTheory.set_lintegral_measure_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (s : Set.{u1} α) (f : α -> ENNReal), (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => f x)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (s : Set.{u1} α) (f : α -> ENNReal), (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => f x)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align measure_theory.set_lintegral_measure_zero MeasureTheory.set_lintegral_measure_zeroₓ'. -/
theorem set_lintegral_measure_zero (s : Set α) (f : α → ℝ≥0∞) (hs' : μ s = 0) :
    (∫⁻ x in s, f x ∂μ) = 0 := by
  convert lintegral_zero_measure _
  exact measure.restrict_eq_zero.2 hs'
#align measure_theory.set_lintegral_measure_zero MeasureTheory.set_lintegral_measure_zero

/- warning: measure_theory.lintegral_finset_sum' -> MeasureTheory.lintegral_finset_sum' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (s : Finset.{u2} β) {f : β -> α -> ENNReal}, (forall (b : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) -> (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m (f b) μ)) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => Finset.sum.{0, u2} ENNReal β (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) s (fun (b : β) => f b a))) (Finset.sum.{0, u2} ENNReal β (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) s (fun (b : β) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f b a))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (s : Finset.{u2} β) {f : β -> α -> ENNReal}, (forall (b : β), (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b s) -> (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m (f b) μ)) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => Finset.sum.{0, u2} ENNReal β (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) s (fun (b : β) => f b a))) (Finset.sum.{0, u2} ENNReal β (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) s (fun (b : β) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f b a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_finset_sum' MeasureTheory.lintegral_finset_sum'ₓ'. -/
theorem lintegral_finset_sum' (s : Finset β) {f : β → α → ℝ≥0∞}
    (hf : ∀ b ∈ s, AEMeasurable (f b) μ) : (∫⁻ a, ∑ b in s, f b a ∂μ) = ∑ b in s, ∫⁻ a, f b a ∂μ :=
  by
  induction' s using Finset.induction_on with a s has ih
  · simp
  · simp only [Finset.sum_insert has]
    rw [Finset.forall_mem_insert] at hf
    rw [lintegral_add_left' hf.1, ih hf.2]
#align measure_theory.lintegral_finset_sum' MeasureTheory.lintegral_finset_sum'

/- warning: measure_theory.lintegral_finset_sum -> MeasureTheory.lintegral_finset_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (s : Finset.{u2} β) {f : β -> α -> ENNReal}, (forall (b : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) -> (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace (f b))) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => Finset.sum.{0, u2} ENNReal β (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) s (fun (b : β) => f b a))) (Finset.sum.{0, u2} ENNReal β (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) s (fun (b : β) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f b a))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (s : Finset.{u2} β) {f : β -> α -> ENNReal}, (forall (b : β), (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b s) -> (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace (f b))) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => Finset.sum.{0, u2} ENNReal β (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) s (fun (b : β) => f b a))) (Finset.sum.{0, u2} ENNReal β (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) s (fun (b : β) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f b a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_finset_sum MeasureTheory.lintegral_finset_sumₓ'. -/
theorem lintegral_finset_sum (s : Finset β) {f : β → α → ℝ≥0∞} (hf : ∀ b ∈ s, Measurable (f b)) :
    (∫⁻ a, ∑ b in s, f b a ∂μ) = ∑ b in s, ∫⁻ a, f b a ∂μ :=
  lintegral_finset_sum' s fun b hb => (hf b hb).AEMeasurable
#align measure_theory.lintegral_finset_sum MeasureTheory.lintegral_finset_sum

/- warning: measure_theory.lintegral_const_mul -> MeasureTheory.lintegral_const_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (r : ENNReal) {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) r (f a))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) r (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (r : ENNReal) {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) r (f a))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) r (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_const_mul MeasureTheory.lintegral_const_mulₓ'. -/
@[simp]
theorem lintegral_const_mul (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ a, r * f a ∂μ) = r * ∫⁻ a, f a ∂μ :=
  calc
    (∫⁻ a, r * f a ∂μ) = ∫⁻ a, ⨆ n, (const α r * eapprox f n) a ∂μ :=
      by
      congr
      funext a
      rw [← supr_eapprox_apply f hf, ENNReal.mul_iSup]
      rfl
    _ = ⨆ n, r * (eapprox f n).lintegral μ :=
      by
      rw [lintegral_supr]
      · congr
        funext n
        rw [← simple_func.const_mul_lintegral, ← simple_func.lintegral_eq_lintegral]
      · intro n
        exact simple_func.measurable _
      · intro i j h a
        exact mul_le_mul_left' (monotone_eapprox _ h _) _
    _ = r * ∫⁻ a, f a ∂μ := by rw [← ENNReal.mul_iSup, lintegral_eq_supr_eapprox_lintegral hf]
    
#align measure_theory.lintegral_const_mul MeasureTheory.lintegral_const_mul

/- warning: measure_theory.lintegral_const_mul'' -> MeasureTheory.lintegral_const_mul'' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (r : ENNReal) {f : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m f μ) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) r (f a))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) r (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (r : ENNReal) {f : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m f μ) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) r (f a))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) r (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_const_mul'' MeasureTheory.lintegral_const_mul''ₓ'. -/
theorem lintegral_const_mul'' (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    (∫⁻ a, r * f a ∂μ) = r * ∫⁻ a, f a ∂μ :=
  by
  have A : (∫⁻ a, f a ∂μ) = ∫⁻ a, hf.mk f a ∂μ := lintegral_congr_ae hf.ae_eq_mk
  have B : (∫⁻ a, r * f a ∂μ) = ∫⁻ a, r * hf.mk f a ∂μ :=
    lintegral_congr_ae (eventually_eq.fun_comp hf.ae_eq_mk _)
  rw [A, B, lintegral_const_mul _ hf.measurable_mk]
#align measure_theory.lintegral_const_mul'' MeasureTheory.lintegral_const_mul''

/- warning: measure_theory.lintegral_const_mul_le -> MeasureTheory.lintegral_const_mul_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (r : ENNReal) (f : α -> ENNReal), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) r (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) r (f a)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (r : ENNReal) (f : α -> ENNReal), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) r (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) r (f a)))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_const_mul_le MeasureTheory.lintegral_const_mul_leₓ'. -/
theorem lintegral_const_mul_le (r : ℝ≥0∞) (f : α → ℝ≥0∞) : (r * ∫⁻ a, f a ∂μ) ≤ ∫⁻ a, r * f a ∂μ :=
  by
  rw [lintegral, ENNReal.mul_iSup]
  refine' iSup_le fun s => _
  rw [ENNReal.mul_iSup]
  simp only [iSup_le_iff]
  intro hs
  rw [← simple_func.const_mul_lintegral, lintegral]
  refine' le_iSup_of_le (const α r * s) (le_iSup_of_le (fun x => _) le_rfl)
  exact mul_le_mul_left' (hs x) _
#align measure_theory.lintegral_const_mul_le MeasureTheory.lintegral_const_mul_le

/- warning: measure_theory.lintegral_const_mul' -> MeasureTheory.lintegral_const_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (r : ENNReal) (f : α -> ENNReal), (Ne.{1} ENNReal r (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) r (f a))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) r (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (r : ENNReal) (f : α -> ENNReal), (Ne.{1} ENNReal r (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) r (f a))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) r (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_const_mul' MeasureTheory.lintegral_const_mul'ₓ'. -/
theorem lintegral_const_mul' (r : ℝ≥0∞) (f : α → ℝ≥0∞) (hr : r ≠ ∞) :
    (∫⁻ a, r * f a ∂μ) = r * ∫⁻ a, f a ∂μ :=
  by
  by_cases h : r = 0
  · simp [h]
  apply le_antisymm _ (lintegral_const_mul_le r f)
  have rinv : r * r⁻¹ = 1 := ENNReal.mul_inv_cancel h hr
  have rinv' : r⁻¹ * r = 1 := by
    rw [mul_comm]
    exact rinv
  have := lintegral_const_mul_le r⁻¹ fun x => r * f x
  simp [(mul_assoc _ _ _).symm, rinv'] at this
  simpa [(mul_assoc _ _ _).symm, rinv] using mul_le_mul_left' this r
#align measure_theory.lintegral_const_mul' MeasureTheory.lintegral_const_mul'

/- warning: measure_theory.lintegral_mul_const -> MeasureTheory.lintegral_mul_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (r : ENNReal) {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f a) r)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) r))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (r : ENNReal) {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (f a) r)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) r))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_mul_const MeasureTheory.lintegral_mul_constₓ'. -/
theorem lintegral_mul_const (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ a, f a * r ∂μ) = (∫⁻ a, f a ∂μ) * r := by simp_rw [mul_comm, lintegral_const_mul r hf]
#align measure_theory.lintegral_mul_const MeasureTheory.lintegral_mul_const

/- warning: measure_theory.lintegral_mul_const'' -> MeasureTheory.lintegral_mul_const'' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (r : ENNReal) {f : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m f μ) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f a) r)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) r))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (r : ENNReal) {f : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m f μ) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (f a) r)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) r))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_mul_const'' MeasureTheory.lintegral_mul_const''ₓ'. -/
theorem lintegral_mul_const'' (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    (∫⁻ a, f a * r ∂μ) = (∫⁻ a, f a ∂μ) * r := by simp_rw [mul_comm, lintegral_const_mul'' r hf]
#align measure_theory.lintegral_mul_const'' MeasureTheory.lintegral_mul_const''

/- warning: measure_theory.lintegral_mul_const_le -> MeasureTheory.lintegral_mul_const_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (r : ENNReal) (f : α -> ENNReal), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) r) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f a) r))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (r : ENNReal) (f : α -> ENNReal), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) r) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (f a) r))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_mul_const_le MeasureTheory.lintegral_mul_const_leₓ'. -/
theorem lintegral_mul_const_le (r : ℝ≥0∞) (f : α → ℝ≥0∞) : (∫⁻ a, f a ∂μ) * r ≤ ∫⁻ a, f a * r ∂μ :=
  by simp_rw [mul_comm, lintegral_const_mul_le r f]
#align measure_theory.lintegral_mul_const_le MeasureTheory.lintegral_mul_const_le

/- warning: measure_theory.lintegral_mul_const' -> MeasureTheory.lintegral_mul_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (r : ENNReal) (f : α -> ENNReal), (Ne.{1} ENNReal r (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f a) r)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) r))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (r : ENNReal) (f : α -> ENNReal), (Ne.{1} ENNReal r (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (f a) r)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) r))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_mul_const' MeasureTheory.lintegral_mul_const'ₓ'. -/
theorem lintegral_mul_const' (r : ℝ≥0∞) (f : α → ℝ≥0∞) (hr : r ≠ ∞) :
    (∫⁻ a, f a * r ∂μ) = (∫⁻ a, f a ∂μ) * r := by simp_rw [mul_comm, lintegral_const_mul' r f hr]
#align measure_theory.lintegral_mul_const' MeasureTheory.lintegral_mul_const'

/- warning: measure_theory.lintegral_lintegral_mul -> MeasureTheory.lintegral_lintegral_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u2} β] {ν : MeasureTheory.Measure.{u2} β _inst_1} {f : α -> ENNReal} {g : β -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m f μ) -> (AEMeasurable.{u2, 0} β ENNReal ENNReal.measurableSpace _inst_1 g ν) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => MeasureTheory.lintegral.{u2} β _inst_1 ν (fun (y : β) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f x) (g y)))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (MeasureTheory.lintegral.{u2} β _inst_1 ν (fun (y : β) => g y))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u2} β] {ν : MeasureTheory.Measure.{u2} β _inst_1} {f : α -> ENNReal} {g : β -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m f μ) -> (AEMeasurable.{u2, 0} β ENNReal ENNReal.measurableSpace _inst_1 g ν) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => MeasureTheory.lintegral.{u2} β _inst_1 ν (fun (y : β) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (f x) (g y)))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (MeasureTheory.lintegral.{u2} β _inst_1 ν (fun (y : β) => g y))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_lintegral_mul MeasureTheory.lintegral_lintegral_mulₓ'. -/
/- A double integral of a product where each factor contains only one variable
  is a product of integrals -/
theorem lintegral_lintegral_mul {β} [MeasurableSpace β] {ν : Measure β} {f : α → ℝ≥0∞}
    {g : β → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g ν) :
    (∫⁻ x, ∫⁻ y, f x * g y ∂ν ∂μ) = (∫⁻ x, f x ∂μ) * ∫⁻ y, g y ∂ν := by
  simp [lintegral_const_mul'' _ hg, lintegral_mul_const'' _ hf]
#align measure_theory.lintegral_lintegral_mul MeasureTheory.lintegral_lintegral_mul

/- warning: measure_theory.lintegral_rw₁ -> MeasureTheory.lintegral_rw₁ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> β} {f' : α -> β}, (Filter.EventuallyEq.{u1, u2} α β (MeasureTheory.Measure.ae.{u1} α m μ) f f') -> (forall (g : β -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g (f a))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g (f' a))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} {f : α -> β} {f' : α -> β}, (Filter.EventuallyEq.{u2, u1} α β (MeasureTheory.Measure.ae.{u2} α m μ) f f') -> (forall (g : β -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u2} α m μ (fun (a : α) => g (f a))) (MeasureTheory.lintegral.{u2} α m μ (fun (a : α) => g (f' a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_rw₁ MeasureTheory.lintegral_rw₁ₓ'. -/
-- TODO: Need a better way of rewriting inside of a integral
theorem lintegral_rw₁ {f f' : α → β} (h : f =ᵐ[μ] f') (g : β → ℝ≥0∞) :
    (∫⁻ a, g (f a) ∂μ) = ∫⁻ a, g (f' a) ∂μ :=
  lintegral_congr_ae <| h.mono fun a h => by rw [h]
#align measure_theory.lintegral_rw₁ MeasureTheory.lintegral_rw₁

/- warning: measure_theory.lintegral_rw₂ -> MeasureTheory.lintegral_rw₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f₁ : α -> β} {f₁' : α -> β} {f₂ : α -> γ} {f₂' : α -> γ}, (Filter.EventuallyEq.{u1, u2} α β (MeasureTheory.Measure.ae.{u1} α m μ) f₁ f₁') -> (Filter.EventuallyEq.{u1, u3} α γ (MeasureTheory.Measure.ae.{u1} α m μ) f₂ f₂') -> (forall (g : β -> γ -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g (f₁ a) (f₂ a))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g (f₁' a) (f₂' a))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {m : MeasurableSpace.{u3} α} {μ : MeasureTheory.Measure.{u3} α m} {f₁ : α -> β} {f₁' : α -> β} {f₂ : α -> γ} {f₂' : α -> γ}, (Filter.EventuallyEq.{u3, u2} α β (MeasureTheory.Measure.ae.{u3} α m μ) f₁ f₁') -> (Filter.EventuallyEq.{u3, u1} α γ (MeasureTheory.Measure.ae.{u3} α m μ) f₂ f₂') -> (forall (g : β -> γ -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u3} α m μ (fun (a : α) => g (f₁ a) (f₂ a))) (MeasureTheory.lintegral.{u3} α m μ (fun (a : α) => g (f₁' a) (f₂' a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_rw₂ MeasureTheory.lintegral_rw₂ₓ'. -/
-- TODO: Need a better way of rewriting inside of a integral
theorem lintegral_rw₂ {f₁ f₁' : α → β} {f₂ f₂' : α → γ} (h₁ : f₁ =ᵐ[μ] f₁') (h₂ : f₂ =ᵐ[μ] f₂')
    (g : β → γ → ℝ≥0∞) : (∫⁻ a, g (f₁ a) (f₂ a) ∂μ) = ∫⁻ a, g (f₁' a) (f₂' a) ∂μ :=
  lintegral_congr_ae <| h₁.mp <| h₂.mono fun _ h₂ h₁ => by rw [h₁, h₂]
#align measure_theory.lintegral_rw₂ MeasureTheory.lintegral_rw₂

/- warning: measure_theory.lintegral_indicator -> MeasureTheory.lintegral_indicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : α -> ENNReal) {s : Set.{u1} α}, (MeasurableSet.{u1} α m s) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => Set.indicator.{u1, 0} α ENNReal ENNReal.hasZero s f a)) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (a : α) => f a)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : α -> ENNReal) {s : Set.{u1} α}, (MeasurableSet.{u1} α m s) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => Set.indicator.{u1, 0} α ENNReal instENNRealZero s f a)) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (a : α) => f a)))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_indicator MeasureTheory.lintegral_indicatorₓ'. -/
@[simp]
theorem lintegral_indicator (f : α → ℝ≥0∞) {s : Set α} (hs : MeasurableSet s) :
    (∫⁻ a, s.indicator f a ∂μ) = ∫⁻ a in s, f a ∂μ :=
  by
  simp only [lintegral, ← restrict_lintegral_eq_lintegral_restrict _ hs, iSup_subtype']
  apply le_antisymm <;> refine' iSup_mono' (Subtype.forall.2 fun φ hφ => _)
  · refine' ⟨⟨φ, le_trans hφ (indicator_le_self _ _)⟩, _⟩
    refine' simple_func.lintegral_mono (fun x => _) le_rfl
    by_cases hx : x ∈ s
    · simp [hx, hs, le_refl]
    · apply le_trans (hφ x)
      simp [hx, hs, le_refl]
  · refine' ⟨⟨φ.restrict s, fun x => _⟩, le_rfl⟩
    simp [hφ x, hs, indicator_le_indicator]
#align measure_theory.lintegral_indicator MeasureTheory.lintegral_indicator

/- warning: measure_theory.lintegral_indicator₀ -> MeasureTheory.lintegral_indicator₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : α -> ENNReal) {s : Set.{u1} α}, (MeasureTheory.NullMeasurableSet.{u1} α m s μ) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => Set.indicator.{u1, 0} α ENNReal ENNReal.hasZero s f a)) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (a : α) => f a)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : α -> ENNReal) {s : Set.{u1} α}, (MeasureTheory.NullMeasurableSet.{u1} α m s μ) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => Set.indicator.{u1, 0} α ENNReal instENNRealZero s f a)) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (a : α) => f a)))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_indicator₀ MeasureTheory.lintegral_indicator₀ₓ'. -/
theorem lintegral_indicator₀ (f : α → ℝ≥0∞) {s : Set α} (hs : NullMeasurableSet s μ) :
    (∫⁻ a, s.indicator f a ∂μ) = ∫⁻ a in s, f a ∂μ := by
  rw [← lintegral_congr_ae (indicator_ae_eq_of_ae_eq_set hs.to_measurable_ae_eq),
    lintegral_indicator _ (measurable_set_to_measurable _ _),
    measure.restrict_congr_set hs.to_measurable_ae_eq]
#align measure_theory.lintegral_indicator₀ MeasureTheory.lintegral_indicator₀

/- warning: measure_theory.lintegral_indicator_const -> MeasureTheory.lintegral_indicator_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α}, (MeasurableSet.{u1} α m s) -> (forall (c : ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => Set.indicator.{u1, 0} α ENNReal ENNReal.hasZero s (fun (_x : α) => c) a)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) c (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ s)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α}, (MeasurableSet.{u1} α m s) -> (forall (c : ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => Set.indicator.{u1, 0} α ENNReal instENNRealZero s (fun (_x : α) => c) a)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) c (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) s)))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_indicator_const MeasureTheory.lintegral_indicator_constₓ'. -/
theorem lintegral_indicator_const {s : Set α} (hs : MeasurableSet s) (c : ℝ≥0∞) :
    (∫⁻ a, s.indicator (fun _ => c) a ∂μ) = c * μ s := by
  rw [lintegral_indicator _ hs, set_lintegral_const]
#align measure_theory.lintegral_indicator_const MeasureTheory.lintegral_indicator_const

/- warning: measure_theory.set_lintegral_eq_const -> MeasureTheory.set_lintegral_eq_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (forall (r : ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (setOf.{u1} α (fun (x : α) => Eq.{1} ENNReal (f x) r))) (fun (x : α) => f x)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) r (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (setOf.{u1} α (fun (x : α) => Eq.{1} ENNReal (f x) r)))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (forall (r : ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (setOf.{u1} α (fun (x : α) => Eq.{1} ENNReal (f x) r))) (fun (x : α) => f x)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) r (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) (setOf.{u1} α (fun (x : α) => Eq.{1} ENNReal (f x) r)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.set_lintegral_eq_const MeasureTheory.set_lintegral_eq_constₓ'. -/
theorem set_lintegral_eq_const {f : α → ℝ≥0∞} (hf : Measurable f) (r : ℝ≥0∞) :
    (∫⁻ x in { x | f x = r }, f x ∂μ) = r * μ { x | f x = r } :=
  by
  have : ∀ᵐ x ∂μ, x ∈ { x | f x = r } → f x = r := ae_of_all μ fun _ hx => hx
  rw [set_lintegral_congr_fun _ this]
  dsimp
  rw [lintegral_const, measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  exact hf (measurable_set_singleton r)
#align measure_theory.set_lintegral_eq_const MeasureTheory.set_lintegral_eq_const

/- warning: measure_theory.lintegral_add_mul_meas_add_le_le_lintegral -> MeasureTheory.lintegral_add_mul_meas_add_le_le_lintegral is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal} {g : α -> ENNReal}, (Filter.EventuallyLE.{u1, 0} α ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.Measure.ae.{u1} α m μ) f g) -> (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m g μ) -> (forall (ε : ENNReal), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) ε (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (setOf.{u1} α (fun (x : α) => LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f x) ε) (g x)))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal} {g : α -> ENNReal}, (Filter.EventuallyLE.{u1, 0} α ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.Measure.ae.{u1} α m μ) f g) -> (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m g μ) -> (forall (ε : ENNReal), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) ε (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) (setOf.{u1} α (fun (x : α) => LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (f x) ε) (g x)))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a)))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_add_mul_meas_add_le_le_lintegral MeasureTheory.lintegral_add_mul_meas_add_le_le_lintegralₓ'. -/
/-- A version of **Markov's inequality** for two functions. It doesn't follow from the standard
Markov's inequality because we only assume measurability of `g`, not `f`. -/
theorem lintegral_add_mul_meas_add_le_le_lintegral {f g : α → ℝ≥0∞} (hle : f ≤ᵐ[μ] g)
    (hg : AEMeasurable g μ) (ε : ℝ≥0∞) :
    (∫⁻ a, f a ∂μ) + ε * μ { x | f x + ε ≤ g x } ≤ ∫⁻ a, g a ∂μ :=
  by
  rcases exists_measurable_le_lintegral_eq μ f with ⟨φ, hφm, hφ_le, hφ_eq⟩
  calc
    (∫⁻ x, f x ∂μ) + ε * μ { x | f x + ε ≤ g x } = (∫⁻ x, φ x ∂μ) + ε * μ { x | f x + ε ≤ g x } :=
      by rw [hφ_eq]
    _ ≤ (∫⁻ x, φ x ∂μ) + ε * μ { x | φ x + ε ≤ g x } :=
      (add_le_add_left
        (mul_le_mul_left' (measure_mono fun x => (add_le_add_right (hφ_le _) _).trans) _) _)
    _ = ∫⁻ x, φ x + indicator { x | φ x + ε ≤ g x } (fun _ => ε) x ∂μ :=
      by
      rw [lintegral_add_left hφm, lintegral_indicator₀, set_lintegral_const]
      exact measurableSet_le (hφm.null_measurable.measurable'.add_const _) hg.null_measurable
    _ ≤ ∫⁻ x, g x ∂μ := lintegral_mono_ae (hle.mono fun x hx₁ => _)
    
  simp only [indicator_apply]; split_ifs with hx₂
  exacts[hx₂, (add_zero _).trans_le <| (hφ_le x).trans hx₁]
#align measure_theory.lintegral_add_mul_meas_add_le_le_lintegral MeasureTheory.lintegral_add_mul_meas_add_le_le_lintegral

/- warning: measure_theory.mul_meas_ge_le_lintegral₀ -> MeasureTheory.mul_meas_ge_le_lintegral₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m f μ) -> (forall (ε : ENNReal), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) ε (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (setOf.{u1} α (fun (x : α) => LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (f x))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m f μ) -> (forall (ε : ENNReal), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) ε (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) (setOf.{u1} α (fun (x : α) => LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (f x))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)))
Case conversion may be inaccurate. Consider using '#align measure_theory.mul_meas_ge_le_lintegral₀ MeasureTheory.mul_meas_ge_le_lintegral₀ₓ'. -/
/-- **Markov's inequality** also known as **Chebyshev's first inequality**. -/
theorem mul_meas_ge_le_lintegral₀ {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (ε : ℝ≥0∞) :
    ε * μ { x | ε ≤ f x } ≤ ∫⁻ a, f a ∂μ := by
  simpa only [lintegral_zero, zero_add] using
    lintegral_add_mul_meas_add_le_le_lintegral (ae_of_all _ fun x => zero_le (f x)) hf ε
#align measure_theory.mul_meas_ge_le_lintegral₀ MeasureTheory.mul_meas_ge_le_lintegral₀

/- warning: measure_theory.mul_meas_ge_le_lintegral -> MeasureTheory.mul_meas_ge_le_lintegral is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (forall (ε : ENNReal), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) ε (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (setOf.{u1} α (fun (x : α) => LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (f x))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (forall (ε : ENNReal), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) ε (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) (setOf.{u1} α (fun (x : α) => LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (f x))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)))
Case conversion may be inaccurate. Consider using '#align measure_theory.mul_meas_ge_le_lintegral MeasureTheory.mul_meas_ge_le_lintegralₓ'. -/
/-- **Markov's inequality** also known as **Chebyshev's first inequality**. For a version assuming
`ae_measurable`, see `mul_meas_ge_le_lintegral₀`. -/
theorem mul_meas_ge_le_lintegral {f : α → ℝ≥0∞} (hf : Measurable f) (ε : ℝ≥0∞) :
    ε * μ { x | ε ≤ f x } ≤ ∫⁻ a, f a ∂μ :=
  mul_meas_ge_le_lintegral₀ hf.AEMeasurable ε
#align measure_theory.mul_meas_ge_le_lintegral MeasureTheory.mul_meas_ge_le_lintegral

/- warning: measure_theory.lintegral_eq_top_of_measure_eq_top_pos -> MeasureTheory.lintegral_eq_top_of_measure_eq_top_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m f μ) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (setOf.{u1} α (fun (x : α) => Eq.{1} ENNReal (f x) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))))) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m f μ) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) (setOf.{u1} α (fun (x : α) => Eq.{1} ENNReal (f x) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))))) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_eq_top_of_measure_eq_top_pos MeasureTheory.lintegral_eq_top_of_measure_eq_top_posₓ'. -/
theorem lintegral_eq_top_of_measure_eq_top_pos {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hμf : 0 < μ { x | f x = ∞ }) : (∫⁻ x, f x ∂μ) = ∞ :=
  eq_top_iff.mpr <|
    calc
      ∞ = ∞ * μ { x | ∞ ≤ f x } := by simp [mul_eq_top, hμf.ne.symm]
      _ ≤ ∫⁻ x, f x ∂μ := mul_meas_ge_le_lintegral₀ hf ∞
      
#align measure_theory.lintegral_eq_top_of_measure_eq_top_pos MeasureTheory.lintegral_eq_top_of_measure_eq_top_pos

/- warning: measure_theory.meas_ge_le_lintegral_div -> MeasureTheory.meas_ge_le_lintegral_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m f μ) -> (forall {ε : ENNReal}, (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Ne.{1} ENNReal ε (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (setOf.{u1} α (fun (x : α) => LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (f x)))) (HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toHasDiv.{0} ENNReal ENNReal.divInvMonoid)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) ε)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m f μ) -> (forall {ε : ENNReal}, (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Ne.{1} ENNReal ε (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) (setOf.{u1} α (fun (x : α) => LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (f x)))) (HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toDiv.{0} ENNReal ENNReal.instDivInvMonoidENNReal)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) ε)))
Case conversion may be inaccurate. Consider using '#align measure_theory.meas_ge_le_lintegral_div MeasureTheory.meas_ge_le_lintegral_divₓ'. -/
/-- **Markov's inequality** also known as **Chebyshev's first inequality**. -/
theorem meas_ge_le_lintegral_div {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) {ε : ℝ≥0∞} (hε : ε ≠ 0)
    (hε' : ε ≠ ∞) : μ { x | ε ≤ f x } ≤ (∫⁻ a, f a ∂μ) / ε :=
  (ENNReal.le_div_iff_mul_le (Or.inl hε) (Or.inl hε')).2 <|
    by
    rw [mul_comm]
    exact mul_meas_ge_le_lintegral₀ hf ε
#align measure_theory.meas_ge_le_lintegral_div MeasureTheory.meas_ge_le_lintegral_div

/- warning: measure_theory.ae_eq_of_ae_le_of_lintegral_le -> MeasureTheory.ae_eq_of_ae_le_of_lintegral_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal} {g : α -> ENNReal}, (Filter.EventuallyLE.{u1, 0} α ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.Measure.ae.{u1} α m μ) f g) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m g μ) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => g x)) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x))) -> (Filter.EventuallyEq.{u1, 0} α ENNReal (MeasureTheory.Measure.ae.{u1} α m μ) f g)
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal} {g : α -> ENNReal}, (Filter.EventuallyLE.{u1, 0} α ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.Measure.ae.{u1} α m μ) f g) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m g μ) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => g x)) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x))) -> (Filter.EventuallyEq.{u1, 0} α ENNReal (MeasureTheory.Measure.ae.{u1} α m μ) f g)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_of_ae_le_of_lintegral_le MeasureTheory.ae_eq_of_ae_le_of_lintegral_leₓ'. -/
theorem ae_eq_of_ae_le_of_lintegral_le {f g : α → ℝ≥0∞} (hfg : f ≤ᵐ[μ] g) (hf : (∫⁻ x, f x ∂μ) ≠ ∞)
    (hg : AEMeasurable g μ) (hgf : (∫⁻ x, g x ∂μ) ≤ ∫⁻ x, f x ∂μ) : f =ᵐ[μ] g :=
  by
  have : ∀ n : ℕ, ∀ᵐ x ∂μ, g x < f x + n⁻¹ := by
    intro n
    simp only [ae_iff, not_lt]
    have : (∫⁻ x, f x ∂μ) + (↑n)⁻¹ * μ { x : α | f x + n⁻¹ ≤ g x } ≤ ∫⁻ x, f x ∂μ :=
      (lintegral_add_mul_meas_add_le_le_lintegral hfg hg n⁻¹).trans hgf
    rw [(ENNReal.cancel_of_ne hf).add_le_iff_nonpos_right, nonpos_iff_eq_zero, mul_eq_zero] at this
    exact this.resolve_left (ENNReal.inv_ne_zero.2 (ENNReal.nat_ne_top _))
  refine' hfg.mp ((ae_all_iff.2 this).mono fun x hlt hle => hle.antisymm _)
  suffices : tendsto (fun n : ℕ => f x + n⁻¹) at_top (𝓝 (f x))
  exact ge_of_tendsto' this fun i => (hlt i).le
  simpa only [inv_top, add_zero] using
    tendsto_const_nhds.add (ENNReal.tendsto_inv_iff.2 ENNReal.tendsto_nat_nhds_top)
#align measure_theory.ae_eq_of_ae_le_of_lintegral_le MeasureTheory.ae_eq_of_ae_le_of_lintegral_le

/- warning: measure_theory.lintegral_eq_zero_iff' -> MeasureTheory.lintegral_eq_zero_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m f μ) -> (Iff (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Filter.EventuallyEq.{u1, 0} α ENNReal (MeasureTheory.Measure.ae.{u1} α m μ) f (OfNat.ofNat.{u1} (α -> ENNReal) 0 (OfNat.mk.{u1} (α -> ENNReal) 0 (Zero.zero.{u1} (α -> ENNReal) (Pi.instZero.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => ENNReal.hasZero)))))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m f μ) -> (Iff (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Filter.EventuallyEq.{u1, 0} α ENNReal (MeasureTheory.Measure.ae.{u1} α m μ) f (OfNat.ofNat.{u1} (α -> ENNReal) 0 (Zero.toOfNat0.{u1} (α -> ENNReal) (Pi.instZero.{u1, 0} α (fun (a._@.Mathlib.Order.Filter.Basic._hyg.19136 : α) => ENNReal) (fun (i : α) => instENNRealZero))))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_eq_zero_iff' MeasureTheory.lintegral_eq_zero_iff'ₓ'. -/
@[simp]
theorem lintegral_eq_zero_iff' {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    (∫⁻ a, f a ∂μ) = 0 ↔ f =ᵐ[μ] 0 :=
  have : (∫⁻ a : α, 0 ∂μ) ≠ ∞ := by simpa only [lintegral_zero] using zero_ne_top
  ⟨fun h =>
    (ae_eq_of_ae_le_of_lintegral_le (ae_of_all _ <| zero_le f) this hf
        (h.trans lintegral_zero.symm).le).symm,
    fun h => (lintegral_congr_ae h).trans lintegral_zero⟩
#align measure_theory.lintegral_eq_zero_iff' MeasureTheory.lintegral_eq_zero_iff'

/- warning: measure_theory.lintegral_eq_zero_iff -> MeasureTheory.lintegral_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (Iff (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Filter.EventuallyEq.{u1, 0} α ENNReal (MeasureTheory.Measure.ae.{u1} α m μ) f (OfNat.ofNat.{u1} (α -> ENNReal) 0 (OfNat.mk.{u1} (α -> ENNReal) 0 (Zero.zero.{u1} (α -> ENNReal) (Pi.instZero.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => ENNReal.hasZero)))))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (Iff (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Filter.EventuallyEq.{u1, 0} α ENNReal (MeasureTheory.Measure.ae.{u1} α m μ) f (OfNat.ofNat.{u1} (α -> ENNReal) 0 (Zero.toOfNat0.{u1} (α -> ENNReal) (Pi.instZero.{u1, 0} α (fun (a._@.Mathlib.Order.Filter.Basic._hyg.19136 : α) => ENNReal) (fun (i : α) => instENNRealZero))))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_eq_zero_iff MeasureTheory.lintegral_eq_zero_iffₓ'. -/
@[simp]
theorem lintegral_eq_zero_iff {f : α → ℝ≥0∞} (hf : Measurable f) : (∫⁻ a, f a ∂μ) = 0 ↔ f =ᵐ[μ] 0 :=
  lintegral_eq_zero_iff' hf.AEMeasurable
#align measure_theory.lintegral_eq_zero_iff MeasureTheory.lintegral_eq_zero_iff

/- warning: measure_theory.lintegral_pos_iff_support -> MeasureTheory.lintegral_pos_iff_support is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (Iff (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a))) (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (Function.support.{u1, 0} α ENNReal ENNReal.hasZero f))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (Iff (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a))) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) (Function.support.{u1, 0} α ENNReal instENNRealZero f))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_pos_iff_support MeasureTheory.lintegral_pos_iff_supportₓ'. -/
theorem lintegral_pos_iff_support {f : α → ℝ≥0∞} (hf : Measurable f) :
    (0 < ∫⁻ a, f a ∂μ) ↔ 0 < μ (Function.support f) := by
  simp [pos_iff_ne_zero, hf, Filter.EventuallyEq, ae_iff, Function.support]
#align measure_theory.lintegral_pos_iff_support MeasureTheory.lintegral_pos_iff_support

/- warning: measure_theory.lintegral_supr_ae -> MeasureTheory.lintegral_iSup_ae is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : Nat -> α -> ENNReal}, (forall (n : Nat), Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace (f n)) -> (forall (n : Nat), Filter.Eventually.{u1} α (fun (a : α) => LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (f n a) (f (Nat.succ n) a)) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => iSup.{0, 1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) Nat (fun (n : Nat) => f n a))) (iSup.{0, 1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) Nat (fun (n : Nat) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f n a))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : Nat -> α -> ENNReal}, (forall (n : Nat), Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace (f n)) -> (forall (n : Nat), Filter.Eventually.{u1} α (fun (a : α) => LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (f n a) (f (Nat.succ n) a)) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => iSup.{0, 1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) Nat (fun (n : Nat) => f n a))) (iSup.{0, 1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) Nat (fun (n : Nat) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f n a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_supr_ae MeasureTheory.lintegral_iSup_aeₓ'. -/
/-- Weaker version of the monotone convergence theorem-/
theorem lintegral_iSup_ae {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, Measurable (f n))
    (h_mono : ∀ n, ∀ᵐ a ∂μ, f n a ≤ f n.succ a) : (∫⁻ a, ⨆ n, f n a ∂μ) = ⨆ n, ∫⁻ a, f n a ∂μ :=
  let ⟨s, hs⟩ := exists_measurable_superset_of_null (ae_iff.1 (ae_all_iff.2 h_mono))
  let g n a := if a ∈ s then 0 else f n a
  have g_eq_f : ∀ᵐ a ∂μ, ∀ n, g n a = f n a :=
    (measure_zero_iff_ae_nmem.1 hs.2.2).mono fun a ha n => if_neg ha
  calc
    (∫⁻ a, ⨆ n, f n a ∂μ) = ∫⁻ a, ⨆ n, g n a ∂μ :=
      lintegral_congr_ae <| g_eq_f.mono fun a ha => by simp only [ha]
    _ = ⨆ n, ∫⁻ a, g n a ∂μ :=
      (lintegral_iSup (fun n => measurable_const.piecewise hs.2.1 (hf n))
        (monotone_nat_of_le_succ fun n a =>
          by_cases (fun h : a ∈ s => by simp [g, if_pos h]) fun h : a ∉ s =>
            by
            simp only [g, if_neg h]; have := hs.1; rw [subset_def] at this; have := mt (this a) h
            simp only [Classical.not_not, mem_set_of_eq] at this; exact this n))
    _ = ⨆ n, ∫⁻ a, f n a ∂μ := by simp only [lintegral_congr_ae (g_eq_f.mono fun a ha => ha _)]
    
#align measure_theory.lintegral_supr_ae MeasureTheory.lintegral_iSup_ae

/- warning: measure_theory.lintegral_sub' -> MeasureTheory.lintegral_sub' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal} {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m g μ) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Filter.EventuallyLE.{u1, 0} α ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.Measure.ae.{u1} α m μ) g f) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.hasSub) (f a) (g a))) (HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.hasSub) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal} {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m g μ) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Filter.EventuallyLE.{u1, 0} α ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.Measure.ae.{u1} α m μ) g f) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.instSub) (f a) (g a))) (HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.instSub) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_sub' MeasureTheory.lintegral_sub'ₓ'. -/
theorem lintegral_sub' {f g : α → ℝ≥0∞} (hg : AEMeasurable g μ) (hg_fin : (∫⁻ a, g a ∂μ) ≠ ∞)
    (h_le : g ≤ᵐ[μ] f) : (∫⁻ a, f a - g a ∂μ) = (∫⁻ a, f a ∂μ) - ∫⁻ a, g a ∂μ :=
  by
  refine' ENNReal.eq_sub_of_add_eq hg_fin _
  rw [← lintegral_add_right' _ hg]
  exact lintegral_congr_ae (h_le.mono fun x hx => tsub_add_cancel_of_le hx)
#align measure_theory.lintegral_sub' MeasureTheory.lintegral_sub'

/- warning: measure_theory.lintegral_sub -> MeasureTheory.lintegral_sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal} {g : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace g) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Filter.EventuallyLE.{u1, 0} α ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.Measure.ae.{u1} α m μ) g f) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.hasSub) (f a) (g a))) (HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.hasSub) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal} {g : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace g) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Filter.EventuallyLE.{u1, 0} α ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.Measure.ae.{u1} α m μ) g f) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.instSub) (f a) (g a))) (HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.instSub) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_sub MeasureTheory.lintegral_subₓ'. -/
theorem lintegral_sub {f g : α → ℝ≥0∞} (hg : Measurable g) (hg_fin : (∫⁻ a, g a ∂μ) ≠ ∞)
    (h_le : g ≤ᵐ[μ] f) : (∫⁻ a, f a - g a ∂μ) = (∫⁻ a, f a ∂μ) - ∫⁻ a, g a ∂μ :=
  lintegral_sub' hg.AEMeasurable hg_fin h_le
#align measure_theory.lintegral_sub MeasureTheory.lintegral_sub

/- warning: measure_theory.lintegral_sub_le' -> MeasureTheory.lintegral_sub_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : α -> ENNReal) (g : α -> ENNReal), (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m f μ) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.hasSub) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => g x)) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x))) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.hasSub) (g x) (f x))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : α -> ENNReal) (g : α -> ENNReal), (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m f μ) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.instSub) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => g x)) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x))) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.instSub) (g x) (f x))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_sub_le' MeasureTheory.lintegral_sub_le'ₓ'. -/
theorem lintegral_sub_le' (f g : α → ℝ≥0∞) (hf : AEMeasurable f μ) :
    ((∫⁻ x, g x ∂μ) - ∫⁻ x, f x ∂μ) ≤ ∫⁻ x, g x - f x ∂μ :=
  by
  rw [tsub_le_iff_right]
  by_cases hfi : (∫⁻ x, f x ∂μ) = ∞
  · rw [hfi, add_top]
    exact le_top
  · rw [← lintegral_add_right' _ hf]
    exact lintegral_mono fun x => le_tsub_add
#align measure_theory.lintegral_sub_le' MeasureTheory.lintegral_sub_le'

/- warning: measure_theory.lintegral_sub_le -> MeasureTheory.lintegral_sub_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : α -> ENNReal) (g : α -> ENNReal), (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.hasSub) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => g x)) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x))) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.hasSub) (g x) (f x))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : α -> ENNReal) (g : α -> ENNReal), (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.instSub) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => g x)) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x))) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.instSub) (g x) (f x))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_sub_le MeasureTheory.lintegral_sub_leₓ'. -/
theorem lintegral_sub_le (f g : α → ℝ≥0∞) (hf : Measurable f) :
    ((∫⁻ x, g x ∂μ) - ∫⁻ x, f x ∂μ) ≤ ∫⁻ x, g x - f x ∂μ :=
  lintegral_sub_le' f g hf.AEMeasurable
#align measure_theory.lintegral_sub_le MeasureTheory.lintegral_sub_le

/- warning: measure_theory.lintegral_strict_mono_of_ae_le_of_frequently_ae_lt -> MeasureTheory.lintegral_strict_mono_of_ae_le_of_frequently_ae_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal} {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m g μ) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Filter.EventuallyLE.{u1, 0} α ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.Measure.ae.{u1} α m μ) f g) -> (Filter.Frequently.{u1} α (fun (x : α) => Ne.{1} ENNReal (f x) (g x)) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => g x)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal} {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m g μ) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Filter.EventuallyLE.{u1, 0} α ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.Measure.ae.{u1} α m μ) f g) -> (Filter.Frequently.{u1} α (fun (x : α) => Ne.{1} ENNReal (f x) (g x)) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => g x)))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_strict_mono_of_ae_le_of_frequently_ae_lt MeasureTheory.lintegral_strict_mono_of_ae_le_of_frequently_ae_ltₓ'. -/
theorem lintegral_strict_mono_of_ae_le_of_frequently_ae_lt {f g : α → ℝ≥0∞} (hg : AEMeasurable g μ)
    (hfi : (∫⁻ x, f x ∂μ) ≠ ∞) (h_le : f ≤ᵐ[μ] g) (h : ∃ᵐ x ∂μ, f x ≠ g x) :
    (∫⁻ x, f x ∂μ) < ∫⁻ x, g x ∂μ := by
  contrapose! h
  simp only [not_frequently, Ne.def, Classical.not_not]
  exact ae_eq_of_ae_le_of_lintegral_le h_le hfi hg h
#align measure_theory.lintegral_strict_mono_of_ae_le_of_frequently_ae_lt MeasureTheory.lintegral_strict_mono_of_ae_le_of_frequently_ae_lt

/- warning: measure_theory.lintegral_strict_mono_of_ae_le_of_ae_lt_on -> MeasureTheory.lintegral_strict_mono_of_ae_le_of_ae_lt_on is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal} {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m g μ) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Filter.EventuallyLE.{u1, 0} α ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.Measure.ae.{u1} α m μ) f g) -> (forall {s : Set.{u1} α}, (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Filter.Eventually.{u1} α (fun (x : α) => (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (f x) (g x))) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => g x))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal} {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m g μ) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Filter.EventuallyLE.{u1, 0} α ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.Measure.ae.{u1} α m μ) f g) -> (forall {s : Set.{u1} α}, (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Filter.Eventually.{u1} α (fun (x : α) => (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (f x) (g x))) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => g x))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_strict_mono_of_ae_le_of_ae_lt_on MeasureTheory.lintegral_strict_mono_of_ae_le_of_ae_lt_onₓ'. -/
theorem lintegral_strict_mono_of_ae_le_of_ae_lt_on {f g : α → ℝ≥0∞} (hg : AEMeasurable g μ)
    (hfi : (∫⁻ x, f x ∂μ) ≠ ∞) (h_le : f ≤ᵐ[μ] g) {s : Set α} (hμs : μ s ≠ 0)
    (h : ∀ᵐ x ∂μ, x ∈ s → f x < g x) : (∫⁻ x, f x ∂μ) < ∫⁻ x, g x ∂μ :=
  lintegral_strict_mono_of_ae_le_of_frequently_ae_lt hg hfi h_le <|
    ((frequently_ae_mem_iff.2 hμs).and_eventually h).mono fun x hx => (hx.2 hx.1).Ne
#align measure_theory.lintegral_strict_mono_of_ae_le_of_ae_lt_on MeasureTheory.lintegral_strict_mono_of_ae_le_of_ae_lt_on

/- warning: measure_theory.lintegral_strict_mono -> MeasureTheory.lintegral_strict_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal} {g : α -> ENNReal}, (Ne.{succ u1} (MeasureTheory.Measure.{u1} α m) μ (OfNat.ofNat.{u1} (MeasureTheory.Measure.{u1} α m) 0 (OfNat.mk.{u1} (MeasureTheory.Measure.{u1} α m) 0 (Zero.zero.{u1} (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.instZero.{u1} α m))))) -> (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m g μ) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Filter.Eventually.{u1} α (fun (x : α) => LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (f x) (g x)) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => g x)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal} {g : α -> ENNReal}, (Ne.{succ u1} (MeasureTheory.Measure.{u1} α m) μ (OfNat.ofNat.{u1} (MeasureTheory.Measure.{u1} α m) 0 (Zero.toOfNat0.{u1} (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.instZero.{u1} α m)))) -> (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m g μ) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Filter.Eventually.{u1} α (fun (x : α) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (f x) (g x)) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => g x)))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_strict_mono MeasureTheory.lintegral_strict_monoₓ'. -/
theorem lintegral_strict_mono {f g : α → ℝ≥0∞} (hμ : μ ≠ 0) (hg : AEMeasurable g μ)
    (hfi : (∫⁻ x, f x ∂μ) ≠ ∞) (h : ∀ᵐ x ∂μ, f x < g x) : (∫⁻ x, f x ∂μ) < ∫⁻ x, g x ∂μ :=
  by
  rw [Ne.def, ← measure.measure_univ_eq_zero] at hμ
  refine' lintegral_strict_mono_of_ae_le_of_ae_lt_on hg hfi (ae_le_of_ae_lt h) hμ _
  simpa using h
#align measure_theory.lintegral_strict_mono MeasureTheory.lintegral_strict_mono

/- warning: measure_theory.set_lintegral_strict_mono -> MeasureTheory.set_lintegral_strict_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal} {g : α -> ENNReal} {s : Set.{u1} α}, (MeasurableSet.{u1} α m s) -> (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace g) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Filter.Eventually.{u1} α (fun (x : α) => (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (f x) (g x))) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => f x)) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => g x)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal} {g : α -> ENNReal} {s : Set.{u1} α}, (MeasurableSet.{u1} α m s) -> (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace g) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Filter.Eventually.{u1} α (fun (x : α) => (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (f x) (g x))) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => f x)) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => g x)))
Case conversion may be inaccurate. Consider using '#align measure_theory.set_lintegral_strict_mono MeasureTheory.set_lintegral_strict_monoₓ'. -/
theorem set_lintegral_strict_mono {f g : α → ℝ≥0∞} {s : Set α} (hsm : MeasurableSet s)
    (hs : μ s ≠ 0) (hg : Measurable g) (hfi : (∫⁻ x in s, f x ∂μ) ≠ ∞)
    (h : ∀ᵐ x ∂μ, x ∈ s → f x < g x) : (∫⁻ x in s, f x ∂μ) < ∫⁻ x in s, g x ∂μ :=
  lintegral_strict_mono (by simp [hs]) hg.AEMeasurable hfi ((ae_restrict_iff' hsm).mpr h)
#align measure_theory.set_lintegral_strict_mono MeasureTheory.set_lintegral_strict_mono

/- warning: measure_theory.lintegral_infi_ae -> MeasureTheory.lintegral_iInf_ae is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : Nat -> α -> ENNReal}, (forall (n : Nat), Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace (f n)) -> (forall (n : Nat), Filter.EventuallyLE.{u1, 0} α ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.Measure.ae.{u1} α m μ) (f (Nat.succ n)) (f n)) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) a)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => iInf.{0, 1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) Nat (fun (n : Nat) => f n a))) (iInf.{0, 1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) Nat (fun (n : Nat) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f n a))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : Nat -> α -> ENNReal}, (forall (n : Nat), Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace (f n)) -> (forall (n : Nat), Filter.EventuallyLE.{u1, 0} α ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.Measure.ae.{u1} α m μ) (f (Nat.succ n)) (f n)) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) a)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => iInf.{0, 1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) Nat (fun (n : Nat) => f n a))) (iInf.{0, 1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) Nat (fun (n : Nat) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f n a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_infi_ae MeasureTheory.lintegral_iInf_aeₓ'. -/
/-- Monotone convergence theorem for nonincreasing sequences of functions -/
theorem lintegral_iInf_ae {f : ℕ → α → ℝ≥0∞} (h_meas : ∀ n, Measurable (f n))
    (h_mono : ∀ n : ℕ, f n.succ ≤ᵐ[μ] f n) (h_fin : (∫⁻ a, f 0 a ∂μ) ≠ ∞) :
    (∫⁻ a, ⨅ n, f n a ∂μ) = ⨅ n, ∫⁻ a, f n a ∂μ :=
  have fn_le_f0 : (∫⁻ a, ⨅ n, f n a ∂μ) ≤ ∫⁻ a, f 0 a ∂μ :=
    lintegral_mono fun a => iInf_le_of_le 0 le_rfl
  have fn_le_f0' : (⨅ n, ∫⁻ a, f n a ∂μ) ≤ ∫⁻ a, f 0 a ∂μ := iInf_le_of_le 0 le_rfl
  (ENNReal.sub_right_inj h_fin fn_le_f0 fn_le_f0').1 <|
    show ((∫⁻ a, f 0 a ∂μ) - ∫⁻ a, ⨅ n, f n a ∂μ) = (∫⁻ a, f 0 a ∂μ) - ⨅ n, ∫⁻ a, f n a ∂μ from
      calc
        ((∫⁻ a, f 0 a ∂μ) - ∫⁻ a, ⨅ n, f n a ∂μ) = ∫⁻ a, f 0 a - ⨅ n, f n a ∂μ :=
          (lintegral_sub (measurable_iInf h_meas)
              (ne_top_of_le_ne_top h_fin <| lintegral_mono fun a => iInf_le _ _)
              (ae_of_all _ fun a => iInf_le _ _)).symm
        _ = ∫⁻ a, ⨆ n, f 0 a - f n a ∂μ := (congr rfl (funext fun a => ENNReal.sub_iInf))
        _ = ⨆ n, ∫⁻ a, f 0 a - f n a ∂μ :=
          (lintegral_iSup_ae (fun n => (h_meas 0).sub (h_meas n)) fun n =>
            (h_mono n).mono fun a ha => tsub_le_tsub le_rfl ha)
        _ = ⨆ n, (∫⁻ a, f 0 a ∂μ) - ∫⁻ a, f n a ∂μ :=
          (have h_mono : ∀ᵐ a ∂μ, ∀ n : ℕ, f n.succ a ≤ f n a := ae_all_iff.2 h_mono
          have h_mono : ∀ n, ∀ᵐ a ∂μ, f n a ≤ f 0 a := fun n =>
            h_mono.mono fun a h => by
              induction' n with n ih
              · exact le_rfl; · exact le_trans (h n) ih
          congr_arg iSup <|
            funext fun n =>
              lintegral_sub (h_meas _) (ne_top_of_le_ne_top h_fin <| lintegral_mono_ae <| h_mono n)
                (h_mono n))
        _ = (∫⁻ a, f 0 a ∂μ) - ⨅ n, ∫⁻ a, f n a ∂μ := ENNReal.sub_iInf.symm
        
#align measure_theory.lintegral_infi_ae MeasureTheory.lintegral_iInf_ae

/- warning: measure_theory.lintegral_infi -> MeasureTheory.lintegral_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : Nat -> α -> ENNReal}, (forall (n : Nat), Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace (f n)) -> (Antitone.{0, u1} Nat (α -> ENNReal) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (Pi.preorder.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) f) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) a)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => iInf.{0, 1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) Nat (fun (n : Nat) => f n a))) (iInf.{0, 1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) Nat (fun (n : Nat) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f n a))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : Nat -> α -> ENNReal}, (forall (n : Nat), Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace (f n)) -> (Antitone.{0, u1} Nat (α -> ENNReal) (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (Pi.preorder.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) f) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) a)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => iInf.{0, 1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) Nat (fun (n : Nat) => f n a))) (iInf.{0, 1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) Nat (fun (n : Nat) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f n a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_infi MeasureTheory.lintegral_iInfₓ'. -/
/-- Monotone convergence theorem for nonincreasing sequences of functions -/
theorem lintegral_iInf {f : ℕ → α → ℝ≥0∞} (h_meas : ∀ n, Measurable (f n)) (h_anti : Antitone f)
    (h_fin : (∫⁻ a, f 0 a ∂μ) ≠ ∞) : (∫⁻ a, ⨅ n, f n a ∂μ) = ⨅ n, ∫⁻ a, f n a ∂μ :=
  lintegral_iInf_ae h_meas (fun n => ae_of_all _ <| h_anti n.le_succ) h_fin
#align measure_theory.lintegral_infi MeasureTheory.lintegral_iInf

/- warning: measure_theory.lintegral_liminf_le' -> MeasureTheory.lintegral_liminf_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : Nat -> α -> ENNReal}, (forall (n : Nat), AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m (f n) μ) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => Filter.liminf.{0, 0} ENNReal Nat (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)) (fun (n : Nat) => f n a) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))))) (Filter.liminf.{0, 0} ENNReal Nat (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)) (fun (n : Nat) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f n a)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : Nat -> α -> ENNReal}, (forall (n : Nat), AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m (f n) μ) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => Filter.liminf.{0, 0} ENNReal Nat (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) (fun (n : Nat) => f n a) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))))) (Filter.liminf.{0, 0} ENNReal Nat (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) (fun (n : Nat) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f n a)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_liminf_le' MeasureTheory.lintegral_liminf_le'ₓ'. -/
/-- Known as Fatou's lemma, version with `ae_measurable` functions -/
theorem lintegral_liminf_le' {f : ℕ → α → ℝ≥0∞} (h_meas : ∀ n, AEMeasurable (f n) μ) :
    (∫⁻ a, liminf (fun n => f n a) atTop ∂μ) ≤ liminf (fun n => ∫⁻ a, f n a ∂μ) atTop :=
  calc
    (∫⁻ a, liminf (fun n => f n a) atTop ∂μ) = ∫⁻ a, ⨆ n : ℕ, ⨅ i ≥ n, f i a ∂μ := by
      simp only [liminf_eq_supr_infi_of_nat]
    _ = ⨆ n : ℕ, ∫⁻ a, ⨅ i ≥ n, f i a ∂μ :=
      (lintegral_iSup' (fun n => aemeasurable_biInf _ (to_countable _) h_meas)
        (ae_of_all μ fun a n m hnm => iInf_le_iInf_of_subset fun i hi => le_trans hnm hi))
    _ ≤ ⨆ n : ℕ, ⨅ i ≥ n, ∫⁻ a, f i a ∂μ := (iSup_mono fun n => le_iInf₂_lintegral _)
    _ = atTop.liminf fun n => ∫⁻ a, f n a ∂μ := Filter.liminf_eq_iSup_iInf_of_nat.symm
    
#align measure_theory.lintegral_liminf_le' MeasureTheory.lintegral_liminf_le'

/- warning: measure_theory.lintegral_liminf_le -> MeasureTheory.lintegral_liminf_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : Nat -> α -> ENNReal}, (forall (n : Nat), Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace (f n)) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => Filter.liminf.{0, 0} ENNReal Nat (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)) (fun (n : Nat) => f n a) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))))) (Filter.liminf.{0, 0} ENNReal Nat (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)) (fun (n : Nat) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f n a)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : Nat -> α -> ENNReal}, (forall (n : Nat), Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace (f n)) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => Filter.liminf.{0, 0} ENNReal Nat (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) (fun (n : Nat) => f n a) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))))) (Filter.liminf.{0, 0} ENNReal Nat (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) (fun (n : Nat) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f n a)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_liminf_le MeasureTheory.lintegral_liminf_leₓ'. -/
/-- Known as Fatou's lemma -/
theorem lintegral_liminf_le {f : ℕ → α → ℝ≥0∞} (h_meas : ∀ n, Measurable (f n)) :
    (∫⁻ a, liminf (fun n => f n a) atTop ∂μ) ≤ liminf (fun n => ∫⁻ a, f n a ∂μ) atTop :=
  lintegral_liminf_le' fun n => (h_meas n).AEMeasurable
#align measure_theory.lintegral_liminf_le MeasureTheory.lintegral_liminf_le

/- warning: measure_theory.limsup_lintegral_le -> MeasureTheory.limsup_lintegral_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : Nat -> α -> ENNReal} {g : α -> ENNReal}, (forall (n : Nat), Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace (f n)) -> (forall (n : Nat), Filter.EventuallyLE.{u1, 0} α ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.Measure.ae.{u1} α m μ) (f n) g) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (Filter.limsup.{0, 0} ENNReal Nat (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)) (fun (n : Nat) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f n a)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => Filter.limsup.{0, 0} ENNReal Nat (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)) (fun (n : Nat) => f n a) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : Nat -> α -> ENNReal} {g : α -> ENNReal}, (forall (n : Nat), Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace (f n)) -> (forall (n : Nat), Filter.EventuallyLE.{u1, 0} α ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.Measure.ae.{u1} α m μ) (f n) g) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => g a)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (Filter.limsup.{0, 0} ENNReal Nat (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) (fun (n : Nat) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f n a)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => Filter.limsup.{0, 0} ENNReal Nat (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) (fun (n : Nat) => f n a) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))))))
Case conversion may be inaccurate. Consider using '#align measure_theory.limsup_lintegral_le MeasureTheory.limsup_lintegral_leₓ'. -/
theorem limsup_lintegral_le {f : ℕ → α → ℝ≥0∞} {g : α → ℝ≥0∞} (hf_meas : ∀ n, Measurable (f n))
    (h_bound : ∀ n, f n ≤ᵐ[μ] g) (h_fin : (∫⁻ a, g a ∂μ) ≠ ∞) :
    limsup (fun n => ∫⁻ a, f n a ∂μ) atTop ≤ ∫⁻ a, limsup (fun n => f n a) atTop ∂μ :=
  calc
    limsup (fun n => ∫⁻ a, f n a ∂μ) atTop = ⨅ n : ℕ, ⨆ i ≥ n, ∫⁻ a, f i a ∂μ :=
      limsup_eq_iInf_iSup_of_nat
    _ ≤ ⨅ n : ℕ, ∫⁻ a, ⨆ i ≥ n, f i a ∂μ := (iInf_mono fun n => iSup₂_lintegral_le _)
    _ = ∫⁻ a, ⨅ n : ℕ, ⨆ i ≥ n, f i a ∂μ :=
      by
      refine' (lintegral_infi _ _ _).symm
      · intro n
        exact measurable_biSup _ (to_countable _) hf_meas
      · intro n m hnm a
        exact iSup_le_iSup_of_subset fun i hi => le_trans hnm hi
      · refine' ne_top_of_le_ne_top h_fin (lintegral_mono_ae _)
        refine' (ae_all_iff.2 h_bound).mono fun n hn => _
        exact iSup_le fun i => iSup_le fun hi => hn i
    _ = ∫⁻ a, limsup (fun n => f n a) atTop ∂μ := by simp only [limsup_eq_infi_supr_of_nat]
    
#align measure_theory.limsup_lintegral_le MeasureTheory.limsup_lintegral_le

/- warning: measure_theory.tendsto_lintegral_of_dominated_convergence -> MeasureTheory.tendsto_lintegral_of_dominated_convergence is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {F : Nat -> α -> ENNReal} {f : α -> ENNReal} (bound : α -> ENNReal), (forall (n : Nat), Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace (F n)) -> (forall (n : Nat), Filter.EventuallyLE.{u1, 0} α ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.Measure.ae.{u1} α m μ) (F n) bound) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => bound a)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Filter.Eventually.{u1} α (fun (a : α) => Filter.Tendsto.{0, 0} Nat ENNReal (fun (n : Nat) => F n a) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} ENNReal ENNReal.topologicalSpace (f a))) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (Filter.Tendsto.{0, 0} Nat ENNReal (fun (n : Nat) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => F n a)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} ENNReal ENNReal.topologicalSpace (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {F : Nat -> α -> ENNReal} {f : α -> ENNReal} (bound : α -> ENNReal), (forall (n : Nat), Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace (F n)) -> (forall (n : Nat), Filter.EventuallyLE.{u1, 0} α ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.Measure.ae.{u1} α m μ) (F n) bound) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => bound a)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Filter.Eventually.{u1} α (fun (a : α) => Filter.Tendsto.{0, 0} Nat ENNReal (fun (n : Nat) => F n a) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (f a))) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (Filter.Tendsto.{0, 0} Nat ENNReal (fun (n : Nat) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => F n a)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.tendsto_lintegral_of_dominated_convergence MeasureTheory.tendsto_lintegral_of_dominated_convergenceₓ'. -/
/-- Dominated convergence theorem for nonnegative functions -/
theorem tendsto_lintegral_of_dominated_convergence {F : ℕ → α → ℝ≥0∞} {f : α → ℝ≥0∞}
    (bound : α → ℝ≥0∞) (hF_meas : ∀ n, Measurable (F n)) (h_bound : ∀ n, F n ≤ᵐ[μ] bound)
    (h_fin : (∫⁻ a, bound a ∂μ) ≠ ∞) (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => ∫⁻ a, F n a ∂μ) atTop (𝓝 (∫⁻ a, f a ∂μ)) :=
  tendsto_of_le_liminf_of_limsup_le
    (calc
      (∫⁻ a, f a ∂μ) = ∫⁻ a, liminf (fun n : ℕ => F n a) atTop ∂μ :=
        lintegral_congr_ae <| h_lim.mono fun a h => h.liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ a, F n a ∂μ) atTop := lintegral_liminf_le hF_meas
      )
    (calc
      limsup (fun n : ℕ => ∫⁻ a, F n a ∂μ) atTop ≤ ∫⁻ a, limsup (fun n => F n a) atTop ∂μ :=
        limsup_lintegral_le hF_meas h_bound h_fin
      _ = ∫⁻ a, f a ∂μ := lintegral_congr_ae <| h_lim.mono fun a h => h.limsup_eq
      )
#align measure_theory.tendsto_lintegral_of_dominated_convergence MeasureTheory.tendsto_lintegral_of_dominated_convergence

/- warning: measure_theory.tendsto_lintegral_of_dominated_convergence' -> MeasureTheory.tendsto_lintegral_of_dominated_convergence' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {F : Nat -> α -> ENNReal} {f : α -> ENNReal} (bound : α -> ENNReal), (forall (n : Nat), AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m (F n) μ) -> (forall (n : Nat), Filter.EventuallyLE.{u1, 0} α ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.Measure.ae.{u1} α m μ) (F n) bound) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => bound a)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Filter.Eventually.{u1} α (fun (a : α) => Filter.Tendsto.{0, 0} Nat ENNReal (fun (n : Nat) => F n a) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} ENNReal ENNReal.topologicalSpace (f a))) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (Filter.Tendsto.{0, 0} Nat ENNReal (fun (n : Nat) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => F n a)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} ENNReal ENNReal.topologicalSpace (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {F : Nat -> α -> ENNReal} {f : α -> ENNReal} (bound : α -> ENNReal), (forall (n : Nat), AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m (F n) μ) -> (forall (n : Nat), Filter.EventuallyLE.{u1, 0} α ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.Measure.ae.{u1} α m μ) (F n) bound) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => bound a)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Filter.Eventually.{u1} α (fun (a : α) => Filter.Tendsto.{0, 0} Nat ENNReal (fun (n : Nat) => F n a) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (f a))) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (Filter.Tendsto.{0, 0} Nat ENNReal (fun (n : Nat) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => F n a)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.tendsto_lintegral_of_dominated_convergence' MeasureTheory.tendsto_lintegral_of_dominated_convergence'ₓ'. -/
/-- Dominated convergence theorem for nonnegative functions which are just almost everywhere
measurable. -/
theorem tendsto_lintegral_of_dominated_convergence' {F : ℕ → α → ℝ≥0∞} {f : α → ℝ≥0∞}
    (bound : α → ℝ≥0∞) (hF_meas : ∀ n, AEMeasurable (F n) μ) (h_bound : ∀ n, F n ≤ᵐ[μ] bound)
    (h_fin : (∫⁻ a, bound a ∂μ) ≠ ∞) (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => ∫⁻ a, F n a ∂μ) atTop (𝓝 (∫⁻ a, f a ∂μ)) :=
  by
  have : ∀ n, (∫⁻ a, F n a ∂μ) = ∫⁻ a, (hF_meas n).mk (F n) a ∂μ := fun n =>
    lintegral_congr_ae (hF_meas n).ae_eq_mk
  simp_rw [this]
  apply
    tendsto_lintegral_of_dominated_convergence bound (fun n => (hF_meas n).measurable_mk) _ h_fin
  · have : ∀ n, ∀ᵐ a ∂μ, (hF_meas n).mk (F n) a = F n a := fun n => (hF_meas n).ae_eq_mk.symm
    have : ∀ᵐ a ∂μ, ∀ n, (hF_meas n).mk (F n) a = F n a := ae_all_iff.mpr this
    filter_upwards [this, h_lim]with a H H'
    simp_rw [H]
    exact H'
  · intro n
    filter_upwards [h_bound n, (hF_meas n).ae_eq_mk]with a H H'
    rwa [H'] at H
#align measure_theory.tendsto_lintegral_of_dominated_convergence' MeasureTheory.tendsto_lintegral_of_dominated_convergence'

/- warning: measure_theory.tendsto_lintegral_filter_of_dominated_convergence -> MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {ι : Type.{u2}} {l : Filter.{u2} ι} [_inst_1 : Filter.IsCountablyGenerated.{u2} ι l] {F : ι -> α -> ENNReal} {f : α -> ENNReal} (bound : α -> ENNReal), (Filter.Eventually.{u2} ι (fun (n : ι) => Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace (F n)) l) -> (Filter.Eventually.{u2} ι (fun (n : ι) => Filter.Eventually.{u1} α (fun (a : α) => LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (F n a) (bound a)) (MeasureTheory.Measure.ae.{u1} α m μ)) l) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => bound a)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Filter.Eventually.{u1} α (fun (a : α) => Filter.Tendsto.{u2, 0} ι ENNReal (fun (n : ι) => F n a) l (nhds.{0} ENNReal ENNReal.topologicalSpace (f a))) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (Filter.Tendsto.{u2, 0} ι ENNReal (fun (n : ι) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => F n a)) l (nhds.{0} ENNReal ENNReal.topologicalSpace (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {ι : Type.{u2}} {l : Filter.{u2} ι} [_inst_1 : Filter.IsCountablyGenerated.{u2} ι l] {F : ι -> α -> ENNReal} {f : α -> ENNReal} (bound : α -> ENNReal), (Filter.Eventually.{u2} ι (fun (n : ι) => Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace (F n)) l) -> (Filter.Eventually.{u2} ι (fun (n : ι) => Filter.Eventually.{u1} α (fun (a : α) => LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (F n a) (bound a)) (MeasureTheory.Measure.ae.{u1} α m μ)) l) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => bound a)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Filter.Eventually.{u1} α (fun (a : α) => Filter.Tendsto.{u2, 0} ι ENNReal (fun (n : ι) => F n a) l (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (f a))) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (Filter.Tendsto.{u2, 0} ι ENNReal (fun (n : ι) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => F n a)) l (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.tendsto_lintegral_filter_of_dominated_convergence MeasureTheory.tendsto_lintegral_filter_of_dominated_convergenceₓ'. -/
/-- Dominated convergence theorem for filters with a countable basis -/
theorem tendsto_lintegral_filter_of_dominated_convergence {ι} {l : Filter ι}
    [l.IsCountablyGenerated] {F : ι → α → ℝ≥0∞} {f : α → ℝ≥0∞} (bound : α → ℝ≥0∞)
    (hF_meas : ∀ᶠ n in l, Measurable (F n)) (h_bound : ∀ᶠ n in l, ∀ᵐ a ∂μ, F n a ≤ bound a)
    (h_fin : (∫⁻ a, bound a ∂μ) ≠ ∞) (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) l (𝓝 (f a))) :
    Tendsto (fun n => ∫⁻ a, F n a ∂μ) l (𝓝 <| ∫⁻ a, f a ∂μ) :=
  by
  rw [tendsto_iff_seq_tendsto]
  intro x xl
  have hxl := by
    rw [tendsto_at_top'] at xl
    exact xl
  have h := inter_mem hF_meas h_bound
  replace h := hxl _ h
  rcases h with ⟨k, h⟩
  rw [← tendsto_add_at_top_iff_nat k]
  refine' tendsto_lintegral_of_dominated_convergence _ _ _ _ _
  · exact bound
  · intro
    refine' (h _ _).1
    exact Nat.le_add_left _ _
  · intro
    refine' (h _ _).2
    exact Nat.le_add_left _ _
  · assumption
  · refine' h_lim.mono fun a h_lim => _
    apply @tendsto.comp _ _ _ (fun n => x (n + k)) fun n => F n a
    · assumption
    rw [tendsto_add_at_top_iff_nat]
    assumption
#align measure_theory.tendsto_lintegral_filter_of_dominated_convergence MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence

section

open Encodable

/- warning: measure_theory.lintegral_supr_directed_of_measurable -> MeasureTheory.lintegral_iSup_directed_of_measurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : Countable.{succ u2} β] {f : β -> α -> ENNReal}, (forall (b : β), Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace (f b)) -> (Directed.{u1, succ u2} (α -> ENNReal) β (LE.le.{u1} (α -> ENNReal) (Pi.hasLe.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))))) f) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => iSup.{0, succ u2} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) β (fun (b : β) => f b a))) (iSup.{0, succ u2} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) β (fun (b : β) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f b a))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : Countable.{succ u2} β] {f : β -> α -> ENNReal}, (forall (b : β), Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace (f b)) -> (Directed.{u1, succ u2} (α -> ENNReal) β (fun (x._@.Mathlib.MeasureTheory.Integral.Lebesgue._hyg.25151 : α -> ENNReal) (x._@.Mathlib.MeasureTheory.Integral.Lebesgue._hyg.25153 : α -> ENNReal) => LE.le.{u1} (α -> ENNReal) (Pi.hasLe.{u1, 0} α (fun (a._@.Mathlib.MeasureTheory.Integral.Lebesgue._hyg.25134 : α) => ENNReal) (fun (i : α) => Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))) x._@.Mathlib.MeasureTheory.Integral.Lebesgue._hyg.25151 x._@.Mathlib.MeasureTheory.Integral.Lebesgue._hyg.25153) f) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => iSup.{0, succ u2} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) β (fun (b : β) => f b a))) (iSup.{0, succ u2} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) β (fun (b : β) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f b a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_supr_directed_of_measurable MeasureTheory.lintegral_iSup_directed_of_measurableₓ'. -/
/-- Monotone convergence for a supremum over a directed family and indexed by a countable type -/
theorem lintegral_iSup_directed_of_measurable [Countable β] {f : β → α → ℝ≥0∞}
    (hf : ∀ b, Measurable (f b)) (h_directed : Directed (· ≤ ·) f) :
    (∫⁻ a, ⨆ b, f b a ∂μ) = ⨆ b, ∫⁻ a, f b a ∂μ :=
  by
  cases nonempty_encodable β
  cases isEmpty_or_nonempty β
  · simp [iSup_of_empty]
  inhabit β
  have : ∀ a, (⨆ b, f b a) = ⨆ n, f (h_directed.sequence f n) a :=
    by
    intro a
    refine' le_antisymm (iSup_le fun b => _) (iSup_le fun n => le_iSup (fun n => f n a) _)
    exact le_iSup_of_le (encode b + 1) (h_directed.le_sequence b a)
  calc
    (∫⁻ a, ⨆ b, f b a ∂μ) = ∫⁻ a, ⨆ n, f (h_directed.sequence f n) a ∂μ := by simp only [this]
    _ = ⨆ n, ∫⁻ a, f (h_directed.sequence f n) a ∂μ :=
      (lintegral_supr (fun n => hf _) h_directed.sequence_mono)
    _ = ⨆ b, ∫⁻ a, f b a ∂μ :=
      by
      refine' le_antisymm (iSup_le fun n => _) (iSup_le fun b => _)
      · exact le_iSup (fun b => ∫⁻ a, f b a ∂μ) _
      · exact le_iSup_of_le (encode b + 1) (lintegral_mono <| h_directed.le_sequence b)
    
#align measure_theory.lintegral_supr_directed_of_measurable MeasureTheory.lintegral_iSup_directed_of_measurable

/- warning: measure_theory.lintegral_supr_directed -> MeasureTheory.lintegral_iSup_directed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : Countable.{succ u2} β] {f : β -> α -> ENNReal}, (forall (b : β), AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m (f b) μ) -> (Directed.{u1, succ u2} (α -> ENNReal) β (LE.le.{u1} (α -> ENNReal) (Pi.hasLe.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))))) f) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => iSup.{0, succ u2} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) β (fun (b : β) => f b a))) (iSup.{0, succ u2} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) β (fun (b : β) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f b a))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : Countable.{succ u2} β] {f : β -> α -> ENNReal}, (forall (b : β), AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m (f b) μ) -> (Directed.{u1, succ u2} (α -> ENNReal) β (fun (x._@.Mathlib.MeasureTheory.Integral.Lebesgue._hyg.25659 : α -> ENNReal) (x._@.Mathlib.MeasureTheory.Integral.Lebesgue._hyg.25661 : α -> ENNReal) => LE.le.{u1} (α -> ENNReal) (Pi.hasLe.{u1, 0} α (fun (a._@.Mathlib.MeasureTheory.Integral.Lebesgue._hyg.25641 : α) => ENNReal) (fun (i : α) => Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))) x._@.Mathlib.MeasureTheory.Integral.Lebesgue._hyg.25659 x._@.Mathlib.MeasureTheory.Integral.Lebesgue._hyg.25661) f) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => iSup.{0, succ u2} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) β (fun (b : β) => f b a))) (iSup.{0, succ u2} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) β (fun (b : β) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f b a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_supr_directed MeasureTheory.lintegral_iSup_directedₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:38: in filter_upwards #[[], ["with", ident x, ident i, ident j], []]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: parse error @ arg 0: next failed, no more args -/
/-- Monotone convergence for a supremum over a directed family and indexed by a countable type. -/
theorem lintegral_iSup_directed [Countable β] {f : β → α → ℝ≥0∞} (hf : ∀ b, AEMeasurable (f b) μ)
    (h_directed : Directed (· ≤ ·) f) : (∫⁻ a, ⨆ b, f b a ∂μ) = ⨆ b, ∫⁻ a, f b a ∂μ :=
  by
  simp_rw [← iSup_apply]
  let p : α → (β → ENNReal) → Prop := fun x f' => Directed LE.le f'
  have hp : ∀ᵐ x ∂μ, p x fun i => f i x :=
    by
    trace
      "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:38: in filter_upwards #[[], [\"with\", ident x, ident i, ident j], []]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: parse error @ arg 0: next failed, no more args"
    obtain ⟨z, hz₁, hz₂⟩ := h_directed i j
    exact ⟨z, hz₁ x, hz₂ x⟩
  have h_ae_seq_directed : Directed LE.le (aeSeq hf p) :=
    by
    intro b₁ b₂
    obtain ⟨z, hz₁, hz₂⟩ := h_directed b₁ b₂
    refine' ⟨z, _, _⟩ <;>
      · intro x
        by_cases hx : x ∈ aeSeqSet hf p
        · repeat' rw [aeSeq.aeSeq_eq_fun_of_mem_aeSeqSet hf hx]
          apply_rules [hz₁, hz₂]
        · simp only [aeSeq, hx, if_false]
          exact le_rfl
  convert lintegral_supr_directed_of_measurable (aeSeq.measurable hf p) h_ae_seq_directed using 1
  · simp_rw [← iSup_apply]
    rw [lintegral_congr_ae (aeSeq.iSup hf hp).symm]
  · congr 1
    ext1 b
    rw [lintegral_congr_ae]
    symm
    refine' aeSeq.aeSeq_n_eq_fun_n_ae hf hp _
#align measure_theory.lintegral_supr_directed MeasureTheory.lintegral_iSup_directed

end

/- warning: measure_theory.lintegral_tsum -> MeasureTheory.lintegral_tsum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : Countable.{succ u2} β] {f : β -> α -> ENNReal}, (forall (i : β), AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m (f i) μ) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => tsum.{0, u2} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace β (fun (i : β) => f i a))) (tsum.{0, u2} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace β (fun (i : β) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f i a))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : Countable.{succ u2} β] {f : β -> α -> ENNReal}, (forall (i : β), AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m (f i) μ) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => tsum.{0, u2} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal β (fun (i : β) => f i a))) (tsum.{0, u2} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal β (fun (i : β) => MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f i a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_tsum MeasureTheory.lintegral_tsumₓ'. -/
theorem lintegral_tsum [Countable β] {f : β → α → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) μ) :
    (∫⁻ a, ∑' i, f i a ∂μ) = ∑' i, ∫⁻ a, f i a ∂μ :=
  by
  simp only [ENNReal.tsum_eq_iSup_sum]
  rw [lintegral_supr_directed]
  · simp [lintegral_finset_sum' _ fun i _ => hf i]
  · intro b
    exact Finset.aemeasurable_sum _ fun i _ => hf i
  · intro s t
    use s ∪ t
    constructor
    · exact fun a => Finset.sum_le_sum_of_subset (Finset.subset_union_left _ _)
    · exact fun a => Finset.sum_le_sum_of_subset (Finset.subset_union_right _ _)
#align measure_theory.lintegral_tsum MeasureTheory.lintegral_tsum

open Measure

/- warning: measure_theory.lintegral_Union₀ -> MeasureTheory.lintegral_iUnion₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : Countable.{succ u2} β] {s : β -> (Set.{u1} α)}, (forall (i : β), MeasureTheory.NullMeasurableSet.{u1} α m (s i) μ) -> (Pairwise.{u2} β (Function.onFun.{succ u2, succ u1, 1} β (Set.{u1} α) Prop (MeasureTheory.AEDisjoint.{u1} α m μ) s)) -> (forall (f : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (Set.iUnion.{u1, succ u2} α β (fun (i : β) => s i))) (fun (a : α) => f a)) (tsum.{0, u2} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace β (fun (i : β) => MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (s i)) (fun (a : α) => f a))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : Countable.{succ u2} β] {s : β -> (Set.{u1} α)}, (forall (i : β), MeasureTheory.NullMeasurableSet.{u1} α m (s i) μ) -> (Pairwise.{u2} β (Function.onFun.{succ u2, succ u1, 1} β (Set.{u1} α) Prop (MeasureTheory.AEDisjoint.{u1} α m μ) s)) -> (forall (f : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (Set.iUnion.{u1, succ u2} α β (fun (i : β) => s i))) (fun (a : α) => f a)) (tsum.{0, u2} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal β (fun (i : β) => MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (s i)) (fun (a : α) => f a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_Union₀ MeasureTheory.lintegral_iUnion₀ₓ'. -/
theorem lintegral_iUnion₀ [Countable β] {s : β → Set α} (hm : ∀ i, NullMeasurableSet (s i) μ)
    (hd : Pairwise (AEDisjoint μ on s)) (f : α → ℝ≥0∞) :
    (∫⁻ a in ⋃ i, s i, f a ∂μ) = ∑' i, ∫⁻ a in s i, f a ∂μ := by
  simp only [measure.restrict_Union_ae hd hm, lintegral_sum_measure]
#align measure_theory.lintegral_Union₀ MeasureTheory.lintegral_iUnion₀

/- warning: measure_theory.lintegral_Union -> MeasureTheory.lintegral_iUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : Countable.{succ u2} β] {s : β -> (Set.{u1} α)}, (forall (i : β), MeasurableSet.{u1} α m (s i)) -> (Pairwise.{u2} β (Function.onFun.{succ u2, succ u1, 1} β (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))) s)) -> (forall (f : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (Set.iUnion.{u1, succ u2} α β (fun (i : β) => s i))) (fun (a : α) => f a)) (tsum.{0, u2} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace β (fun (i : β) => MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (s i)) (fun (a : α) => f a))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : Countable.{succ u2} β] {s : β -> (Set.{u1} α)}, (forall (i : β), MeasurableSet.{u1} α m (s i)) -> (Pairwise.{u2} β (Function.onFun.{succ u2, succ u1, 1} β (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) s)) -> (forall (f : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (Set.iUnion.{u1, succ u2} α β (fun (i : β) => s i))) (fun (a : α) => f a)) (tsum.{0, u2} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal β (fun (i : β) => MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (s i)) (fun (a : α) => f a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_Union MeasureTheory.lintegral_iUnionₓ'. -/
theorem lintegral_iUnion [Countable β] {s : β → Set α} (hm : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (f : α → ℝ≥0∞) :
    (∫⁻ a in ⋃ i, s i, f a ∂μ) = ∑' i, ∫⁻ a in s i, f a ∂μ :=
  lintegral_iUnion₀ (fun i => (hm i).NullMeasurableSet) hd.AEDisjoint f
#align measure_theory.lintegral_Union MeasureTheory.lintegral_iUnion

/- warning: measure_theory.lintegral_bUnion₀ -> MeasureTheory.lintegral_biUnion₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {t : Set.{u2} β} {s : β -> (Set.{u1} α)}, (Set.Countable.{u2} β t) -> (forall (i : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) i t) -> (MeasureTheory.NullMeasurableSet.{u1} α m (s i) μ)) -> (Set.Pairwise.{u2} β t (Function.onFun.{succ u2, succ u1, 1} β (Set.{u1} α) Prop (MeasureTheory.AEDisjoint.{u1} α m μ) s)) -> (forall (f : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (Set.iUnion.{u1, succ u2} α β (fun (i : β) => Set.iUnion.{u1, 0} α (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) i t) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) i t) => s i)))) (fun (a : α) => f a)) (tsum.{0, u2} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) (fun (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) => MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (s ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t))))) i))) (fun (a : α) => f a))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {t : Set.{u2} β} {s : β -> (Set.{u1} α)}, (Set.Countable.{u2} β t) -> (forall (i : β), (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) i t) -> (MeasureTheory.NullMeasurableSet.{u1} α m (s i) μ)) -> (Set.Pairwise.{u2} β t (Function.onFun.{succ u2, succ u1, 1} β (Set.{u1} α) Prop (MeasureTheory.AEDisjoint.{u1} α m μ) s)) -> (forall (f : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (Set.iUnion.{u1, succ u2} α β (fun (i : β) => Set.iUnion.{u1, 0} α (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) i t) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) i t) => s i)))) (fun (a : α) => f a)) (tsum.{0, u2} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal (Set.Elem.{u2} β t) (fun (i : Set.Elem.{u2} β t) => MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (s (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x t) i))) (fun (a : α) => f a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_bUnion₀ MeasureTheory.lintegral_biUnion₀ₓ'. -/
theorem lintegral_biUnion₀ {t : Set β} {s : β → Set α} (ht : t.Countable)
    (hm : ∀ i ∈ t, NullMeasurableSet (s i) μ) (hd : t.Pairwise (AEDisjoint μ on s)) (f : α → ℝ≥0∞) :
    (∫⁻ a in ⋃ i ∈ t, s i, f a ∂μ) = ∑' i : t, ∫⁻ a in s i, f a ∂μ :=
  by
  haveI := ht.to_encodable
  rw [bUnion_eq_Union, lintegral_Union₀ (SetCoe.forall'.1 hm) (hd.subtype _ _)]
#align measure_theory.lintegral_bUnion₀ MeasureTheory.lintegral_biUnion₀

/- warning: measure_theory.lintegral_bUnion -> MeasureTheory.lintegral_biUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {t : Set.{u2} β} {s : β -> (Set.{u1} α)}, (Set.Countable.{u2} β t) -> (forall (i : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) i t) -> (MeasurableSet.{u1} α m (s i))) -> (Set.PairwiseDisjoint.{u1, u2} (Set.{u1} α) β (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) t s) -> (forall (f : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (Set.iUnion.{u1, succ u2} α β (fun (i : β) => Set.iUnion.{u1, 0} α (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) i t) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) i t) => s i)))) (fun (a : α) => f a)) (tsum.{0, u2} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) (fun (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) => MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (s ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t))))) i))) (fun (a : α) => f a))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {t : Set.{u2} β} {s : β -> (Set.{u1} α)}, (Set.Countable.{u2} β t) -> (forall (i : β), (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) i t) -> (MeasurableSet.{u1} α m (s i))) -> (Set.PairwiseDisjoint.{u1, u2} (Set.{u1} α) β (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) t s) -> (forall (f : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (Set.iUnion.{u1, succ u2} α β (fun (i : β) => Set.iUnion.{u1, 0} α (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) i t) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) i t) => s i)))) (fun (a : α) => f a)) (tsum.{0, u2} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal (Set.Elem.{u2} β t) (fun (i : Set.Elem.{u2} β t) => MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (s (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x t) i))) (fun (a : α) => f a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_bUnion MeasureTheory.lintegral_biUnionₓ'. -/
theorem lintegral_biUnion {t : Set β} {s : β → Set α} (ht : t.Countable)
    (hm : ∀ i ∈ t, MeasurableSet (s i)) (hd : t.PairwiseDisjoint s) (f : α → ℝ≥0∞) :
    (∫⁻ a in ⋃ i ∈ t, s i, f a ∂μ) = ∑' i : t, ∫⁻ a in s i, f a ∂μ :=
  lintegral_biUnion₀ ht (fun i hi => (hm i hi).NullMeasurableSet) hd.AEDisjoint f
#align measure_theory.lintegral_bUnion MeasureTheory.lintegral_biUnion

/- warning: measure_theory.lintegral_bUnion_finset₀ -> MeasureTheory.lintegral_biUnion_finset₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Finset.{u2} β} {t : β -> (Set.{u1} α)}, (Set.Pairwise.{u2} β ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) s) (Function.onFun.{succ u2, succ u1, 1} β (Set.{u1} α) Prop (MeasureTheory.AEDisjoint.{u1} α m μ) t)) -> (forall (b : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) -> (MeasureTheory.NullMeasurableSet.{u1} α m (t b) μ)) -> (forall (f : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (Set.iUnion.{u1, succ u2} α β (fun (b : β) => Set.iUnion.{u1, 0} α (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) => t b)))) (fun (a : α) => f a)) (Finset.sum.{0, u2} ENNReal β (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) s (fun (b : β) => MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (t b)) (fun (a : α) => f a))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Finset.{u2} β} {t : β -> (Set.{u1} α)}, (Set.Pairwise.{u2} β (Finset.toSet.{u2} β s) (Function.onFun.{succ u2, succ u1, 1} β (Set.{u1} α) Prop (MeasureTheory.AEDisjoint.{u1} α m μ) t)) -> (forall (b : β), (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b s) -> (MeasureTheory.NullMeasurableSet.{u1} α m (t b) μ)) -> (forall (f : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (Set.iUnion.{u1, succ u2} α β (fun (b : β) => Set.iUnion.{u1, 0} α (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b s) (fun (H : Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b s) => t b)))) (fun (a : α) => f a)) (Finset.sum.{0, u2} ENNReal β (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) s (fun (b : β) => MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (t b)) (fun (a : α) => f a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_bUnion_finset₀ MeasureTheory.lintegral_biUnion_finset₀ₓ'. -/
theorem lintegral_biUnion_finset₀ {s : Finset β} {t : β → Set α}
    (hd : Set.Pairwise (↑s) (AEDisjoint μ on t)) (hm : ∀ b ∈ s, NullMeasurableSet (t b) μ)
    (f : α → ℝ≥0∞) : (∫⁻ a in ⋃ b ∈ s, t b, f a ∂μ) = ∑ b in s, ∫⁻ a in t b, f a ∂μ := by
  simp only [← Finset.mem_coe, lintegral_bUnion₀ s.countable_to_set hm hd, ← s.tsum_subtype']
#align measure_theory.lintegral_bUnion_finset₀ MeasureTheory.lintegral_biUnion_finset₀

/- warning: measure_theory.lintegral_bUnion_finset -> MeasureTheory.lintegral_biUnion_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Finset.{u2} β} {t : β -> (Set.{u1} α)}, (Set.PairwiseDisjoint.{u1, u2} (Set.{u1} α) β (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) s) t) -> (forall (b : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) -> (MeasurableSet.{u1} α m (t b))) -> (forall (f : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (Set.iUnion.{u1, succ u2} α β (fun (b : β) => Set.iUnion.{u1, 0} α (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) => t b)))) (fun (a : α) => f a)) (Finset.sum.{0, u2} ENNReal β (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) s (fun (b : β) => MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (t b)) (fun (a : α) => f a))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Finset.{u2} β} {t : β -> (Set.{u1} α)}, (Set.PairwiseDisjoint.{u1, u2} (Set.{u1} α) β (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Finset.toSet.{u2} β s) t) -> (forall (b : β), (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b s) -> (MeasurableSet.{u1} α m (t b))) -> (forall (f : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (Set.iUnion.{u1, succ u2} α β (fun (b : β) => Set.iUnion.{u1, 0} α (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b s) (fun (H : Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b s) => t b)))) (fun (a : α) => f a)) (Finset.sum.{0, u2} ENNReal β (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) s (fun (b : β) => MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (t b)) (fun (a : α) => f a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_bUnion_finset MeasureTheory.lintegral_biUnion_finsetₓ'. -/
theorem lintegral_biUnion_finset {s : Finset β} {t : β → Set α} (hd : Set.PairwiseDisjoint (↑s) t)
    (hm : ∀ b ∈ s, MeasurableSet (t b)) (f : α → ℝ≥0∞) :
    (∫⁻ a in ⋃ b ∈ s, t b, f a ∂μ) = ∑ b in s, ∫⁻ a in t b, f a ∂μ :=
  lintegral_biUnion_finset₀ hd.AEDisjoint (fun b hb => (hm b hb).NullMeasurableSet) f
#align measure_theory.lintegral_bUnion_finset MeasureTheory.lintegral_biUnion_finset

/- warning: measure_theory.lintegral_Union_le -> MeasureTheory.lintegral_iUnion_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : Countable.{succ u2} β] (s : β -> (Set.{u1} α)) (f : α -> ENNReal), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (Set.iUnion.{u1, succ u2} α β (fun (i : β) => s i))) (fun (a : α) => f a)) (tsum.{0, u2} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace β (fun (i : β) => MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (s i)) (fun (a : α) => f a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : Countable.{succ u2} β] (s : β -> (Set.{u1} α)) (f : α -> ENNReal), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (Set.iUnion.{u1, succ u2} α β (fun (i : β) => s i))) (fun (a : α) => f a)) (tsum.{0, u2} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal β (fun (i : β) => MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (s i)) (fun (a : α) => f a)))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_Union_le MeasureTheory.lintegral_iUnion_leₓ'. -/
theorem lintegral_iUnion_le [Countable β] (s : β → Set α) (f : α → ℝ≥0∞) :
    (∫⁻ a in ⋃ i, s i, f a ∂μ) ≤ ∑' i, ∫⁻ a in s i, f a ∂μ :=
  by
  rw [← lintegral_sum_measure]
  exact lintegral_mono' restrict_Union_le le_rfl
#align measure_theory.lintegral_Union_le MeasureTheory.lintegral_iUnion_le

/- warning: measure_theory.lintegral_union -> MeasureTheory.lintegral_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal} {A : Set.{u1} α} {B : Set.{u1} α}, (MeasurableSet.{u1} α m B) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) A B) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) A B)) (fun (a : α) => f a)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ A) (fun (a : α) => f a)) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ B) (fun (a : α) => f a))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal} {A : Set.{u1} α} {B : Set.{u1} α}, (MeasurableSet.{u1} α m B) -> (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) A B) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) A B)) (fun (a : α) => f a)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ A) (fun (a : α) => f a)) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ B) (fun (a : α) => f a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_union MeasureTheory.lintegral_unionₓ'. -/
theorem lintegral_union {f : α → ℝ≥0∞} {A B : Set α} (hB : MeasurableSet B) (hAB : Disjoint A B) :
    (∫⁻ a in A ∪ B, f a ∂μ) = (∫⁻ a in A, f a ∂μ) + ∫⁻ a in B, f a ∂μ := by
  rw [restrict_union hAB hB, lintegral_add_measure]
#align measure_theory.lintegral_union MeasureTheory.lintegral_union

/- warning: measure_theory.lintegral_inter_add_diff -> MeasureTheory.lintegral_inter_add_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {B : Set.{u1} α} (f : α -> ENNReal) (A : Set.{u1} α), (MeasurableSet.{u1} α m B) -> (Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) A B)) (fun (x : α) => f x)) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) A B)) (fun (x : α) => f x))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ A) (fun (x : α) => f x)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {B : Set.{u1} α} (f : α -> ENNReal) (A : Set.{u1} α), (MeasurableSet.{u1} α m B) -> (Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) A B)) (fun (x : α) => f x)) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) A B)) (fun (x : α) => f x))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ A) (fun (x : α) => f x)))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_inter_add_diff MeasureTheory.lintegral_inter_add_diffₓ'. -/
theorem lintegral_inter_add_diff {B : Set α} (f : α → ℝ≥0∞) (A : Set α) (hB : MeasurableSet B) :
    ((∫⁻ x in A ∩ B, f x ∂μ) + ∫⁻ x in A \ B, f x ∂μ) = ∫⁻ x in A, f x ∂μ := by
  rw [← lintegral_add_measure, restrict_inter_add_diff _ hB]
#align measure_theory.lintegral_inter_add_diff MeasureTheory.lintegral_inter_add_diff

/- warning: measure_theory.lintegral_add_compl -> MeasureTheory.lintegral_add_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : α -> ENNReal) {A : Set.{u1} α}, (MeasurableSet.{u1} α m A) -> (Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ A) (fun (x : α) => f x)) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) A)) (fun (x : α) => f x))) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : α -> ENNReal) {A : Set.{u1} α}, (MeasurableSet.{u1} α m A) -> (Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ A) (fun (x : α) => f x)) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) A)) (fun (x : α) => f x))) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_add_compl MeasureTheory.lintegral_add_complₓ'. -/
theorem lintegral_add_compl (f : α → ℝ≥0∞) {A : Set α} (hA : MeasurableSet A) :
    ((∫⁻ x in A, f x ∂μ) + ∫⁻ x in Aᶜ, f x ∂μ) = ∫⁻ x, f x ∂μ := by
  rw [← lintegral_add_measure, measure.restrict_add_restrict_compl hA]
#align measure_theory.lintegral_add_compl MeasureTheory.lintegral_add_compl

/- warning: measure_theory.lintegral_max -> MeasureTheory.lintegral_max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal} {g : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace g) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => LinearOrder.max.{0} ENNReal (ConditionallyCompleteLinearOrder.toLinearOrder.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.completeLinearOrder))) (f x) (g x))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (setOf.{u1} α (fun (x : α) => LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (f x) (g x)))) (fun (x : α) => g x)) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (setOf.{u1} α (fun (x : α) => LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (g x) (f x)))) (fun (x : α) => f x))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal} {g : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace g) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => Max.max.{0} ENNReal (CanonicallyLinearOrderedAddMonoid.toMax.{0} ENNReal ENNReal.instCanonicallyLinearOrderedAddMonoidENNReal) (f x) (g x))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (setOf.{u1} α (fun (x : α) => LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (f x) (g x)))) (fun (x : α) => g x)) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (setOf.{u1} α (fun (x : α) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (g x) (f x)))) (fun (x : α) => f x))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_max MeasureTheory.lintegral_maxₓ'. -/
theorem lintegral_max {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, max (f x) (g x) ∂μ) =
      (∫⁻ x in { x | f x ≤ g x }, g x ∂μ) + ∫⁻ x in { x | g x < f x }, f x ∂μ :=
  by
  have hm : MeasurableSet { x | f x ≤ g x } := measurableSet_le hf hg
  rw [← lintegral_add_compl (fun x => max (f x) (g x)) hm]
  simp only [← compl_set_of, ← not_le]
  refine' congr_arg₂ (· + ·) (set_lintegral_congr_fun hm _) (set_lintegral_congr_fun hm.compl _)
  exacts[ae_of_all _ fun x => max_eq_right, ae_of_all _ fun x hx => max_eq_left (not_le.1 hx).le]
#align measure_theory.lintegral_max MeasureTheory.lintegral_max

/- warning: measure_theory.set_lintegral_max -> MeasureTheory.set_lintegral_max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal} {g : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace g) -> (forall (s : Set.{u1} α), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => LinearOrder.max.{0} ENNReal (ConditionallyCompleteLinearOrder.toLinearOrder.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.completeLinearOrder))) (f x) (g x))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (x : α) => LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (f x) (g x))))) (fun (x : α) => g x)) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (setOf.{u1} α (fun (x : α) => LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (g x) (f x))))) (fun (x : α) => f x))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal} {g : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace g) -> (forall (s : Set.{u1} α), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => Max.max.{0} ENNReal (CanonicallyLinearOrderedAddMonoid.toMax.{0} ENNReal ENNReal.instCanonicallyLinearOrderedAddMonoidENNReal) (f x) (g x))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (setOf.{u1} α (fun (x : α) => LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (f x) (g x))))) (fun (x : α) => g x)) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (setOf.{u1} α (fun (x : α) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (g x) (f x))))) (fun (x : α) => f x))))
Case conversion may be inaccurate. Consider using '#align measure_theory.set_lintegral_max MeasureTheory.set_lintegral_maxₓ'. -/
theorem set_lintegral_max {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (s : Set α) :
    (∫⁻ x in s, max (f x) (g x) ∂μ) =
      (∫⁻ x in s ∩ { x | f x ≤ g x }, g x ∂μ) + ∫⁻ x in s ∩ { x | g x < f x }, f x ∂μ :=
  by
  rw [lintegral_max hf hg, restrict_restrict, restrict_restrict, inter_comm s, inter_comm s]
  exacts[measurableSet_lt hg hf, measurableSet_le hf hg]
#align measure_theory.set_lintegral_max MeasureTheory.set_lintegral_max

#print MeasureTheory.lintegral_map /-
theorem lintegral_map {mβ : MeasurableSpace β} {f : β → ℝ≥0∞} {g : α → β} (hf : Measurable f)
    (hg : Measurable g) : (∫⁻ a, f a ∂map g μ) = ∫⁻ a, f (g a) ∂μ :=
  by
  simp only [lintegral_eq_supr_eapprox_lintegral, hf, hf.comp hg]
  congr with n : 1
  convert simple_func.lintegral_map _ hg
  ext1 x; simp only [eapprox_comp hf hg, coe_comp]
#align measure_theory.lintegral_map MeasureTheory.lintegral_map
-/

#print MeasureTheory.lintegral_map' /-
theorem lintegral_map' {mβ : MeasurableSpace β} {f : β → ℝ≥0∞} {g : α → β}
    (hf : AEMeasurable f (Measure.map g μ)) (hg : AEMeasurable g μ) :
    (∫⁻ a, f a ∂Measure.map g μ) = ∫⁻ a, f (g a) ∂μ :=
  calc
    (∫⁻ a, f a ∂Measure.map g μ) = ∫⁻ a, hf.mk f a ∂Measure.map g μ :=
      lintegral_congr_ae hf.ae_eq_mk
    _ = ∫⁻ a, hf.mk f a ∂Measure.map (hg.mk g) μ :=
      by
      congr 1
      exact measure.map_congr hg.ae_eq_mk
    _ = ∫⁻ a, hf.mk f (hg.mk g a) ∂μ := (lintegral_map hf.measurable_mk hg.measurable_mk)
    _ = ∫⁻ a, hf.mk f (g a) ∂μ := (lintegral_congr_ae <| hg.ae_eq_mk.symm.fun_comp _)
    _ = ∫⁻ a, f (g a) ∂μ := lintegral_congr_ae (ae_eq_comp hg hf.ae_eq_mk.symm)
    
#align measure_theory.lintegral_map' MeasureTheory.lintegral_map'
-/

/- warning: measure_theory.lintegral_map_le -> MeasureTheory.lintegral_map_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {mβ : MeasurableSpace.{u2} β} (f : β -> ENNReal) {g : α -> β}, (Measurable.{u1, u2} α β m mβ g) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u2} β mβ (MeasureTheory.Measure.map.{u1, u2} α β mβ m g μ) (fun (a : β) => f a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f (g a))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {mβ : MeasurableSpace.{u2} β} (f : β -> ENNReal) {g : α -> β}, (Measurable.{u1, u2} α β m mβ g) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u2} β mβ (MeasureTheory.Measure.map.{u1, u2} α β mβ m g μ) (fun (a : β) => f a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f (g a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_map_le MeasureTheory.lintegral_map_leₓ'. -/
theorem lintegral_map_le {mβ : MeasurableSpace β} (f : β → ℝ≥0∞) {g : α → β} (hg : Measurable g) :
    (∫⁻ a, f a ∂Measure.map g μ) ≤ ∫⁻ a, f (g a) ∂μ :=
  by
  rw [← supr_lintegral_measurable_le_eq_lintegral, ← supr_lintegral_measurable_le_eq_lintegral]
  refine' iSup₂_le fun i hi => iSup_le fun h'i => _
  refine' le_iSup₂_of_le (i ∘ g) (hi.comp hg) _
  exact le_iSup_of_le (fun x => h'i (g x)) (le_of_eq (lintegral_map hi hg))
#align measure_theory.lintegral_map_le MeasureTheory.lintegral_map_le

#print MeasureTheory.lintegral_comp /-
theorem lintegral_comp [MeasurableSpace β] {f : β → ℝ≥0∞} {g : α → β} (hf : Measurable f)
    (hg : Measurable g) : lintegral μ (f ∘ g) = ∫⁻ a, f a ∂map g μ :=
  (lintegral_map hf hg).symm
#align measure_theory.lintegral_comp MeasureTheory.lintegral_comp
-/

#print MeasureTheory.set_lintegral_map /-
theorem set_lintegral_map [MeasurableSpace β] {f : β → ℝ≥0∞} {g : α → β} {s : Set β}
    (hs : MeasurableSet s) (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ y in s, f y ∂map g μ) = ∫⁻ x in g ⁻¹' s, f (g x) ∂μ := by
  rw [restrict_map hg hs, lintegral_map hf hg]
#align measure_theory.set_lintegral_map MeasureTheory.set_lintegral_map
-/

/- warning: measure_theory.lintegral_indicator_const_comp -> MeasureTheory.lintegral_indicator_const_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {mβ : MeasurableSpace.{u2} β} {f : α -> β} {s : Set.{u2} β}, (Measurable.{u1, u2} α β m mβ f) -> (MeasurableSet.{u2} β mβ s) -> (forall (c : ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => Set.indicator.{u2, 0} β ENNReal ENNReal.hasZero s (fun (_x : β) => c) (f a))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) c (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (Set.preimage.{u1, u2} α β f s))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {mβ : MeasurableSpace.{u2} β} {f : α -> β} {s : Set.{u2} β}, (Measurable.{u1, u2} α β m mβ f) -> (MeasurableSet.{u2} β mβ s) -> (forall (c : ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => Set.indicator.{u2, 0} β ENNReal instENNRealZero s (fun (_x : β) => c) (f a))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) c (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) (Set.preimage.{u1, u2} α β f s))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_indicator_const_comp MeasureTheory.lintegral_indicator_const_compₓ'. -/
theorem lintegral_indicator_const_comp {mβ : MeasurableSpace β} {f : α → β} {s : Set β}
    (hf : Measurable f) (hs : MeasurableSet s) (c : ℝ≥0∞) :
    (∫⁻ a, s.indicator (fun _ => c) (f a) ∂μ) = c * μ (f ⁻¹' s) := by
  rw [lintegral_comp (measurable_const.indicator hs) hf, lintegral_indicator_const hs,
    measure.map_apply hf hs]
#align measure_theory.lintegral_indicator_const_comp MeasureTheory.lintegral_indicator_const_comp

#print MeasurableEmbedding.lintegral_map /-
/-- If `g : α → β` is a measurable embedding and `f : β → ℝ≥0∞` is any function (not necessarily
measurable), then `∫⁻ a, f a ∂(map g μ) = ∫⁻ a, f (g a) ∂μ`. Compare with `lintegral_map` wich
applies to any measurable `g : α → β` but requires that `f` is measurable as well. -/
theorem MeasurableEmbedding.lintegral_map [MeasurableSpace β] {g : α → β}
    (hg : MeasurableEmbedding g) (f : β → ℝ≥0∞) : (∫⁻ a, f a ∂map g μ) = ∫⁻ a, f (g a) ∂μ :=
  by
  rw [lintegral, lintegral]
  refine' le_antisymm (iSup₂_le fun f₀ hf₀ => _) (iSup₂_le fun f₀ hf₀ => _)
  · rw [simple_func.lintegral_map _ hg.measurable]
    have : (f₀.comp g hg.measurable : α → ℝ≥0∞) ≤ f ∘ g := fun x => hf₀ (g x)
    exact le_iSup_of_le (comp f₀ g hg.measurable) (le_iSup _ this)
  · rw [← f₀.extend_comp_eq hg (const _ 0), ← simple_func.lintegral_map, ←
      simple_func.lintegral_eq_lintegral, ← lintegral]
    refine' lintegral_mono_ae (hg.ae_map_iff.2 <| eventually_of_forall fun x => _)
    exact (extend_apply _ _ _ _).trans_le (hf₀ _)
#align measurable_embedding.lintegral_map MeasurableEmbedding.lintegral_map
-/

#print MeasureTheory.lintegral_map_equiv /-
/-- The `lintegral` transforms appropriately under a measurable equivalence `g : α ≃ᵐ β`.
(Compare `lintegral_map`, which applies to a wider class of functions `g : α → β`, but requires
measurability of the function being integrated.) -/
theorem lintegral_map_equiv [MeasurableSpace β] (f : β → ℝ≥0∞) (g : α ≃ᵐ β) :
    (∫⁻ a, f a ∂map g μ) = ∫⁻ a, f (g a) ∂μ :=
  g.MeasurableEmbedding.lintegral_map f
#align measure_theory.lintegral_map_equiv MeasureTheory.lintegral_map_equiv
-/

#print MeasureTheory.MeasurePreserving.lintegral_comp /-
theorem MeasurePreserving.lintegral_comp {mb : MeasurableSpace β} {ν : Measure β} {g : α → β}
    (hg : MeasurePreserving g μ ν) {f : β → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ a, f (g a) ∂μ) = ∫⁻ b, f b ∂ν := by rw [← hg.map_eq, lintegral_map hf hg.measurable]
#align measure_theory.measure_preserving.lintegral_comp MeasureTheory.MeasurePreserving.lintegral_comp
-/

#print MeasureTheory.MeasurePreserving.lintegral_comp_emb /-
theorem MeasurePreserving.lintegral_comp_emb {mb : MeasurableSpace β} {ν : Measure β} {g : α → β}
    (hg : MeasurePreserving g μ ν) (hge : MeasurableEmbedding g) (f : β → ℝ≥0∞) :
    (∫⁻ a, f (g a) ∂μ) = ∫⁻ b, f b ∂ν := by rw [← hg.map_eq, hge.lintegral_map]
#align measure_theory.measure_preserving.lintegral_comp_emb MeasureTheory.MeasurePreserving.lintegral_comp_emb
-/

#print MeasureTheory.MeasurePreserving.set_lintegral_comp_preimage /-
theorem MeasurePreserving.set_lintegral_comp_preimage {mb : MeasurableSpace β} {ν : Measure β}
    {g : α → β} (hg : MeasurePreserving g μ ν) {s : Set β} (hs : MeasurableSet s) {f : β → ℝ≥0∞}
    (hf : Measurable f) : (∫⁻ a in g ⁻¹' s, f (g a) ∂μ) = ∫⁻ b in s, f b ∂ν := by
  rw [← hg.map_eq, set_lintegral_map hs hf hg.measurable]
#align measure_theory.measure_preserving.set_lintegral_comp_preimage MeasureTheory.MeasurePreserving.set_lintegral_comp_preimage
-/

#print MeasureTheory.MeasurePreserving.set_lintegral_comp_preimage_emb /-
theorem MeasurePreserving.set_lintegral_comp_preimage_emb {mb : MeasurableSpace β} {ν : Measure β}
    {g : α → β} (hg : MeasurePreserving g μ ν) (hge : MeasurableEmbedding g) (f : β → ℝ≥0∞)
    (s : Set β) : (∫⁻ a in g ⁻¹' s, f (g a) ∂μ) = ∫⁻ b in s, f b ∂ν := by
  rw [← hg.map_eq, hge.restrict_map, hge.lintegral_map]
#align measure_theory.measure_preserving.set_lintegral_comp_preimage_emb MeasureTheory.MeasurePreserving.set_lintegral_comp_preimage_emb
-/

#print MeasureTheory.MeasurePreserving.set_lintegral_comp_emb /-
theorem MeasurePreserving.set_lintegral_comp_emb {mb : MeasurableSpace β} {ν : Measure β}
    {g : α → β} (hg : MeasurePreserving g μ ν) (hge : MeasurableEmbedding g) (f : β → ℝ≥0∞)
    (s : Set α) : (∫⁻ a in s, f (g a) ∂μ) = ∫⁻ b in g '' s, f b ∂ν := by
  rw [← hg.set_lintegral_comp_preimage_emb hge, preimage_image_eq _ hge.injective]
#align measure_theory.measure_preserving.set_lintegral_comp_emb MeasureTheory.MeasurePreserving.set_lintegral_comp_emb
-/

section DiracAndCount

/- warning: measurable_space.top.measurable_singleton_class -> MeasurableSpace.Top.measurableSingletonClass is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, MeasurableSingletonClass.{u1} α (Top.top.{u1} (MeasurableSpace.{u1} α) (CompleteLattice.toHasTop.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.completeLattice.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}}, MeasurableSingletonClass.{u1} α (Top.top.{u1} (MeasurableSpace.{u1} α) (CompleteLattice.toTop.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.instCompleteLatticeMeasurableSpace.{u1} α)))
Case conversion may be inaccurate. Consider using '#align measurable_space.top.measurable_singleton_class MeasurableSpace.Top.measurableSingletonClassₓ'. -/
instance (priority := 10) MeasurableSpace.Top.measurableSingletonClass {α : Type _} :
    @MeasurableSingletonClass α (⊤ : MeasurableSpace α)
    where measurableSet_singleton i := MeasurableSpace.measurableSet_top
#align measurable_space.top.measurable_singleton_class MeasurableSpace.Top.measurableSingletonClass

variable [MeasurableSpace α]

#print MeasureTheory.lintegral_dirac' /-
theorem lintegral_dirac' (a : α) {f : α → ℝ≥0∞} (hf : Measurable f) : (∫⁻ a, f a ∂dirac a) = f a :=
  by simp [lintegral_congr_ae (ae_eq_dirac' hf)]
#align measure_theory.lintegral_dirac' MeasureTheory.lintegral_dirac'
-/

#print MeasureTheory.lintegral_dirac /-
theorem lintegral_dirac [MeasurableSingletonClass α] (a : α) (f : α → ℝ≥0∞) :
    (∫⁻ a, f a ∂dirac a) = f a := by simp [lintegral_congr_ae (ae_eq_dirac f)]
#align measure_theory.lintegral_dirac MeasureTheory.lintegral_dirac
-/

/- warning: measure_theory.set_lintegral_dirac' -> MeasureTheory.set_lintegral_dirac' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {a : α} {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal _inst_1 ENNReal.measurableSpace f) -> (forall {s : Set.{u1} α}, (MeasurableSet.{u1} α _inst_1 s) -> (forall [_inst_2 : Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)], Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 (MeasureTheory.Measure.restrict.{u1} α _inst_1 (MeasureTheory.Measure.dirac.{u1} α _inst_1 a) s) (fun (x : α) => f x)) (ite.{1} ENNReal (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) _inst_2 (f a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {a : α} {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal _inst_1 ENNReal.measurableSpace f) -> (forall {s : Set.{u1} α}, (MeasurableSet.{u1} α _inst_1 s) -> (forall [_inst_2 : Decidable (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s)], Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 (MeasureTheory.Measure.restrict.{u1} α _inst_1 (MeasureTheory.Measure.dirac.{u1} α _inst_1 a) s) (fun (x : α) => f x)) (ite.{1} ENNReal (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) _inst_2 (f a) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.set_lintegral_dirac' MeasureTheory.set_lintegral_dirac'ₓ'. -/
theorem set_lintegral_dirac' {a : α} {f : α → ℝ≥0∞} (hf : Measurable f) {s : Set α}
    (hs : MeasurableSet s) [Decidable (a ∈ s)] :
    (∫⁻ x in s, f x ∂Measure.dirac a) = if a ∈ s then f a else 0 :=
  by
  rw [restrict_dirac' hs]
  swap; · infer_instance
  split_ifs
  · exact lintegral_dirac' _ hf
  · exact lintegral_zero_measure _
#align measure_theory.set_lintegral_dirac' MeasureTheory.set_lintegral_dirac'

/- warning: measure_theory.set_lintegral_dirac -> MeasureTheory.set_lintegral_dirac is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {a : α} (f : α -> ENNReal) (s : Set.{u1} α) [_inst_2 : MeasurableSingletonClass.{u1} α _inst_1] [_inst_3 : Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)], Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 (MeasureTheory.Measure.restrict.{u1} α _inst_1 (MeasureTheory.Measure.dirac.{u1} α _inst_1 a) s) (fun (x : α) => f x)) (ite.{1} ENNReal (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) _inst_3 (f a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {a : α} (f : α -> ENNReal) (s : Set.{u1} α) [_inst_2 : MeasurableSingletonClass.{u1} α _inst_1] [_inst_3 : Decidable (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s)], Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 (MeasureTheory.Measure.restrict.{u1} α _inst_1 (MeasureTheory.Measure.dirac.{u1} α _inst_1 a) s) (fun (x : α) => f x)) (ite.{1} ENNReal (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) _inst_3 (f a) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align measure_theory.set_lintegral_dirac MeasureTheory.set_lintegral_diracₓ'. -/
theorem set_lintegral_dirac {a : α} (f : α → ℝ≥0∞) (s : Set α) [MeasurableSingletonClass α]
    [Decidable (a ∈ s)] : (∫⁻ x in s, f x ∂Measure.dirac a) = if a ∈ s then f a else 0 :=
  by
  rw [restrict_dirac]
  split_ifs
  · exact lintegral_dirac _ _
  · exact lintegral_zero_measure _
#align measure_theory.set_lintegral_dirac MeasureTheory.set_lintegral_dirac

/- warning: measure_theory.lintegral_count' -> MeasureTheory.lintegral_count' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal _inst_1 ENNReal.measurableSpace f) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 (MeasureTheory.Measure.count.{u1} α _inst_1) (fun (a : α) => f a)) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => f a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal _inst_1 ENNReal.measurableSpace f) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 (MeasureTheory.Measure.count.{u1} α _inst_1) (fun (a : α) => f a)) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => f a)))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_count' MeasureTheory.lintegral_count'ₓ'. -/
theorem lintegral_count' {f : α → ℝ≥0∞} (hf : Measurable f) : (∫⁻ a, f a ∂count) = ∑' a, f a :=
  by
  rw [count, lintegral_sum_measure]
  congr
  exact funext fun a => lintegral_dirac' a hf
#align measure_theory.lintegral_count' MeasureTheory.lintegral_count'

/- warning: measure_theory.lintegral_count -> MeasureTheory.lintegral_count is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSingletonClass.{u1} α _inst_1] (f : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 (MeasureTheory.Measure.count.{u1} α _inst_1) (fun (a : α) => f a)) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => f a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSingletonClass.{u1} α _inst_1] (f : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 (MeasureTheory.Measure.count.{u1} α _inst_1) (fun (a : α) => f a)) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => f a))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_count MeasureTheory.lintegral_countₓ'. -/
theorem lintegral_count [MeasurableSingletonClass α] (f : α → ℝ≥0∞) :
    (∫⁻ a, f a ∂count) = ∑' a, f a :=
  by
  rw [count, lintegral_sum_measure]
  congr
  exact funext fun a => lintegral_dirac a f
#align measure_theory.lintegral_count MeasureTheory.lintegral_count

/- warning: ennreal.tsum_const_eq -> ENNReal.tsum_const_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSingletonClass.{u1} α _inst_1] (c : ENNReal), Eq.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (i : α) => c)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) c (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) (MeasureTheory.Measure.count.{u1} α _inst_1) (Set.univ.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSingletonClass.{u1} α _inst_1] (c : ENNReal), Eq.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (i : α) => c)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) c (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 (MeasureTheory.Measure.count.{u1} α _inst_1)) (Set.univ.{u1} α)))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_const_eq ENNReal.tsum_const_eqₓ'. -/
theorem ENNReal.tsum_const_eq [MeasurableSingletonClass α] (c : ℝ≥0∞) :
    (∑' i : α, c) = c * Measure.count (univ : Set α) := by rw [← lintegral_count, lintegral_const]
#align ennreal.tsum_const_eq ENNReal.tsum_const_eq

/- warning: ennreal.count_const_le_le_of_tsum_le -> ENNReal.count_const_le_le_of_tsum_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSingletonClass.{u1} α _inst_1] {a : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal _inst_1 ENNReal.measurableSpace a) -> (forall {c : ENNReal}, (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (i : α) => a i)) c) -> (forall {ε : ENNReal}, (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Ne.{1} ENNReal ε (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) (MeasureTheory.Measure.count.{u1} α _inst_1) (setOf.{u1} α (fun (i : α) => LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (a i)))) (HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toHasDiv.{0} ENNReal ENNReal.divInvMonoid)) c ε))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSingletonClass.{u1} α _inst_1] {a : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal _inst_1 ENNReal.measurableSpace a) -> (forall {c : ENNReal}, (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (i : α) => a i)) c) -> (forall {ε : ENNReal}, (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Ne.{1} ENNReal ε (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 (MeasureTheory.Measure.count.{u1} α _inst_1)) (setOf.{u1} α (fun (i : α) => LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (a i)))) (HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toDiv.{0} ENNReal ENNReal.instDivInvMonoidENNReal)) c ε))))
Case conversion may be inaccurate. Consider using '#align ennreal.count_const_le_le_of_tsum_le ENNReal.count_const_le_le_of_tsum_leₓ'. -/
/-- Markov's inequality for the counting measure with hypothesis using `tsum` in `ℝ≥0∞`. -/
theorem ENNReal.count_const_le_le_of_tsum_le [MeasurableSingletonClass α] {a : α → ℝ≥0∞}
    (a_mble : Measurable a) {c : ℝ≥0∞} (tsum_le_c : (∑' i, a i) ≤ c) {ε : ℝ≥0∞} (ε_ne_zero : ε ≠ 0)
    (ε_ne_top : ε ≠ ∞) : Measure.count { i : α | ε ≤ a i } ≤ c / ε :=
  by
  rw [← lintegral_count] at tsum_le_c
  apply (MeasureTheory.meas_ge_le_lintegral_div a_mble.ae_measurable ε_ne_zero ε_ne_top).trans
  exact ENNReal.div_le_div tsum_le_c rfl.le
#align ennreal.count_const_le_le_of_tsum_le ENNReal.count_const_le_le_of_tsum_le

/- warning: nnreal.count_const_le_le_of_tsum_le -> NNReal.count_const_le_le_of_tsum_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSingletonClass.{u1} α _inst_1] {a : α -> NNReal}, (Measurable.{u1, 0} α NNReal _inst_1 NNReal.measurableSpace a) -> (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace a) -> (forall {c : NNReal}, (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace α (fun (i : α) => a i)) c) -> (forall {ε : NNReal}, (Ne.{1} NNReal ε (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) (MeasureTheory.Measure.count.{u1} α _inst_1) (setOf.{u1} α (fun (i : α) => LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) ε (a i)))) (HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toHasDiv.{0} ENNReal ENNReal.divInvMonoid)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) c) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) ε)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSingletonClass.{u1} α _inst_1] {a : α -> NNReal}, (Measurable.{u1, 0} α NNReal _inst_1 NNReal.measurableSpace a) -> (Summable.{0, u1} NNReal α (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal a) -> (forall {c : NNReal}, (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (tsum.{0, u1} NNReal (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal α (fun (i : α) => a i)) c) -> (forall {ε : NNReal}, (Ne.{1} NNReal ε (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 (MeasureTheory.Measure.count.{u1} α _inst_1)) (setOf.{u1} α (fun (i : α) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) ε (a i)))) (HDiv.hDiv.{0, 0, 0} ENNReal ENNReal ENNReal (instHDiv.{0} ENNReal (DivInvMonoid.toDiv.{0} ENNReal ENNReal.instDivInvMonoidENNReal)) (ENNReal.some c) (ENNReal.some ε)))))
Case conversion may be inaccurate. Consider using '#align nnreal.count_const_le_le_of_tsum_le NNReal.count_const_le_le_of_tsum_leₓ'. -/
/-- Markov's inequality for counting measure with hypothesis using `tsum` in `ℝ≥0`. -/
theorem NNReal.count_const_le_le_of_tsum_le [MeasurableSingletonClass α] {a : α → ℝ≥0}
    (a_mble : Measurable a) (a_summable : Summable a) {c : ℝ≥0} (tsum_le_c : (∑' i, a i) ≤ c)
    {ε : ℝ≥0} (ε_ne_zero : ε ≠ 0) : Measure.count { i : α | ε ≤ a i } ≤ c / ε :=
  by
  rw [show (fun i => ε ≤ a i) = fun i => (ε : ℝ≥0∞) ≤ (coe ∘ a) i
      by
      funext i
      simp only [ENNReal.coe_le_coe]]
  apply
    ENNReal.count_const_le_le_of_tsum_le (measurable_coe_nnreal_ennreal.comp a_mble) _
      (by exact_mod_cast ε_ne_zero) (@ENNReal.coe_ne_top ε)
  convert ennreal.coe_le_coe.mpr tsum_le_c
  rw [ENNReal.tsum_coe_eq a_summable.has_sum]
#align nnreal.count_const_le_le_of_tsum_le NNReal.count_const_le_le_of_tsum_le

end DiracAndCount

section Countable

/-!
### Lebesgue integral over finite and countable types and sets
-/


/- warning: measure_theory.lintegral_countable' -> MeasureTheory.lintegral_countable' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : Countable.{succ u1} α] [_inst_2 : MeasurableSingletonClass.{u1} α m] (f : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f a) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : Countable.{succ u1} α] [_inst_2 : MeasurableSingletonClass.{u1} α m] (f : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (f a) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_countable' MeasureTheory.lintegral_countable'ₓ'. -/
theorem lintegral_countable' [Countable α] [MeasurableSingletonClass α] (f : α → ℝ≥0∞) :
    (∫⁻ a, f a ∂μ) = ∑' a, f a * μ {a} :=
  by
  conv_lhs => rw [← sum_smul_dirac μ, lintegral_sum_measure]
  congr 1 with a : 1
  rw [lintegral_smul_measure, lintegral_dirac, mul_comm]
#align measure_theory.lintegral_countable' MeasureTheory.lintegral_countable'

/- warning: measure_theory.lintegral_singleton' -> MeasureTheory.lintegral_singleton' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (forall (a : α), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)) (fun (x : α) => f x)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f a) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (forall (a : α), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a)) (fun (x : α) => f x)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (f a) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_singleton' MeasureTheory.lintegral_singleton'ₓ'. -/
theorem lintegral_singleton' {f : α → ℝ≥0∞} (hf : Measurable f) (a : α) :
    (∫⁻ x in {a}, f x ∂μ) = f a * μ {a} := by
  simp only [restrict_singleton, lintegral_smul_measure, lintegral_dirac' _ hf, mul_comm]
#align measure_theory.lintegral_singleton' MeasureTheory.lintegral_singleton'

/- warning: measure_theory.lintegral_singleton -> MeasureTheory.lintegral_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : MeasurableSingletonClass.{u1} α m] (f : α -> ENNReal) (a : α), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)) (fun (x : α) => f x)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f a) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : MeasurableSingletonClass.{u1} α m] (f : α -> ENNReal) (a : α), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a)) (fun (x : α) => f x)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (f a) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a)))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_singleton MeasureTheory.lintegral_singletonₓ'. -/
theorem lintegral_singleton [MeasurableSingletonClass α] (f : α → ℝ≥0∞) (a : α) :
    (∫⁻ x in {a}, f x ∂μ) = f a * μ {a} := by
  simp only [restrict_singleton, lintegral_smul_measure, lintegral_dirac, mul_comm]
#align measure_theory.lintegral_singleton MeasureTheory.lintegral_singleton

/- warning: measure_theory.lintegral_countable -> MeasureTheory.lintegral_countable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : MeasurableSingletonClass.{u1} α m] (f : α -> ENNReal) {s : Set.{u1} α}, (Set.Countable.{u1} α s) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (a : α) => f a)) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (fun (a : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) a)) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) a))))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : MeasurableSingletonClass.{u1} α m] (f : α -> ENNReal) {s : Set.{u1} α}, (Set.Countable.{u1} α s) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (a : α) => f a)) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal (Set.Elem.{u1} α s) (fun (a : Set.Elem.{u1} α s) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (f (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) a)) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) a))))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_countable MeasureTheory.lintegral_countableₓ'. -/
theorem lintegral_countable [MeasurableSingletonClass α] (f : α → ℝ≥0∞) {s : Set α}
    (hs : s.Countable) : (∫⁻ a in s, f a ∂μ) = ∑' a : s, f a * μ {(a : α)} :=
  calc
    (∫⁻ a in s, f a ∂μ) = ∫⁻ a in ⋃ x ∈ s, {x}, f a ∂μ := by rw [bUnion_of_singleton]
    _ = ∑' a : s, ∫⁻ x in {a}, f x ∂μ :=
      (lintegral_biUnion hs (fun _ _ => measurableSet_singleton _) (pairwise_disjoint_fiber id s) _)
    _ = ∑' a : s, f a * μ {(a : α)} := by simp only [lintegral_singleton]
    
#align measure_theory.lintegral_countable MeasureTheory.lintegral_countable

/- warning: measure_theory.lintegral_insert -> MeasureTheory.lintegral_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : MeasurableSingletonClass.{u1} α m] {a : α} {s : Set.{u1} α}, (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) -> (forall (f : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)) (fun (x : α) => f x)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f a) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => f x))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : MeasurableSingletonClass.{u1} α m] {a : α} {s : Set.{u1} α}, (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s)) -> (forall (f : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s)) (fun (x : α) => f x)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (f a) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => f x))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_insert MeasureTheory.lintegral_insertₓ'. -/
theorem lintegral_insert [MeasurableSingletonClass α] {a : α} {s : Set α} (h : a ∉ s)
    (f : α → ℝ≥0∞) : (∫⁻ x in insert a s, f x ∂μ) = f a * μ {a} + ∫⁻ x in s, f x ∂μ :=
  by
  rw [← union_singleton, lintegral_union (measurable_set_singleton a), lintegral_singleton,
    add_comm]
  rwa [disjoint_singleton_right]
#align measure_theory.lintegral_insert MeasureTheory.lintegral_insert

/- warning: measure_theory.lintegral_finset -> MeasureTheory.lintegral_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : MeasurableSingletonClass.{u1} α m] (s : Finset.{u1} α) (f : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) (fun (x : α) => f x)) (Finset.sum.{0, u1} ENNReal α (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) s (fun (x : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f x) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : MeasurableSingletonClass.{u1} α m] (s : Finset.{u1} α) (f : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (Finset.toSet.{u1} α s)) (fun (x : α) => f x)) (Finset.sum.{0, u1} ENNReal α (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) s (fun (x : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (f x) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_finset MeasureTheory.lintegral_finsetₓ'. -/
theorem lintegral_finset [MeasurableSingletonClass α] (s : Finset α) (f : α → ℝ≥0∞) :
    (∫⁻ x in s, f x ∂μ) = ∑ x in s, f x * μ {x} := by
  simp only [lintegral_countable _ s.countable_to_set, ← s.tsum_subtype']
#align measure_theory.lintegral_finset MeasureTheory.lintegral_finset

/- warning: measure_theory.lintegral_fintype -> MeasureTheory.lintegral_fintype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : MeasurableSingletonClass.{u1} α m] [_inst_2 : Fintype.{u1} α] (f : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (Finset.sum.{0, u1} ENNReal α (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) (Finset.univ.{u1} α _inst_2) (fun (x : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f x) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : MeasurableSingletonClass.{u1} α m] [_inst_2 : Fintype.{u1} α] (f : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (Finset.sum.{0, u1} ENNReal α (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) (Finset.univ.{u1} α _inst_2) (fun (x : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (f x) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_fintype MeasureTheory.lintegral_fintypeₓ'. -/
theorem lintegral_fintype [MeasurableSingletonClass α] [Fintype α] (f : α → ℝ≥0∞) :
    (∫⁻ x, f x ∂μ) = ∑ x, f x * μ {x} := by
  rw [← lintegral_finset, Finset.coe_univ, measure.restrict_univ]
#align measure_theory.lintegral_fintype MeasureTheory.lintegral_fintype

/- warning: measure_theory.lintegral_unique -> MeasureTheory.lintegral_unique is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : Unique.{succ u1} α] (f : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f (Inhabited.default.{succ u1} α (Unique.inhabited.{succ u1} α _inst_1))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (Set.univ.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : Unique.{succ u1} α] (f : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (f (Inhabited.default.{succ u1} α (Unique.instInhabited.{succ u1} α _inst_1))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) (Set.univ.{u1} α)))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_unique MeasureTheory.lintegral_uniqueₓ'. -/
theorem lintegral_unique [Unique α] (f : α → ℝ≥0∞) : (∫⁻ x, f x ∂μ) = f default * μ univ :=
  calc
    (∫⁻ x, f x ∂μ) = ∫⁻ x, f default ∂μ := lintegral_congr <| Unique.forall_iff.2 rfl
    _ = f default * μ univ := lintegral_const _
    
#align measure_theory.lintegral_unique MeasureTheory.lintegral_unique

end Countable

/- warning: measure_theory.ae_lt_top -> MeasureTheory.ae_lt_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Filter.Eventually.{u1} α (fun (x : α) => LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (f x) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (MeasureTheory.Measure.ae.{u1} α m μ))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Filter.Eventually.{u1} α (fun (x : α) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (f x) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (MeasureTheory.Measure.ae.{u1} α m μ))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_lt_top MeasureTheory.ae_lt_topₓ'. -/
theorem ae_lt_top {f : α → ℝ≥0∞} (hf : Measurable f) (h2f : (∫⁻ x, f x ∂μ) ≠ ∞) :
    ∀ᵐ x ∂μ, f x < ∞ := by
  simp_rw [ae_iff, ENNReal.not_lt_top]
  by_contra h
  apply h2f.lt_top.not_le
  have : (f ⁻¹' {∞}).indicator ⊤ ≤ f := by
    intro x
    by_cases hx : x ∈ f ⁻¹' {∞} <;> [simpa [hx] ;simp [hx]]
  convert lintegral_mono this
  rw [lintegral_indicator _ (hf (measurable_set_singleton ∞))]
  simp [ENNReal.top_mul', preimage, h]
#align measure_theory.ae_lt_top MeasureTheory.ae_lt_top

/- warning: measure_theory.ae_lt_top' -> MeasureTheory.ae_lt_top' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m f μ) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Filter.Eventually.{u1} α (fun (x : α) => LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (f x) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (MeasureTheory.Measure.ae.{u1} α m μ))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m f μ) -> (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Filter.Eventually.{u1} α (fun (x : α) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (f x) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (MeasureTheory.Measure.ae.{u1} α m μ))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_lt_top' MeasureTheory.ae_lt_top'ₓ'. -/
theorem ae_lt_top' {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (h2f : (∫⁻ x, f x ∂μ) ≠ ∞) :
    ∀ᵐ x ∂μ, f x < ∞ :=
  haveI h2f_meas : (∫⁻ x, hf.mk f x ∂μ) ≠ ∞ := by rwa [← lintegral_congr_ae hf.ae_eq_mk]
  (ae_lt_top hf.measurable_mk h2f_meas).mp (hf.ae_eq_mk.mono fun x hx h => by rwa [hx])
#align measure_theory.ae_lt_top' MeasureTheory.ae_lt_top'

/- warning: measure_theory.set_lintegral_lt_top_of_bdd_above -> MeasureTheory.set_lintegral_lt_top_of_bddAbove is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α}, (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (forall {f : α -> NNReal}, (Measurable.{u1, 0} α NNReal m NNReal.measurableSpace f) -> (BddAbove.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))) (Set.image.{u1, 0} α NNReal f s)) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (f x))) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {s : Set.{u1} α}, (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (forall {f : α -> NNReal}, (Measurable.{u1, 0} α NNReal m NNReal.measurableSpace f) -> (BddAbove.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) (Set.image.{u1, 0} α NNReal f s)) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => ENNReal.some (f x))) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.set_lintegral_lt_top_of_bdd_above MeasureTheory.set_lintegral_lt_top_of_bddAboveₓ'. -/
theorem set_lintegral_lt_top_of_bddAbove {s : Set α} (hs : μ s ≠ ∞) {f : α → ℝ≥0}
    (hf : Measurable f) (hbdd : BddAbove (f '' s)) : (∫⁻ x in s, f x ∂μ) < ∞ :=
  by
  obtain ⟨M, hM⟩ := hbdd
  rw [mem_upperBounds] at hM
  refine'
    lt_of_le_of_lt (set_lintegral_mono hf.coe_nnreal_ennreal (@measurable_const _ _ _ _ ↑M) _) _
  · simpa using hM
  · rw [lintegral_const]
    refine' ENNReal.mul_lt_top ennreal.coe_lt_top.ne _
    simp [hs]
#align measure_theory.set_lintegral_lt_top_of_bdd_above MeasureTheory.set_lintegral_lt_top_of_bddAbove

/- warning: measure_theory.set_lintegral_lt_top_of_is_compact -> MeasureTheory.set_lintegral_lt_top_of_isCompact is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OpensMeasurableSpace.{u1} α _inst_1 m] {s : Set.{u1} α}, (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (IsCompact.{u1} α _inst_1 s) -> (forall {f : α -> NNReal}, (Continuous.{u1, 0} α NNReal _inst_1 NNReal.topologicalSpace f) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (f x))) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OpensMeasurableSpace.{u1} α _inst_1 m] {s : Set.{u1} α}, (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (IsCompact.{u1} α _inst_1 s) -> (forall {f : α -> NNReal}, (Continuous.{u1, 0} α NNReal _inst_1 NNReal.instTopologicalSpaceNNReal f) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => ENNReal.some (f x))) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.set_lintegral_lt_top_of_is_compact MeasureTheory.set_lintegral_lt_top_of_isCompactₓ'. -/
theorem set_lintegral_lt_top_of_isCompact [TopologicalSpace α] [OpensMeasurableSpace α] {s : Set α}
    (hs : μ s ≠ ∞) (hsc : IsCompact s) {f : α → ℝ≥0} (hf : Continuous f) :
    (∫⁻ x in s, f x ∂μ) < ∞ :=
  set_lintegral_lt_top_of_bddAbove hs hf.Measurable (hsc.image hf).BddAbove
#align measure_theory.set_lintegral_lt_top_of_is_compact MeasureTheory.set_lintegral_lt_top_of_isCompact

/- warning: is_finite_measure.lintegral_lt_top_of_bounded_to_ennreal -> IsFiniteMeasure.lintegral_lt_top_of_bounded_to_eNNReal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (μ : MeasureTheory.Measure.{u1} α _inst_1) [μ_fin : MeasureTheory.FiniteMeasure.{u1} α _inst_1 μ] {f : α -> ENNReal}, (Exists.{1} NNReal (fun (c : NNReal) => forall (x : α), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (f x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) c))) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (μ : MeasureTheory.Measure.{u1} α _inst_1) [μ_fin : MeasureTheory.FiniteMeasure.{u1} α _inst_1 μ] {f : α -> ENNReal}, (Exists.{1} NNReal (fun (c : NNReal) => forall (x : α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (f x) (ENNReal.some c))) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (x : α) => f x)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align is_finite_measure.lintegral_lt_top_of_bounded_to_ennreal IsFiniteMeasure.lintegral_lt_top_of_bounded_to_eNNRealₓ'. -/
theorem IsFiniteMeasure.lintegral_lt_top_of_bounded_to_eNNReal {α : Type _} [MeasurableSpace α]
    (μ : Measure α) [μ_fin : FiniteMeasure μ] {f : α → ℝ≥0∞} (f_bdd : ∃ c : ℝ≥0, ∀ x, f x ≤ c) :
    (∫⁻ x, f x ∂μ) < ∞ := by
  cases' f_bdd with c hc
  apply lt_of_le_of_lt (@lintegral_mono _ _ μ _ _ hc)
  rw [lintegral_const]
  exact ENNReal.mul_lt_top ennreal.coe_lt_top.ne μ_fin.measure_univ_lt_top.ne
#align is_finite_measure.lintegral_lt_top_of_bounded_to_ennreal IsFiniteMeasure.lintegral_lt_top_of_bounded_to_eNNReal

#print MeasureTheory.Measure.withDensity /-
/-- Given a measure `μ : measure α` and a function `f : α → ℝ≥0∞`, `μ.with_density f` is the
measure such that for a measurable set `s` we have `μ.with_density f s = ∫⁻ a in s, f a ∂μ`. -/
def Measure.withDensity {m : MeasurableSpace α} (μ : Measure α) (f : α → ℝ≥0∞) : Measure α :=
  Measure.ofMeasurable (fun s hs => ∫⁻ a in s, f a ∂μ) (by simp) fun s hs hd =>
    lintegral_iUnion hs hd _
#align measure_theory.measure.with_density MeasureTheory.Measure.withDensity
-/

#print MeasureTheory.withDensity_apply /-
@[simp]
theorem withDensity_apply (f : α → ℝ≥0∞) {s : Set α} (hs : MeasurableSet s) :
    μ.withDensity f s = ∫⁻ a in s, f a ∂μ :=
  Measure.ofMeasurable_apply s hs
#align measure_theory.with_density_apply MeasureTheory.withDensity_apply
-/

#print MeasureTheory.withDensity_congr_ae /-
theorem withDensity_congr_ae {f g : α → ℝ≥0∞} (h : f =ᵐ[μ] g) : μ.withDensity f = μ.withDensity g :=
  by
  apply measure.ext fun s hs => _
  rw [with_density_apply _ hs, with_density_apply _ hs]
  exact lintegral_congr_ae (ae_restrict_of_ae h)
#align measure_theory.with_density_congr_ae MeasureTheory.withDensity_congr_ae
-/

#print MeasureTheory.withDensity_add_left /-
theorem withDensity_add_left {f : α → ℝ≥0∞} (hf : Measurable f) (g : α → ℝ≥0∞) :
    μ.withDensity (f + g) = μ.withDensity f + μ.withDensity g :=
  by
  refine' measure.ext fun s hs => _
  rw [with_density_apply _ hs, measure.add_apply, with_density_apply _ hs, with_density_apply _ hs,
    ← lintegral_add_left hf]
  rfl
#align measure_theory.with_density_add_left MeasureTheory.withDensity_add_left
-/

#print MeasureTheory.withDensity_add_right /-
theorem withDensity_add_right (f : α → ℝ≥0∞) {g : α → ℝ≥0∞} (hg : Measurable g) :
    μ.withDensity (f + g) = μ.withDensity f + μ.withDensity g := by
  simpa only [add_comm] using with_density_add_left hg f
#align measure_theory.with_density_add_right MeasureTheory.withDensity_add_right
-/

#print MeasureTheory.withDensity_add_measure /-
theorem withDensity_add_measure {m : MeasurableSpace α} (μ ν : Measure α) (f : α → ℝ≥0∞) :
    (μ + ν).withDensity f = μ.withDensity f + ν.withDensity f :=
  by
  ext1 s hs
  simp only [with_density_apply f hs, restrict_add, lintegral_add_measure, measure.add_apply]
#align measure_theory.with_density_add_measure MeasureTheory.withDensity_add_measure
-/

#print MeasureTheory.withDensity_sum /-
theorem withDensity_sum {ι : Type _} {m : MeasurableSpace α} (μ : ι → Measure α) (f : α → ℝ≥0∞) :
    (Sum μ).withDensity f = Sum fun n => (μ n).withDensity f :=
  by
  ext1 s hs
  simp_rw [sum_apply _ hs, with_density_apply f hs, restrict_sum μ hs, lintegral_sum_measure]
#align measure_theory.with_density_sum MeasureTheory.withDensity_sum
-/

#print MeasureTheory.withDensity_smul /-
theorem withDensity_smul (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : Measurable f) :
    μ.withDensity (r • f) = r • μ.withDensity f :=
  by
  refine' measure.ext fun s hs => _
  rw [with_density_apply _ hs, measure.coe_smul, Pi.smul_apply, with_density_apply _ hs,
    smul_eq_mul, ← lintegral_const_mul r hf]
  rfl
#align measure_theory.with_density_smul MeasureTheory.withDensity_smul
-/

/- warning: measure_theory.with_density_smul' -> MeasureTheory.withDensity_smul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (r : ENNReal) (f : α -> ENNReal), (Ne.{1} ENNReal r (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Eq.{succ u1} (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.withDensity.{u1} α m μ (SMul.smul.{0, u1} ENNReal (α -> ENNReal) (Function.hasSMul.{u1, 0, 0} α ENNReal ENNReal (Mul.toSMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) r f)) (SMul.smul.{0, u1} ENNReal (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.instSMul.{u1, 0} α ENNReal (SMulZeroClass.toHasSmul.{0, 0} ENNReal ENNReal (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (SMulWithZero.toSmulZeroClass.{0, 0} ENNReal ENNReal (MulZeroClass.toHasZero.{0} ENNReal (MulZeroOneClass.toMulZeroClass.{0} ENNReal (MonoidWithZero.toMulZeroOneClass.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))) (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (MulActionWithZero.toSMulWithZero.{0, 0} ENNReal ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (Module.toMulActionWithZero.{0, 0} ENNReal ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))) (Algebra.toModule.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) (IsScalarTower.right.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) m) r (MeasureTheory.Measure.withDensity.{u1} α m μ f)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (r : ENNReal) (f : α -> ENNReal), (Ne.{1} ENNReal r (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Eq.{succ u1} (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.withDensity.{u1} α m μ (HSMul.hSMul.{0, u1, u1} ENNReal (α -> ENNReal) (α -> ENNReal) (instHSMul.{0, u1} ENNReal (α -> ENNReal) (Pi.instSMul.{u1, 0, 0} α ENNReal (fun (a._@.Mathlib.MeasureTheory.Integral.Lebesgue._hyg.34021 : α) => ENNReal) (fun (i : α) => Algebra.toSMul.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))) r f)) (HSMul.hSMul.{0, u1, u1} ENNReal (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.{u1} α m) (instHSMul.{0, u1} ENNReal (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.instSMul.{u1, 0} α ENNReal (Algebra.toSMul.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (IsScalarTower.right.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) m)) r (MeasureTheory.Measure.withDensity.{u1} α m μ f)))
Case conversion may be inaccurate. Consider using '#align measure_theory.with_density_smul' MeasureTheory.withDensity_smul'ₓ'. -/
theorem withDensity_smul' (r : ℝ≥0∞) (f : α → ℝ≥0∞) (hr : r ≠ ∞) :
    μ.withDensity (r • f) = r • μ.withDensity f :=
  by
  refine' measure.ext fun s hs => _
  rw [with_density_apply _ hs, measure.coe_smul, Pi.smul_apply, with_density_apply _ hs,
    smul_eq_mul, ← lintegral_const_mul' r f hr]
  rfl
#align measure_theory.with_density_smul' MeasureTheory.withDensity_smul'

/- warning: measure_theory.is_finite_measure_with_density -> MeasureTheory.finiteMeasure_withDensity is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (MeasureTheory.FiniteMeasure.{u1} α m (MeasureTheory.Measure.withDensity.{u1} α m μ f))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (Ne.{1} ENNReal (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => f a)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (MeasureTheory.FiniteMeasure.{u1} α m (MeasureTheory.Measure.withDensity.{u1} α m μ f))
Case conversion may be inaccurate. Consider using '#align measure_theory.is_finite_measure_with_density MeasureTheory.finiteMeasure_withDensityₓ'. -/
theorem finiteMeasure_withDensity {f : α → ℝ≥0∞} (hf : (∫⁻ a, f a ∂μ) ≠ ∞) :
    FiniteMeasure (μ.withDensity f) :=
  {
    measure_univ_lt_top := by
      rwa [with_density_apply _ MeasurableSet.univ, measure.restrict_univ, lt_top_iff_ne_top] }
#align measure_theory.is_finite_measure_with_density MeasureTheory.finiteMeasure_withDensity

#print MeasureTheory.withDensity_absolutelyContinuous /-
theorem withDensity_absolutelyContinuous {m : MeasurableSpace α} (μ : Measure α) (f : α → ℝ≥0∞) :
    μ.withDensity f ≪ μ :=
  by
  refine' absolutely_continuous.mk fun s hs₁ hs₂ => _
  rw [with_density_apply _ hs₁]
  exact set_lintegral_measure_zero _ _ hs₂
#align measure_theory.with_density_absolutely_continuous MeasureTheory.withDensity_absolutelyContinuous
-/

#print MeasureTheory.withDensity_zero /-
@[simp]
theorem withDensity_zero : μ.withDensity 0 = 0 :=
  by
  ext1 s hs
  simp [with_density_apply _ hs]
#align measure_theory.with_density_zero MeasureTheory.withDensity_zero
-/

#print MeasureTheory.withDensity_one /-
@[simp]
theorem withDensity_one : μ.withDensity 1 = μ :=
  by
  ext1 s hs
  simp [with_density_apply _ hs]
#align measure_theory.with_density_one MeasureTheory.withDensity_one
-/

#print MeasureTheory.withDensity_tsum /-
theorem withDensity_tsum {f : ℕ → α → ℝ≥0∞} (h : ∀ i, Measurable (f i)) :
    μ.withDensity (∑' n, f n) = Sum fun n => μ.withDensity (f n) :=
  by
  ext1 s hs
  simp_rw [sum_apply _ hs, with_density_apply _ hs]
  change (∫⁻ x in s, (∑' n, f n) x ∂μ) = ∑' i : ℕ, ∫⁻ x, f i x ∂μ.restrict s
  rw [← lintegral_tsum fun i => (h i).AEMeasurable]
  refine' lintegral_congr fun x => tsum_apply (Pi.summable.2 fun _ => ENNReal.summable)
#align measure_theory.with_density_tsum MeasureTheory.withDensity_tsum
-/

#print MeasureTheory.withDensity_indicator /-
theorem withDensity_indicator {s : Set α} (hs : MeasurableSet s) (f : α → ℝ≥0∞) :
    μ.withDensity (s.indicator f) = (μ.restrict s).withDensity f :=
  by
  ext1 t ht
  rw [with_density_apply _ ht, lintegral_indicator _ hs, restrict_comm hs, ←
    with_density_apply _ ht]
#align measure_theory.with_density_indicator MeasureTheory.withDensity_indicator
-/

#print MeasureTheory.withDensity_indicator_one /-
theorem withDensity_indicator_one {s : Set α} (hs : MeasurableSet s) :
    μ.withDensity (s.indicator 1) = μ.restrict s := by
  rw [with_density_indicator hs, with_density_one]
#align measure_theory.with_density_indicator_one MeasureTheory.withDensity_indicator_one
-/

#print MeasureTheory.withDensity_ofReal_mutuallySingular /-
theorem withDensity_ofReal_mutuallySingular {f : α → ℝ} (hf : Measurable f) :
    (μ.withDensity fun x => ENNReal.ofReal <| f x) ⟂ₘ
      μ.withDensity fun x => ENNReal.ofReal <| -f x :=
  by
  set S : Set α := { x | f x < 0 } with hSdef
  have hS : MeasurableSet S := measurableSet_lt hf measurable_const
  refine' ⟨S, hS, _, _⟩
  · rw [with_density_apply _ hS, lintegral_eq_zero_iff hf.ennreal_of_real, eventually_eq]
    exact (ae_restrict_mem hS).mono fun x hx => ENNReal.ofReal_eq_zero.2 (le_of_lt hx)
  · rw [with_density_apply _ hS.compl, lintegral_eq_zero_iff hf.neg.ennreal_of_real, eventually_eq]
    exact
      (ae_restrict_mem hS.compl).mono fun x hx =>
        ENNReal.ofReal_eq_zero.2 (not_lt.1 <| mt neg_pos.1 hx)
#align measure_theory.with_density_of_real_mutually_singular MeasureTheory.withDensity_ofReal_mutuallySingular
-/

#print MeasureTheory.restrict_withDensity /-
theorem restrict_withDensity {s : Set α} (hs : MeasurableSet s) (f : α → ℝ≥0∞) :
    (μ.withDensity f).restrict s = (μ.restrict s).withDensity f :=
  by
  ext1 t ht
  rw [restrict_apply ht, with_density_apply _ ht, with_density_apply _ (ht.inter hs),
    restrict_restrict ht]
#align measure_theory.restrict_with_density MeasureTheory.restrict_withDensity
-/

/- warning: measure_theory.with_density_eq_zero -> MeasureTheory.withDensity_eq_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m f μ) -> (Eq.{succ u1} (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.withDensity.{u1} α m μ f) (OfNat.ofNat.{u1} (MeasureTheory.Measure.{u1} α m) 0 (OfNat.mk.{u1} (MeasureTheory.Measure.{u1} α m) 0 (Zero.zero.{u1} (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.instZero.{u1} α m))))) -> (Filter.EventuallyEq.{u1, 0} α ENNReal (MeasureTheory.Measure.ae.{u1} α m μ) f (OfNat.ofNat.{u1} (α -> ENNReal) 0 (OfNat.mk.{u1} (α -> ENNReal) 0 (Zero.zero.{u1} (α -> ENNReal) (Pi.instZero.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => ENNReal.hasZero))))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m f μ) -> (Eq.{succ u1} (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.withDensity.{u1} α m μ f) (OfNat.ofNat.{u1} (MeasureTheory.Measure.{u1} α m) 0 (Zero.toOfNat0.{u1} (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.instZero.{u1} α m)))) -> (Filter.EventuallyEq.{u1, 0} α ENNReal (MeasureTheory.Measure.ae.{u1} α m μ) f (OfNat.ofNat.{u1} (α -> ENNReal) 0 (Zero.toOfNat0.{u1} (α -> ENNReal) (Pi.instZero.{u1, 0} α (fun (a._@.Mathlib.Order.Filter.Basic._hyg.19136 : α) => ENNReal) (fun (i : α) => instENNRealZero)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.with_density_eq_zero MeasureTheory.withDensity_eq_zeroₓ'. -/
theorem withDensity_eq_zero {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (h : μ.withDensity f = 0) :
    f =ᵐ[μ] 0 := by
  rw [← lintegral_eq_zero_iff' hf, ← set_lintegral_univ, ← with_density_apply _ MeasurableSet.univ,
    h, measure.coe_zero, Pi.zero_apply]
#align measure_theory.with_density_eq_zero MeasureTheory.withDensity_eq_zero

/- warning: measure_theory.with_density_apply_eq_zero -> MeasureTheory.withDensity_apply_eq_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal} {s : Set.{u1} α}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (Iff (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) (MeasureTheory.Measure.withDensity.{u1} α m μ f) s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (setOf.{u1} α (fun (x : α) => Ne.{1} ENNReal (f x) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))) s)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal} {s : Set.{u1} α}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (Iff (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m (MeasureTheory.Measure.withDensity.{u1} α m μ f)) s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (setOf.{u1} α (fun (x : α) => Ne.{1} ENNReal (f x) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))) s)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))))
Case conversion may be inaccurate. Consider using '#align measure_theory.with_density_apply_eq_zero MeasureTheory.withDensity_apply_eq_zeroₓ'. -/
theorem withDensity_apply_eq_zero {f : α → ℝ≥0∞} {s : Set α} (hf : Measurable f) :
    μ.withDensity f s = 0 ↔ μ ({ x | f x ≠ 0 } ∩ s) = 0 :=
  by
  constructor
  · intro hs
    let t := to_measurable (μ.with_density f) s
    apply measure_mono_null (inter_subset_inter_right _ (subset_to_measurable (μ.with_density f) s))
    have A : μ.with_density f t = 0 := by rw [measure_to_measurable, hs]
    rw [with_density_apply f (measurable_set_to_measurable _ s), lintegral_eq_zero_iff hf,
      eventually_eq, ae_restrict_iff, ae_iff] at A
    swap
    · exact hf (measurable_set_singleton 0)
    simp only [Pi.zero_apply, mem_set_of_eq, Filter.mem_mk] at A
    convert A
    ext x
    simp only [and_comm', exists_prop, mem_inter_iff, iff_self_iff, mem_set_of_eq, mem_compl_iff,
      not_forall]
  · intro hs
    let t := to_measurable μ ({ x | f x ≠ 0 } ∩ s)
    have A : s ⊆ t ∪ { x | f x = 0 } := by
      intro x hx
      rcases eq_or_ne (f x) 0 with (fx | fx)
      · simp only [fx, mem_union, mem_set_of_eq, eq_self_iff_true, or_true_iff]
      · left
        apply subset_to_measurable _ _
        exact ⟨fx, hx⟩
    apply measure_mono_null A (measure_union_null _ _)
    · apply with_density_absolutely_continuous
      rwa [measure_to_measurable]
    · have M : MeasurableSet { x : α | f x = 0 } := hf (measurable_set_singleton _)
      rw [with_density_apply _ M, lintegral_eq_zero_iff hf]
      filter_upwards [ae_restrict_mem M]
      simp only [imp_self, Pi.zero_apply, imp_true_iff]
#align measure_theory.with_density_apply_eq_zero MeasureTheory.withDensity_apply_eq_zero

/- warning: measure_theory.ae_with_density_iff -> MeasureTheory.ae_withDensity_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {p : α -> Prop} {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (Iff (Filter.Eventually.{u1} α (fun (x : α) => p x) (MeasureTheory.Measure.ae.{u1} α m (MeasureTheory.Measure.withDensity.{u1} α m μ f))) (Filter.Eventually.{u1} α (fun (x : α) => (Ne.{1} ENNReal (f x) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (p x)) (MeasureTheory.Measure.ae.{u1} α m μ)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {p : α -> Prop} {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (Iff (Filter.Eventually.{u1} α (fun (x : α) => p x) (MeasureTheory.Measure.ae.{u1} α m (MeasureTheory.Measure.withDensity.{u1} α m μ f))) (Filter.Eventually.{u1} α (fun (x : α) => (Ne.{1} ENNReal (f x) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (p x)) (MeasureTheory.Measure.ae.{u1} α m μ)))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_with_density_iff MeasureTheory.ae_withDensity_iffₓ'. -/
theorem ae_withDensity_iff {p : α → Prop} {f : α → ℝ≥0∞} (hf : Measurable f) :
    (∀ᵐ x ∂μ.withDensity f, p x) ↔ ∀ᵐ x ∂μ, f x ≠ 0 → p x :=
  by
  rw [ae_iff, ae_iff, with_density_apply_eq_zero hf]
  congr
  ext x
  simp only [exists_prop, mem_inter_iff, iff_self_iff, mem_set_of_eq, not_forall]
#align measure_theory.ae_with_density_iff MeasureTheory.ae_withDensity_iff

#print MeasureTheory.ae_withDensity_iff_ae_restrict /-
theorem ae_withDensity_iff_ae_restrict {p : α → Prop} {f : α → ℝ≥0∞} (hf : Measurable f) :
    (∀ᵐ x ∂μ.withDensity f, p x) ↔ ∀ᵐ x ∂μ.restrict { x | f x ≠ 0 }, p x :=
  by
  rw [ae_with_density_iff hf, ae_restrict_iff']
  · rfl
  · exact hf (measurable_set_singleton 0).compl
#align measure_theory.ae_with_density_iff_ae_restrict MeasureTheory.ae_withDensity_iff_ae_restrict
-/

/- warning: measure_theory.ae_measurable_with_density_ennreal_iff -> MeasureTheory.aemeasurable_withDensity_ennreal_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> NNReal}, (Measurable.{u1, 0} α NNReal m NNReal.measurableSpace f) -> (forall {g : α -> ENNReal}, Iff (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m g (MeasureTheory.Measure.withDensity.{u1} α m μ (fun (x : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (f x)))) (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m (fun (x : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (f x)) (g x)) μ))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> NNReal}, (Measurable.{u1, 0} α NNReal m NNReal.measurableSpace f) -> (forall {g : α -> ENNReal}, Iff (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m g (MeasureTheory.Measure.withDensity.{u1} α m μ (fun (x : α) => ENNReal.some (f x)))) (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m (fun (x : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (ENNReal.some (f x)) (g x)) μ))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_measurable_with_density_ennreal_iff MeasureTheory.aemeasurable_withDensity_ennreal_iffₓ'. -/
theorem aemeasurable_withDensity_ennreal_iff {f : α → ℝ≥0} (hf : Measurable f) {g : α → ℝ≥0∞} :
    AEMeasurable g (μ.withDensity fun x => (f x : ℝ≥0∞)) ↔
      AEMeasurable (fun x => (f x : ℝ≥0∞) * g x) μ :=
  by
  constructor
  · rintro ⟨g', g'meas, hg'⟩
    have A : MeasurableSet { x : α | f x ≠ 0 } := (hf (measurable_set_singleton 0)).compl
    refine' ⟨fun x => f x * g' x, hf.coe_nnreal_ennreal.smul g'meas, _⟩
    apply ae_of_ae_restrict_of_ae_restrict_compl { x | f x ≠ 0 }
    · rw [eventually_eq, ae_with_density_iff hf.coe_nnreal_ennreal] at hg'
      rw [ae_restrict_iff' A]
      filter_upwards [hg']
      intro a ha h'a
      have : (f a : ℝ≥0∞) ≠ 0 := by simpa only [Ne.def, coe_eq_zero] using h'a
      rw [ha this]
    · filter_upwards [ae_restrict_mem A.compl]
      intro x hx
      simp only [Classical.not_not, mem_set_of_eq, mem_compl_iff] at hx
      simp [hx]
  · rintro ⟨g', g'meas, hg'⟩
    refine' ⟨fun x => (f x)⁻¹ * g' x, hf.coe_nnreal_ennreal.inv.smul g'meas, _⟩
    rw [eventually_eq, ae_with_density_iff hf.coe_nnreal_ennreal]
    filter_upwards [hg']
    intro x hx h'x
    rw [← hx, ← mul_assoc, ENNReal.inv_mul_cancel h'x ENNReal.coe_ne_top, one_mul]
#align measure_theory.ae_measurable_with_density_ennreal_iff MeasureTheory.aemeasurable_withDensity_ennreal_iff

end Lintegral

open MeasureTheory.SimpleFunc

variable {m m0 : MeasurableSpace α}

include m

/- warning: measure_theory.lintegral_with_density_eq_lintegral_mul -> MeasureTheory.lintegral_withDensity_eq_lintegral_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} (μ : MeasureTheory.Measure.{u1} α m) {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (forall {g : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace g) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.withDensity.{u1} α m μ f) (fun (a : α) => g a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HMul.hMul.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHMul.{u1} (α -> ENNReal) (Pi.instMul.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) f g a))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} (μ : MeasureTheory.Measure.{u1} α m) {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (forall {g : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace g) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.withDensity.{u1} α m μ f) (fun (a : α) => g a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HMul.hMul.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHMul.{u1} (α -> ENNReal) (Pi.instMul.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) f g a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_with_density_eq_lintegral_mul MeasureTheory.lintegral_withDensity_eq_lintegral_mulₓ'. -/
/-- This is Exercise 1.2.1 from [tao2010]. It allows you to express integration of a measurable
function with respect to `(μ.with_density f)` as an integral with respect to `μ`, called the base
measure. `μ` is often the Lebesgue measure, and in this circumstance `f` is the probability density
function, and `(μ.with_density f)` represents any continuous random variable as a
probability measure, such as the uniform distribution between 0 and 1, the Gaussian distribution,
the exponential distribution, the Beta distribution, or the Cauchy distribution (see Section 2.4
of [wasserman2004]). Thus, this method shows how to one can calculate expectations, variances,
and other moments as a function of the probability density function.
 -/
theorem lintegral_withDensity_eq_lintegral_mul (μ : Measure α) {f : α → ℝ≥0∞}
    (h_mf : Measurable f) :
    ∀ {g : α → ℝ≥0∞}, Measurable g → (∫⁻ a, g a ∂μ.withDensity f) = ∫⁻ a, (f * g) a ∂μ :=
  by
  apply Measurable.ennreal_induction
  · intro c s h_ms
    simp [*, mul_comm _ c, ← indicator_mul_right]
  · intro g h h_univ h_mea_g h_mea_h h_ind_g h_ind_h
    simp [mul_add, *, Measurable.mul]
  · intro g h_mea_g h_mono_g h_ind
    have : Monotone fun n a => f a * g n a := fun m n hmn x => mul_le_mul_left' (h_mono_g hmn x) _
    simp [lintegral_supr, ENNReal.mul_iSup, h_mf.mul (h_mea_g _), *]
#align measure_theory.lintegral_with_density_eq_lintegral_mul MeasureTheory.lintegral_withDensity_eq_lintegral_mul

/- warning: measure_theory.set_lintegral_with_density_eq_set_lintegral_mul -> MeasureTheory.set_lintegral_withDensity_eq_set_lintegral_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} (μ : MeasureTheory.Measure.{u1} α m) {f : α -> ENNReal} {g : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace g) -> (forall {s : Set.{u1} α}, (MeasurableSet.{u1} α m s) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m (MeasureTheory.Measure.withDensity.{u1} α m μ f) s) (fun (x : α) => g x)) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => HMul.hMul.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHMul.{u1} (α -> ENNReal) (Pi.instMul.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) f g x))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} (μ : MeasureTheory.Measure.{u1} α m) {f : α -> ENNReal} {g : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace g) -> (forall {s : Set.{u1} α}, (MeasurableSet.{u1} α m s) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m (MeasureTheory.Measure.withDensity.{u1} α m μ f) s) (fun (x : α) => g x)) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ s) (fun (x : α) => HMul.hMul.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHMul.{u1} (α -> ENNReal) (Pi.instMul.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) f g x))))
Case conversion may be inaccurate. Consider using '#align measure_theory.set_lintegral_with_density_eq_set_lintegral_mul MeasureTheory.set_lintegral_withDensity_eq_set_lintegral_mulₓ'. -/
theorem set_lintegral_withDensity_eq_set_lintegral_mul (μ : Measure α) {f g : α → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) {s : Set α} (hs : MeasurableSet s) :
    (∫⁻ x in s, g x ∂μ.withDensity f) = ∫⁻ x in s, (f * g) x ∂μ := by
  rw [restrict_with_density hs, lintegral_with_density_eq_lintegral_mul _ hf hg]
#align measure_theory.set_lintegral_with_density_eq_set_lintegral_mul MeasureTheory.set_lintegral_withDensity_eq_set_lintegral_mul

/- warning: measure_theory.lintegral_with_density_eq_lintegral_mul₀' -> MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m f μ) -> (forall {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m g (MeasureTheory.Measure.withDensity.{u1} α m μ f)) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.withDensity.{u1} α m μ f) (fun (a : α) => g a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HMul.hMul.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHMul.{u1} (α -> ENNReal) (Pi.instMul.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) f g a))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m f μ) -> (forall {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m g (MeasureTheory.Measure.withDensity.{u1} α m μ f)) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.withDensity.{u1} α m μ f) (fun (a : α) => g a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HMul.hMul.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHMul.{u1} (α -> ENNReal) (Pi.instMul.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) f g a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_with_density_eq_lintegral_mul₀' MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀'ₓ'. -/
/-- The Lebesgue integral of `g` with respect to the measure `μ.with_density f` coincides with
the integral of `f * g`. This version assumes that `g` is almost everywhere measurable. For a
version without conditions on `g` but requiring that `f` is almost everywhere finite, see
`lintegral_with_density_eq_lintegral_mul_non_measurable` -/
theorem lintegral_withDensity_eq_lintegral_mul₀' {μ : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) {g : α → ℝ≥0∞} (hg : AEMeasurable g (μ.withDensity f)) :
    (∫⁻ a, g a ∂μ.withDensity f) = ∫⁻ a, (f * g) a ∂μ :=
  by
  let f' := hf.mk f
  have : μ.with_density f = μ.with_density f' := with_density_congr_ae hf.ae_eq_mk
  rw [this] at hg⊢
  let g' := hg.mk g
  calc
    (∫⁻ a, g a ∂μ.with_density f') = ∫⁻ a, g' a ∂μ.with_density f' := lintegral_congr_ae hg.ae_eq_mk
    _ = ∫⁻ a, (f' * g') a ∂μ :=
      (lintegral_with_density_eq_lintegral_mul _ hf.measurable_mk hg.measurable_mk)
    _ = ∫⁻ a, (f' * g) a ∂μ := by
      apply lintegral_congr_ae
      apply ae_of_ae_restrict_of_ae_restrict_compl { x | f' x ≠ 0 }
      · have Z := hg.ae_eq_mk
        rw [eventually_eq, ae_with_density_iff_ae_restrict hf.measurable_mk] at Z
        filter_upwards [Z]
        intro x hx
        simp only [hx, Pi.mul_apply]
      · have M : MeasurableSet ({ x : α | f' x ≠ 0 }ᶜ) :=
          (hf.measurable_mk (measurable_set_singleton 0).compl).compl
        filter_upwards [ae_restrict_mem M]
        intro x hx
        simp only [Classical.not_not, mem_set_of_eq, mem_compl_iff] at hx
        simp only [hx, MulZeroClass.zero_mul, Pi.mul_apply]
    _ = ∫⁻ a : α, (f * g) a ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hf.ae_eq_mk]
      intro x hx
      simp only [hx, Pi.mul_apply]
    
#align measure_theory.lintegral_with_density_eq_lintegral_mul₀' MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀'

/- warning: measure_theory.lintegral_with_density_eq_lintegral_mul₀ -> MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m f μ) -> (forall {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m g μ) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.withDensity.{u1} α m μ f) (fun (a : α) => g a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HMul.hMul.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHMul.{u1} (α -> ENNReal) (Pi.instMul.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) f g a))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m f μ) -> (forall {g : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m g μ) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.withDensity.{u1} α m μ f) (fun (a : α) => g a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HMul.hMul.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHMul.{u1} (α -> ENNReal) (Pi.instMul.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) f g a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_with_density_eq_lintegral_mul₀ MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀ₓ'. -/
theorem lintegral_withDensity_eq_lintegral_mul₀ {μ : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) {g : α → ℝ≥0∞} (hg : AEMeasurable g μ) :
    (∫⁻ a, g a ∂μ.withDensity f) = ∫⁻ a, (f * g) a ∂μ :=
  lintegral_withDensity_eq_lintegral_mul₀' hf (hg.mono' (withDensity_absolutelyContinuous μ f))
#align measure_theory.lintegral_with_density_eq_lintegral_mul₀ MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀

/- warning: measure_theory.lintegral_with_density_le_lintegral_mul -> MeasureTheory.lintegral_withDensity_le_lintegral_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} (μ : MeasureTheory.Measure.{u1} α m) {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (forall (g : α -> ENNReal), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.withDensity.{u1} α m μ f) (fun (a : α) => g a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HMul.hMul.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHMul.{u1} (α -> ENNReal) (Pi.instMul.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) f g a)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} (μ : MeasureTheory.Measure.{u1} α m) {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (forall (g : α -> ENNReal), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.withDensity.{u1} α m μ f) (fun (a : α) => g a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HMul.hMul.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHMul.{u1} (α -> ENNReal) (Pi.instMul.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) f g a)))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_with_density_le_lintegral_mul MeasureTheory.lintegral_withDensity_le_lintegral_mulₓ'. -/
theorem lintegral_withDensity_le_lintegral_mul (μ : Measure α) {f : α → ℝ≥0∞}
    (f_meas : Measurable f) (g : α → ℝ≥0∞) : (∫⁻ a, g a ∂μ.withDensity f) ≤ ∫⁻ a, (f * g) a ∂μ :=
  by
  rw [← supr_lintegral_measurable_le_eq_lintegral, ← supr_lintegral_measurable_le_eq_lintegral]
  refine' iSup₂_le fun i i_meas => iSup_le fun hi => _
  have A : f * i ≤ f * g := fun x => mul_le_mul_left' (hi x) _
  refine' le_iSup₂_of_le (f * i) (f_meas.mul i_meas) _
  exact le_iSup_of_le A (le_of_eq (lintegral_with_density_eq_lintegral_mul _ f_meas i_meas))
#align measure_theory.lintegral_with_density_le_lintegral_mul MeasureTheory.lintegral_withDensity_le_lintegral_mul

/- warning: measure_theory.lintegral_with_density_eq_lintegral_mul_non_measurable -> MeasureTheory.lintegral_withDensity_eq_lintegral_mul_non_measurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} (μ : MeasureTheory.Measure.{u1} α m) {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (Filter.Eventually.{u1} α (fun (x : α) => LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (f x) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (forall (g : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.withDensity.{u1} α m μ f) (fun (a : α) => g a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HMul.hMul.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHMul.{u1} (α -> ENNReal) (Pi.instMul.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) f g a)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} (μ : MeasureTheory.Measure.{u1} α m) {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace f) -> (Filter.Eventually.{u1} α (fun (x : α) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (f x) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (forall (g : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.withDensity.{u1} α m μ f) (fun (a : α) => g a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HMul.hMul.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHMul.{u1} (α -> ENNReal) (Pi.instMul.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) f g a)))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_with_density_eq_lintegral_mul_non_measurable MeasureTheory.lintegral_withDensity_eq_lintegral_mul_non_measurableₓ'. -/
theorem lintegral_withDensity_eq_lintegral_mul_non_measurable (μ : Measure α) {f : α → ℝ≥0∞}
    (f_meas : Measurable f) (hf : ∀ᵐ x ∂μ, f x < ∞) (g : α → ℝ≥0∞) :
    (∫⁻ a, g a ∂μ.withDensity f) = ∫⁻ a, (f * g) a ∂μ :=
  by
  refine' le_antisymm (lintegral_with_density_le_lintegral_mul μ f_meas g) _
  rw [← supr_lintegral_measurable_le_eq_lintegral, ← supr_lintegral_measurable_le_eq_lintegral]
  refine' iSup₂_le fun i i_meas => iSup_le fun hi => _
  have A : (fun x => (f x)⁻¹ * i x) ≤ g := by
    intro x
    dsimp
    rw [mul_comm, ← div_eq_mul_inv]
    exact div_le_of_le_mul' (hi x)
  refine' le_iSup_of_le (fun x => (f x)⁻¹ * i x) (le_iSup_of_le (f_meas.inv.mul i_meas) _)
  refine' le_iSup_of_le A _
  rw [lintegral_with_density_eq_lintegral_mul _ f_meas (f_meas.inv.mul i_meas)]
  apply lintegral_mono_ae
  filter_upwards [hf]
  intro x h'x
  rcases eq_or_ne (f x) 0 with (hx | hx)
  · have := hi x
    simp only [hx, MulZeroClass.zero_mul, Pi.mul_apply, nonpos_iff_eq_zero] at this
    simp [this]
  · apply le_of_eq _
    dsimp
    rw [← mul_assoc, ENNReal.mul_inv_cancel hx h'x.ne, one_mul]
#align measure_theory.lintegral_with_density_eq_lintegral_mul_non_measurable MeasureTheory.lintegral_withDensity_eq_lintegral_mul_non_measurable

#print MeasureTheory.set_lintegral_withDensity_eq_set_lintegral_mul_non_measurable /-
theorem set_lintegral_withDensity_eq_set_lintegral_mul_non_measurable (μ : Measure α) {f : α → ℝ≥0∞}
    (f_meas : Measurable f) (g : α → ℝ≥0∞) {s : Set α} (hs : MeasurableSet s)
    (hf : ∀ᵐ x ∂μ.restrict s, f x < ∞) :
    (∫⁻ a in s, g a ∂μ.withDensity f) = ∫⁻ a in s, (f * g) a ∂μ := by
  rw [restrict_with_density hs, lintegral_with_density_eq_lintegral_mul_non_measurable _ f_meas hf]
#align measure_theory.set_lintegral_with_density_eq_set_lintegral_mul_non_measurable MeasureTheory.set_lintegral_withDensity_eq_set_lintegral_mul_non_measurable
-/

/- warning: measure_theory.lintegral_with_density_eq_lintegral_mul_non_measurable₀ -> MeasureTheory.lintegral_withDensity_eq_lintegral_mul_non_measurable₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} (μ : MeasureTheory.Measure.{u1} α m) {f : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m f μ) -> (Filter.Eventually.{u1} α (fun (x : α) => LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (f x) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (forall (g : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.withDensity.{u1} α m μ f) (fun (a : α) => g a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HMul.hMul.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHMul.{u1} (α -> ENNReal) (Pi.instMul.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) f g a)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} (μ : MeasureTheory.Measure.{u1} α m) {f : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m f μ) -> (Filter.Eventually.{u1} α (fun (x : α) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (f x) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (forall (g : α -> ENNReal), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α m (MeasureTheory.Measure.withDensity.{u1} α m μ f) (fun (a : α) => g a)) (MeasureTheory.lintegral.{u1} α m μ (fun (a : α) => HMul.hMul.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHMul.{u1} (α -> ENNReal) (Pi.instMul.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) f g a)))
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_with_density_eq_lintegral_mul_non_measurable₀ MeasureTheory.lintegral_withDensity_eq_lintegral_mul_non_measurable₀ₓ'. -/
theorem lintegral_withDensity_eq_lintegral_mul_non_measurable₀ (μ : Measure α) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (h'f : ∀ᵐ x ∂μ, f x < ∞) (g : α → ℝ≥0∞) :
    (∫⁻ a, g a ∂μ.withDensity f) = ∫⁻ a, (f * g) a ∂μ :=
  by
  let f' := hf.mk f
  calc
    (∫⁻ a, g a ∂μ.with_density f) = ∫⁻ a, g a ∂μ.with_density f' := by
      rw [with_density_congr_ae hf.ae_eq_mk]
    _ = ∫⁻ a, (f' * g) a ∂μ :=
      by
      apply lintegral_with_density_eq_lintegral_mul_non_measurable _ hf.measurable_mk
      filter_upwards [h'f, hf.ae_eq_mk]
      intro x hx h'x
      rwa [← h'x]
    _ = ∫⁻ a, (f * g) a ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hf.ae_eq_mk]
      intro x hx
      simp only [hx, Pi.mul_apply]
    
#align measure_theory.lintegral_with_density_eq_lintegral_mul_non_measurable₀ MeasureTheory.lintegral_withDensity_eq_lintegral_mul_non_measurable₀

#print MeasureTheory.set_lintegral_withDensity_eq_set_lintegral_mul_non_measurable₀ /-
theorem set_lintegral_withDensity_eq_set_lintegral_mul_non_measurable₀ (μ : Measure α)
    {f : α → ℝ≥0∞} {s : Set α} (hf : AEMeasurable f (μ.restrict s)) (g : α → ℝ≥0∞)
    (hs : MeasurableSet s) (h'f : ∀ᵐ x ∂μ.restrict s, f x < ∞) :
    (∫⁻ a in s, g a ∂μ.withDensity f) = ∫⁻ a in s, (f * g) a ∂μ := by
  rw [restrict_with_density hs, lintegral_with_density_eq_lintegral_mul_non_measurable₀ _ hf h'f]
#align measure_theory.set_lintegral_with_density_eq_set_lintegral_mul_non_measurable₀ MeasureTheory.set_lintegral_withDensity_eq_set_lintegral_mul_non_measurable₀
-/

#print MeasureTheory.withDensity_mul /-
theorem withDensity_mul (μ : Measure α) {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    μ.withDensity (f * g) = (μ.withDensity f).withDensity g :=
  by
  ext1 s hs
  simp [with_density_apply _ hs, restrict_with_density hs,
    lintegral_with_density_eq_lintegral_mul _ hf hg]
#align measure_theory.with_density_mul MeasureTheory.withDensity_mul
-/

/- warning: measure_theory.exists_pos_lintegral_lt_of_sigma_finite -> MeasureTheory.exists_pos_lintegral_lt_of_sigmaFinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} (μ : MeasureTheory.Measure.{u1} α m) [_inst_1 : MeasureTheory.SigmaFinite.{u1} α m μ] {ε : ENNReal}, (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{succ u1} (α -> NNReal) (fun (g : α -> NNReal) => And (forall (x : α), LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) (g x)) (And (Measurable.{u1, 0} α NNReal m NNReal.measurableSpace g) (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (g x))) ε))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} (μ : MeasureTheory.Measure.{u1} α m) [_inst_1 : MeasureTheory.SigmaFinite.{u1} α m μ] {ε : ENNReal}, (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{succ u1} (α -> NNReal) (fun (g : α -> NNReal) => And (forall (x : α), LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) (g x)) (And (Measurable.{u1, 0} α NNReal m NNReal.measurableSpace g) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => ENNReal.some (g x))) ε))))
Case conversion may be inaccurate. Consider using '#align measure_theory.exists_pos_lintegral_lt_of_sigma_finite MeasureTheory.exists_pos_lintegral_lt_of_sigmaFiniteₓ'. -/
/-- In a sigma-finite measure space, there exists an integrable function which is
positive everywhere (and with an arbitrarily small integral). -/
theorem exists_pos_lintegral_lt_of_sigmaFinite (μ : Measure α) [SigmaFinite μ] {ε : ℝ≥0∞}
    (ε0 : ε ≠ 0) : ∃ g : α → ℝ≥0, (∀ x, 0 < g x) ∧ Measurable g ∧ (∫⁻ x, g x ∂μ) < ε :=
  by
  /- Let `s` be a covering of `α` by pairwise disjoint measurable sets of finite measure. Let
    `δ : ℕ → ℝ≥0` be a positive function such that `∑' i, μ (s i) * δ i < ε`. Then the function that
     is equal to `δ n` on `s n` is a positive function with integral less than `ε`. -/
  set s : ℕ → Set α := disjointed (spanning_sets μ)
  have : ∀ n, μ (s n) < ∞ := fun n =>
    (measure_mono <| disjointed_subset _ _).trans_lt (measure_spanning_sets_lt_top μ n)
  obtain ⟨δ, δpos, δsum⟩ : ∃ δ : ℕ → ℝ≥0, (∀ i, 0 < δ i) ∧ (∑' i, μ (s i) * δ i) < ε
  exact ENNReal.exists_pos_tsum_mul_lt_of_countable ε0 _ fun n => (this n).Ne
  set N : α → ℕ := spanning_sets_index μ
  have hN_meas : Measurable N := measurable_spanning_sets_index μ
  have hNs : ∀ n, N ⁻¹' {n} = s n := preimage_spanning_sets_index_singleton μ
  refine' ⟨δ ∘ N, fun x => δpos _, measurable_from_nat.comp hN_meas, _⟩
  simpa [lintegral_comp measurable_from_nat.coe_nnreal_ennreal hN_meas, hNs, lintegral_countable',
    measurable_spanning_sets_index, mul_comm] using δsum
#align measure_theory.exists_pos_lintegral_lt_of_sigma_finite MeasureTheory.exists_pos_lintegral_lt_of_sigmaFinite

#print MeasureTheory.lintegral_trim /-
theorem lintegral_trim {μ : Measure α} (hm : m ≤ m0) {f : α → ℝ≥0∞} (hf : measurable[m] f) :
    (∫⁻ a, f a ∂μ.trim hm) = ∫⁻ a, f a ∂μ :=
  by
  refine'
    @Measurable.ennreal_induction α m (fun f => (∫⁻ a, f a ∂μ.trim hm) = ∫⁻ a, f a ∂μ) _ _ _ f hf
  · intro c s hs
    rw [lintegral_indicator _ hs, lintegral_indicator _ (hm s hs), set_lintegral_const,
      set_lintegral_const]
    suffices h_trim_s : μ.trim hm s = μ s
    · rw [h_trim_s]
    exact trim_measurable_set_eq hm hs
  · intro f g hfg hf hg hf_prop hg_prop
    have h_m := lintegral_add_left hf g
    have h_m0 := lintegral_add_left (Measurable.mono hf hm le_rfl) g
    rwa [hf_prop, hg_prop, ← h_m0] at h_m
  · intro f hf hf_mono hf_prop
    rw [lintegral_supr hf hf_mono]
    rw [lintegral_supr (fun n => Measurable.mono (hf n) hm le_rfl) hf_mono]
    congr
    exact funext fun n => hf_prop n
#align measure_theory.lintegral_trim MeasureTheory.lintegral_trim
-/

#print MeasureTheory.lintegral_trim_ae /-
theorem lintegral_trim_ae {μ : Measure α} (hm : m ≤ m0) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f (μ.trim hm)) : (∫⁻ a, f a ∂μ.trim hm) = ∫⁻ a, f a ∂μ := by
  rw [lintegral_congr_ae (ae_eq_of_ae_eq_trim hf.ae_eq_mk), lintegral_congr_ae hf.ae_eq_mk,
    lintegral_trim hm hf.measurable_mk]
#align measure_theory.lintegral_trim_ae MeasureTheory.lintegral_trim_ae
-/

section SigmaFinite

variable {E : Type _} [NormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]

/- warning: measure_theory.univ_le_of_forall_fin_meas_le -> MeasureTheory.univ_le_of_forall_fin_meas_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} (hm : LE.le.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.hasLe.{u1} α) m m0) [_inst_4 : MeasureTheory.SigmaFinite.{u1} α m (MeasureTheory.Measure.trim.{u1} α m m0 μ hm)] (C : ENNReal) {f : (Set.{u1} α) -> ENNReal}, (forall (s : Set.{u1} α), (MeasurableSet.{u1} α m s) -> (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (f s) C)) -> (forall (S : Nat -> (Set.{u1} α)), (forall (n : Nat), MeasurableSet.{u1} α m (S n)) -> (Monotone.{0, u1} Nat (Set.{u1} α) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) S) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (f (Set.iUnion.{u1, 1} α Nat (fun (n : Nat) => S n))) (iSup.{0, 1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) Nat (fun (n : Nat) => f (S n))))) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (f (Set.univ.{u1} α)) C)
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} (hm : LE.le.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.instLEMeasurableSpace.{u1} α) m m0) [_inst_4 : MeasureTheory.SigmaFinite.{u1} α m (MeasureTheory.Measure.trim.{u1} α m m0 μ hm)] (C : ENNReal) {f : (Set.{u1} α) -> ENNReal}, (forall (s : Set.{u1} α), (MeasurableSet.{u1} α m s) -> (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (f s) C)) -> (forall (S : Nat -> (Set.{u1} α)), (forall (n : Nat), MeasurableSet.{u1} α m (S n)) -> (Monotone.{0, u1} Nat (Set.{u1} α) (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) S) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (f (Set.iUnion.{u1, 1} α Nat (fun (n : Nat) => S n))) (iSup.{0, 1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) Nat (fun (n : Nat) => f (S n))))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (f (Set.univ.{u1} α)) C)
Case conversion may be inaccurate. Consider using '#align measure_theory.univ_le_of_forall_fin_meas_le MeasureTheory.univ_le_of_forall_fin_meas_leₓ'. -/
theorem univ_le_of_forall_fin_meas_le {μ : Measure α} (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (C : ℝ≥0∞) {f : Set α → ℝ≥0∞} (hf : ∀ s, measurable_set[m] s → μ s ≠ ∞ → f s ≤ C)
    (h_F_lim :
      ∀ S : ℕ → Set α, (∀ n, measurable_set[m] (S n)) → Monotone S → f (⋃ n, S n) ≤ ⨆ n, f (S n)) :
    f univ ≤ C := by
  let S := @spanning_sets _ m (μ.trim hm) _
  have hS_mono : Monotone S := @monotone_spanning_sets _ m (μ.trim hm) _
  have hS_meas : ∀ n, measurable_set[m] (S n) := @measurable_spanning_sets _ m (μ.trim hm) _
  rw [← @Union_spanning_sets _ m (μ.trim hm)]
  refine' (h_F_lim S hS_meas hS_mono).trans _
  refine' iSup_le fun n => hf (S n) (hS_meas n) _
  exact ((le_trim hm).trans_lt (@measure_spanning_sets_lt_top _ m (μ.trim hm) _ n)).Ne
#align measure_theory.univ_le_of_forall_fin_meas_le MeasureTheory.univ_le_of_forall_fin_meas_le

/- warning: measure_theory.lintegral_le_of_forall_fin_meas_le_of_measurable -> MeasureTheory.lintegral_le_of_forall_fin_meas_le_of_measurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} (hm : LE.le.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.hasLe.{u1} α) m m0) [_inst_4 : MeasureTheory.SigmaFinite.{u1} α m (MeasureTheory.Measure.trim.{u1} α m m0 μ hm)] (C : ENNReal) {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m0 ENNReal.measurableSpace f) -> (forall (s : Set.{u1} α), (MeasurableSet.{u1} α m s) -> (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m0 (MeasureTheory.Measure.restrict.{u1} α m0 μ s) (fun (x : α) => f x)) C)) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m0 μ (fun (x : α) => f x)) C)
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} (hm : LE.le.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.instLEMeasurableSpace.{u1} α) m m0) [_inst_4 : MeasureTheory.SigmaFinite.{u1} α m (MeasureTheory.Measure.trim.{u1} α m m0 μ hm)] (C : ENNReal) {f : α -> ENNReal}, (Measurable.{u1, 0} α ENNReal m0 ENNReal.measurableSpace f) -> (forall (s : Set.{u1} α), (MeasurableSet.{u1} α m s) -> (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m0 (MeasureTheory.Measure.restrict.{u1} α m0 μ s) (fun (x : α) => f x)) C)) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m0 μ (fun (x : α) => f x)) C)
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_le_of_forall_fin_meas_le_of_measurable MeasureTheory.lintegral_le_of_forall_fin_meas_le_of_measurableₓ'. -/
/-- If the Lebesgue integral of a function is bounded by some constant on all sets with finite
measure in a sub-σ-algebra and the measure is σ-finite on that sub-σ-algebra, then the integral
over the whole space is bounded by that same constant. Version for a measurable function.
See `lintegral_le_of_forall_fin_meas_le'` for the more general `ae_measurable` version. -/
theorem lintegral_le_of_forall_fin_meas_le_of_measurable {μ : Measure α} (hm : m ≤ m0)
    [SigmaFinite (μ.trim hm)] (C : ℝ≥0∞) {f : α → ℝ≥0∞} (hf_meas : Measurable f)
    (hf : ∀ s, measurable_set[m] s → μ s ≠ ∞ → (∫⁻ x in s, f x ∂μ) ≤ C) : (∫⁻ x, f x ∂μ) ≤ C :=
  by
  have : (∫⁻ x in univ, f x ∂μ) = ∫⁻ x, f x ∂μ := by simp only [measure.restrict_univ]
  rw [← this]
  refine' univ_le_of_forall_fin_meas_le hm C hf fun S hS_meas hS_mono => _
  rw [← lintegral_indicator]
  swap
  · exact hm (⋃ n, S n) (@MeasurableSet.iUnion _ _ m _ _ hS_meas)
  have h_integral_indicator : (⨆ n, ∫⁻ x in S n, f x ∂μ) = ⨆ n, ∫⁻ x, (S n).indicator f x ∂μ :=
    by
    congr
    ext1 n
    rw [lintegral_indicator _ (hm _ (hS_meas n))]
  rw [h_integral_indicator, ← lintegral_supr]
  · refine' le_of_eq (lintegral_congr fun x => _)
    simp_rw [indicator_apply]
    by_cases hx_mem : x ∈ Union S
    · simp only [hx_mem, if_true]
      obtain ⟨n, hxn⟩ := mem_Union.mp hx_mem
      refine' le_antisymm (trans _ (le_iSup _ n)) (iSup_le fun i => _)
      · simp only [hxn, le_refl, if_true]
      · by_cases hxi : x ∈ S i <;> simp [hxi]
    · simp only [hx_mem, if_false]
      rw [mem_Union] at hx_mem
      push_neg  at hx_mem
      refine' le_antisymm (zero_le _) (iSup_le fun n => _)
      simp only [hx_mem n, if_false, nonpos_iff_eq_zero]
  · exact fun n => hf_meas.indicator (hm _ (hS_meas n))
  · intro n₁ n₂ hn₁₂ a
    simp_rw [indicator_apply]
    split_ifs
    · exact le_rfl
    · exact absurd (mem_of_mem_of_subset h (hS_mono hn₁₂)) h_1
    · exact zero_le _
    · exact le_rfl
#align measure_theory.lintegral_le_of_forall_fin_meas_le_of_measurable MeasureTheory.lintegral_le_of_forall_fin_meas_le_of_measurable

/- warning: measure_theory.lintegral_le_of_forall_fin_meas_le' -> MeasureTheory.lintegral_le_of_forall_fin_meas_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} (hm : LE.le.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.hasLe.{u1} α) m m0) [_inst_4 : MeasureTheory.SigmaFinite.{u1} α m (MeasureTheory.Measure.trim.{u1} α m m0 μ hm)] (C : ENNReal) {f : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m0 f μ) -> (forall (s : Set.{u1} α), (MeasurableSet.{u1} α m s) -> (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m0 (MeasureTheory.Measure.restrict.{u1} α m0 μ s) (fun (x : α) => f x)) C)) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m0 μ (fun (x : α) => f x)) C)
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} (hm : LE.le.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.instLEMeasurableSpace.{u1} α) m m0) [_inst_4 : MeasureTheory.SigmaFinite.{u1} α m (MeasureTheory.Measure.trim.{u1} α m m0 μ hm)] (C : ENNReal) {f : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace m0 f μ) -> (forall (s : Set.{u1} α), (MeasurableSet.{u1} α m s) -> (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m0 (MeasureTheory.Measure.restrict.{u1} α m0 μ s) (fun (x : α) => f x)) C)) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m0 μ (fun (x : α) => f x)) C)
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_le_of_forall_fin_meas_le' MeasureTheory.lintegral_le_of_forall_fin_meas_le'ₓ'. -/
/-- If the Lebesgue integral of a function is bounded by some constant on all sets with finite
measure in a sub-σ-algebra and the measure is σ-finite on that sub-σ-algebra, then the integral
over the whole space is bounded by that same constant. -/
theorem lintegral_le_of_forall_fin_meas_le' {μ : Measure α} (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (C : ℝ≥0∞) {f : _ → ℝ≥0∞} (hf_meas : AEMeasurable f μ)
    (hf : ∀ s, measurable_set[m] s → μ s ≠ ∞ → (∫⁻ x in s, f x ∂μ) ≤ C) : (∫⁻ x, f x ∂μ) ≤ C :=
  by
  let f' := hf_meas.mk f
  have hf' : ∀ s, measurable_set[m] s → μ s ≠ ∞ → (∫⁻ x in s, f' x ∂μ) ≤ C :=
    by
    refine' fun s hs hμs => (le_of_eq _).trans (hf s hs hμs)
    refine' lintegral_congr_ae (ae_restrict_of_ae (hf_meas.ae_eq_mk.mono fun x hx => _))
    rw [hx]
  rw [lintegral_congr_ae hf_meas.ae_eq_mk]
  exact lintegral_le_of_forall_fin_meas_le_of_measurable hm C hf_meas.measurable_mk hf'
#align measure_theory.lintegral_le_of_forall_fin_meas_le' MeasureTheory.lintegral_le_of_forall_fin_meas_le'

omit m

/- warning: measure_theory.lintegral_le_of_forall_fin_meas_le -> MeasureTheory.lintegral_le_of_forall_fin_meas_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_4 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_4} [_inst_5 : MeasureTheory.SigmaFinite.{u1} α _inst_4 μ] (C : ENNReal) {f : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_4 f μ) -> (forall (s : Set.{u1} α), (MeasurableSet.{u1} α _inst_4 s) -> (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_4) (fun (_x : MeasureTheory.Measure.{u1} α _inst_4) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_4) μ s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α _inst_4 (MeasureTheory.Measure.restrict.{u1} α _inst_4 μ s) (fun (x : α) => f x)) C)) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α _inst_4 μ (fun (x : α) => f x)) C)
but is expected to have type
  forall {α : Type.{u1}} [_inst_4 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_4} [_inst_5 : MeasureTheory.SigmaFinite.{u1} α _inst_4 μ] (C : ENNReal) {f : α -> ENNReal}, (AEMeasurable.{u1, 0} α ENNReal ENNReal.measurableSpace _inst_4 f μ) -> (forall (s : Set.{u1} α), (MeasurableSet.{u1} α _inst_4 s) -> (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_4 μ) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α _inst_4 (MeasureTheory.Measure.restrict.{u1} α _inst_4 μ s) (fun (x : α) => f x)) C)) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α _inst_4 μ (fun (x : α) => f x)) C)
Case conversion may be inaccurate. Consider using '#align measure_theory.lintegral_le_of_forall_fin_meas_le MeasureTheory.lintegral_le_of_forall_fin_meas_leₓ'. -/
/-- If the Lebesgue integral of a function is bounded by some constant on all sets with finite
measure and the measure is σ-finite, then the integral over the whole space is bounded by that same
constant. -/
theorem lintegral_le_of_forall_fin_meas_le [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    (C : ℝ≥0∞) {f : α → ℝ≥0∞} (hf_meas : AEMeasurable f μ)
    (hf : ∀ s, MeasurableSet s → μ s ≠ ∞ → (∫⁻ x in s, f x ∂μ) ≤ C) : (∫⁻ x, f x ∂μ) ≤ C :=
  @lintegral_le_of_forall_fin_meas_le' _ _ _ _ _ (by rwa [trim_eq_self]) C _ hf_meas hf
#align measure_theory.lintegral_le_of_forall_fin_meas_le MeasureTheory.lintegral_le_of_forall_fin_meas_le

-- mathport name: «expr →ₛ »
local infixr:25 " →ₛ " => SimpleFunc

/- warning: measure_theory.simple_func.exists_lt_lintegral_simple_func_of_lt_lintegral -> MeasureTheory.SimpleFunc.exists_lt_lintegral_simpleFunc_of_lt_lintegral is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_4 : MeasureTheory.SigmaFinite.{u1} α m μ] {f : MeasureTheory.SimpleFunc.{u1, 0} α m NNReal} {L : ENNReal}, (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) L (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (coeFn.{succ u1, succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) (fun (_x : MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) => α -> NNReal) (MeasureTheory.SimpleFunc.instCoeFun.{u1, 0} α NNReal m) f x)))) -> (Exists.{succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) (fun (g : MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) => And (forall (x : α), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (coeFn.{succ u1, succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) (fun (_x : MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) => α -> NNReal) (MeasureTheory.SimpleFunc.instCoeFun.{u1, 0} α NNReal m) g x) (coeFn.{succ u1, succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) (fun (_x : MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) => α -> NNReal) (MeasureTheory.SimpleFunc.instCoeFun.{u1, 0} α NNReal m) f x)) (And (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (coeFn.{succ u1, succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) (fun (_x : MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) => α -> NNReal) (MeasureTheory.SimpleFunc.instCoeFun.{u1, 0} α NNReal m) g x))) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) L (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (coeFn.{succ u1, succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) (fun (_x : MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) => α -> NNReal) (MeasureTheory.SimpleFunc.instCoeFun.{u1, 0} α NNReal m) g x)))))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_4 : MeasureTheory.SigmaFinite.{u1} α m μ] {f : MeasureTheory.SimpleFunc.{u1, 0} α m NNReal} {L : ENNReal}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) L (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => ENNReal.some (MeasureTheory.SimpleFunc.toFun.{u1, 0} α m NNReal f x)))) -> (Exists.{succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) (fun (g : MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) => And (forall (x : α), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (MeasureTheory.SimpleFunc.toFun.{u1, 0} α m NNReal g x) (MeasureTheory.SimpleFunc.toFun.{u1, 0} α m NNReal f x)) (And (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => ENNReal.some (MeasureTheory.SimpleFunc.toFun.{u1, 0} α m NNReal g x))) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) L (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => ENNReal.some (MeasureTheory.SimpleFunc.toFun.{u1, 0} α m NNReal g x)))))))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.exists_lt_lintegral_simple_func_of_lt_lintegral MeasureTheory.SimpleFunc.exists_lt_lintegral_simpleFunc_of_lt_lintegralₓ'. -/
theorem SimpleFunc.exists_lt_lintegral_simpleFunc_of_lt_lintegral {m : MeasurableSpace α}
    {μ : Measure α} [SigmaFinite μ] {f : α →ₛ ℝ≥0} {L : ℝ≥0∞} (hL : L < ∫⁻ x, f x ∂μ) :
    ∃ g : α →ₛ ℝ≥0, (∀ x, g x ≤ f x) ∧ (∫⁻ x, g x ∂μ) < ∞ ∧ L < ∫⁻ x, g x ∂μ :=
  by
  induction' f using MeasureTheory.SimpleFunc.induction with c s hs f₁ f₂ H h₁ h₂ generalizing L
  · simp only [hs, const_zero, coe_piecewise, coe_const, simple_func.coe_zero, univ_inter,
      piecewise_eq_indicator, lintegral_indicator, lintegral_const, measure.restrict_apply',
      coe_indicator, Function.const_apply] at hL
    have c_ne_zero : c ≠ 0 := by
      intro hc
      simpa only [hc, ENNReal.coe_zero, MulZeroClass.zero_mul, not_lt_zero] using hL
    have : L / c < μ s := by
      rwa [ENNReal.div_lt_iff, mul_comm]
      · simp only [c_ne_zero, Ne.def, coe_eq_zero, not_false_iff, true_or_iff]
      · simp only [Ne.def, coe_ne_top, not_false_iff, true_or_iff]
    obtain ⟨t, ht, ts, mut, t_top⟩ :
      ∃ t : Set α, MeasurableSet t ∧ t ⊆ s ∧ L / ↑c < μ t ∧ μ t < ∞ :=
      measure.exists_subset_measure_lt_top hs this
    refine' ⟨piecewise t ht (const α c) (const α 0), fun x => _, _, _⟩
    · apply indicator_le_indicator_of_subset ts fun x => _
      exact zero_le _
    ·
      simp only [ht, const_zero, coe_piecewise, coe_const, simple_func.coe_zero, univ_inter,
        piecewise_eq_indicator, coe_indicator, Function.const_apply, lintegral_indicator,
        lintegral_const, measure.restrict_apply', ENNReal.mul_lt_top ENNReal.coe_ne_top t_top.ne]
    · simp only [ht, const_zero, coe_piecewise, coe_const, simple_func.coe_zero,
        piecewise_eq_indicator, coe_indicator, Function.const_apply, lintegral_indicator,
        lintegral_const, measure.restrict_apply', univ_inter]
      rwa [mul_comm, ← ENNReal.div_lt_iff]
      · simp only [c_ne_zero, Ne.def, coe_eq_zero, not_false_iff, true_or_iff]
      · simp only [Ne.def, coe_ne_top, not_false_iff, true_or_iff]
  · replace hL : L < (∫⁻ x, f₁ x ∂μ) + ∫⁻ x, f₂ x ∂μ
    · rwa [← lintegral_add_left f₁.measurable.coe_nnreal_ennreal]
    by_cases hf₁ : (∫⁻ x, f₁ x ∂μ) = 0
    · simp only [hf₁, zero_add] at hL
      rcases h₂ hL with ⟨g, g_le, g_top, gL⟩
      refine' ⟨g, fun x => (g_le x).trans _, g_top, gL⟩
      simp only [simple_func.coe_add, Pi.add_apply, le_add_iff_nonneg_left, zero_le']
    by_cases hf₂ : (∫⁻ x, f₂ x ∂μ) = 0
    · simp only [hf₂, add_zero] at hL
      rcases h₁ hL with ⟨g, g_le, g_top, gL⟩
      refine' ⟨g, fun x => (g_le x).trans _, g_top, gL⟩
      simp only [simple_func.coe_add, Pi.add_apply, le_add_iff_nonneg_right, zero_le']
    obtain ⟨L₁, L₂, hL₁, hL₂, hL⟩ :
      ∃ L₁ L₂ : ℝ≥0∞, (L₁ < ∫⁻ x, f₁ x ∂μ) ∧ (L₂ < ∫⁻ x, f₂ x ∂μ) ∧ L < L₁ + L₂ :=
      ENNReal.exists_lt_add_of_lt_add hL hf₁ hf₂
    rcases h₁ hL₁ with ⟨g₁, g₁_le, g₁_top, hg₁⟩
    rcases h₂ hL₂ with ⟨g₂, g₂_le, g₂_top, hg₂⟩
    refine' ⟨g₁ + g₂, fun x => add_le_add (g₁_le x) (g₂_le x), _, _⟩
    · apply lt_of_le_of_lt _ (add_lt_top.2 ⟨g₁_top, g₂_top⟩)
      rw [← lintegral_add_left g₁.measurable.coe_nnreal_ennreal]
      exact le_rfl
    · apply hL.trans ((ENNReal.add_lt_add hg₁ hg₂).trans_le _)
      rw [← lintegral_add_left g₁.measurable.coe_nnreal_ennreal]
      exact le_rfl
#align measure_theory.simple_func.exists_lt_lintegral_simple_func_of_lt_lintegral MeasureTheory.SimpleFunc.exists_lt_lintegral_simpleFunc_of_lt_lintegral

/- warning: measure_theory.exists_lt_lintegral_simple_func_of_lt_lintegral -> MeasureTheory.exists_lt_lintegral_simpleFunc_of_lt_lintegral is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_4 : MeasureTheory.SigmaFinite.{u1} α m μ] {f : α -> NNReal} {L : ENNReal}, (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) L (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (f x)))) -> (Exists.{succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) (fun (g : MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) => And (forall (x : α), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (coeFn.{succ u1, succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) (fun (_x : MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) => α -> NNReal) (MeasureTheory.SimpleFunc.instCoeFun.{u1, 0} α NNReal m) g x) (f x)) (And (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (coeFn.{succ u1, succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) (fun (_x : MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) => α -> NNReal) (MeasureTheory.SimpleFunc.instCoeFun.{u1, 0} α NNReal m) g x))) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) L (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (coeFn.{succ u1, succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) (fun (_x : MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) => α -> NNReal) (MeasureTheory.SimpleFunc.instCoeFun.{u1, 0} α NNReal m) g x)))))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_4 : MeasureTheory.SigmaFinite.{u1} α m μ] {f : α -> NNReal} {L : ENNReal}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) L (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => ENNReal.some (f x)))) -> (Exists.{succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) (fun (g : MeasureTheory.SimpleFunc.{u1, 0} α m NNReal) => And (forall (x : α), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (MeasureTheory.SimpleFunc.toFun.{u1, 0} α m NNReal g x) (f x)) (And (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => ENNReal.some (MeasureTheory.SimpleFunc.toFun.{u1, 0} α m NNReal g x))) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) L (MeasureTheory.lintegral.{u1} α m μ (fun (x : α) => ENNReal.some (MeasureTheory.SimpleFunc.toFun.{u1, 0} α m NNReal g x)))))))
Case conversion may be inaccurate. Consider using '#align measure_theory.exists_lt_lintegral_simple_func_of_lt_lintegral MeasureTheory.exists_lt_lintegral_simpleFunc_of_lt_lintegralₓ'. -/
theorem exists_lt_lintegral_simpleFunc_of_lt_lintegral {m : MeasurableSpace α} {μ : Measure α}
    [SigmaFinite μ] {f : α → ℝ≥0} {L : ℝ≥0∞} (hL : L < ∫⁻ x, f x ∂μ) :
    ∃ g : α →ₛ ℝ≥0, (∀ x, g x ≤ f x) ∧ (∫⁻ x, g x ∂μ) < ∞ ∧ L < ∫⁻ x, g x ∂μ :=
  by
  simp_rw [lintegral_eq_nnreal, lt_iSup_iff] at hL
  rcases hL with ⟨g₀, hg₀, g₀L⟩
  have h'L : L < ∫⁻ x, g₀ x ∂μ := by
    convert g₀L
    rw [← simple_func.lintegral_eq_lintegral]
    rfl
  rcases simple_func.exists_lt_lintegral_simple_func_of_lt_lintegral h'L with ⟨g, hg, gL, gtop⟩
  exact ⟨g, fun x => (hg x).trans (coe_le_coe.1 (hg₀ x)), gL, gtop⟩
#align measure_theory.exists_lt_lintegral_simple_func_of_lt_lintegral MeasureTheory.exists_lt_lintegral_simpleFunc_of_lt_lintegral

#print MeasureTheory.exists_absolutelyContinuous_finiteMeasure /-
/-- A sigma-finite measure is absolutely continuous with respect to some finite measure. -/
theorem exists_absolutelyContinuous_finiteMeasure {m : MeasurableSpace α} (μ : Measure α)
    [SigmaFinite μ] : ∃ ν : Measure α, FiniteMeasure ν ∧ μ ≪ ν :=
  by
  obtain ⟨g, gpos, gmeas, hg⟩ :
    ∃ g : α → ℝ≥0, (∀ x : α, 0 < g x) ∧ Measurable g ∧ (∫⁻ x : α, ↑(g x) ∂μ) < 1 :=
    exists_pos_lintegral_lt_of_sigma_finite μ one_ne_zero
  refine' ⟨μ.with_density fun x => g x, is_finite_measure_with_density hg.ne_top, _⟩
  have : μ = (μ.with_density fun x => g x).withDensity fun x => (g x)⁻¹ :=
    by
    have A : ((fun x : α => (g x : ℝ≥0∞)) * fun x : α => (↑(g x))⁻¹) = 1 :=
      by
      ext1 x
      exact ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.2 (gpos x).ne') ENNReal.coe_ne_top
    rw [← with_density_mul _ gmeas.coe_nnreal_ennreal gmeas.coe_nnreal_ennreal.inv, A,
      with_density_one]
  conv_lhs => rw [this]
  exact with_density_absolutely_continuous _ _
#align measure_theory.exists_absolutely_continuous_is_finite_measure MeasureTheory.exists_absolutelyContinuous_finiteMeasure
-/

end SigmaFinite

end MeasureTheory

