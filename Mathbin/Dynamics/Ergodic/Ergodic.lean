/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash

! This file was ported from Lean 3 source module dynamics.ergodic.ergodic
! leanprover-community/mathlib commit 781cb2eed038c4caf53bdbd8d20a95e5822d77df
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Dynamics.Ergodic.MeasurePreserving

/-!
# Ergodic maps and measures

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Let `f : α → α` be measure preserving with respect to a measure `μ`. We say `f` is ergodic with
respect to `μ` (or `μ` is ergodic with respect to `f`) if the only measurable sets `s` such that
`f⁻¹' s = s` are either almost empty or full.

In this file we define ergodic maps / measures together with quasi-ergodic maps / measures and
provide some basic API. Quasi-ergodicity is a weaker condition than ergodicity for which the measure
preserving condition is relaxed to quasi measure preserving.

# Main definitions:

 * `pre_ergodic`: the ergodicity condition without the measure preserving condition. This exists
   to share code between the `ergodic` and `quasi_ergodic` definitions.
 * `ergodic`: the definition of ergodic maps / measures.
 * `quasi_ergodic`: the definition of quasi ergodic maps / measures.
 * `ergodic.quasi_ergodic`: an ergodic map / measure is quasi ergodic.
 * `quasi_ergodic.ae_empty_or_univ'`: when the map is quasi measure preserving, one may relax the
   strict invariance condition to almost invariance in the ergodicity condition.

-/


open Set Function Filter MeasureTheory MeasureTheory.Measure

open ENNReal

variable {α : Type _} {m : MeasurableSpace α} (f : α → α) {s : Set α}

include m

#print PreErgodic /-
/-- A map `f : α → α` is said to be pre-ergodic with respect to a measure `μ` if any measurable
strictly invariant set is either almost empty or full. -/
structure PreErgodic (μ : Measure α := by exact MeasureTheory.MeasureSpace.volume) : Prop where
  ae_empty_or_univ : ∀ ⦃s⦄, MeasurableSet s → f ⁻¹' s = s → s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ
#align pre_ergodic PreErgodic
-/

#print Ergodic /-
/-- A map `f : α → α` is said to be ergodic with respect to a measure `μ` if it is measure
preserving and pre-ergodic. -/
@[nolint has_nonempty_instance]
structure Ergodic (μ : Measure α := by exact MeasureTheory.MeasureSpace.volume) extends
  MeasurePreserving f μ μ, PreErgodic f μ : Prop
#align ergodic Ergodic
-/

#print QuasiErgodic /-
/-- A map `f : α → α` is said to be quasi ergodic with respect to a measure `μ` if it is quasi
measure preserving and pre-ergodic. -/
@[nolint has_nonempty_instance]
structure QuasiErgodic (μ : Measure α := by exact MeasureTheory.MeasureSpace.volume) extends
  QuasiMeasurePreserving f μ μ, PreErgodic f μ : Prop
#align quasi_ergodic QuasiErgodic
-/

variable {f} {μ : Measure α}

namespace PreErgodic

/- warning: pre_ergodic.measure_self_or_compl_eq_zero -> PreErgodic.measure_self_or_compl_eq_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {f : α -> α} {s : Set.{u1} α} {μ : MeasureTheory.Measure.{u1} α m}, (PreErgodic.{u1} α m f μ) -> (MeasurableSet.{u1} α m s) -> (Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u1} α α f s) s) -> (Or (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {f : α -> α} {s : Set.{u1} α} {μ : MeasureTheory.Measure.{u1} α m}, (PreErgodic.{u1} α m f μ) -> (MeasurableSet.{u1} α m s) -> (Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u1} α α f s) s) -> (Or (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))))
Case conversion may be inaccurate. Consider using '#align pre_ergodic.measure_self_or_compl_eq_zero PreErgodic.measure_self_or_compl_eq_zeroₓ'. -/
theorem measure_self_or_compl_eq_zero (hf : PreErgodic f μ) (hs : MeasurableSet s)
    (hs' : f ⁻¹' s = s) : μ s = 0 ∨ μ (sᶜ) = 0 := by simpa using hf.ae_empty_or_univ hs hs'
#align pre_ergodic.measure_self_or_compl_eq_zero PreErgodic.measure_self_or_compl_eq_zero

/- warning: pre_ergodic.prob_eq_zero_or_one -> PreErgodic.prob_eq_zero_or_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {f : α -> α} {s : Set.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : MeasureTheory.ProbabilityMeasure.{u1} α m μ], (PreErgodic.{u1} α m f μ) -> (MeasurableSet.{u1} α m s) -> (Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u1} α α f s) s) -> (Or (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ s) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {f : α -> α} {s : Set.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_1 : MeasureTheory.ProbabilityMeasure.{u1} α m μ], (PreErgodic.{u1} α m f μ) -> (MeasurableSet.{u1} α m s) -> (Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u1} α α f s) s) -> (Or (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) s) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))
Case conversion may be inaccurate. Consider using '#align pre_ergodic.prob_eq_zero_or_one PreErgodic.prob_eq_zero_or_oneₓ'. -/
/-- On a probability space, the (pre)ergodicity condition is a zero one law. -/
theorem prob_eq_zero_or_one [ProbabilityMeasure μ] (hf : PreErgodic f μ) (hs : MeasurableSet s)
    (hs' : f ⁻¹' s = s) : μ s = 0 ∨ μ s = 1 := by
  simpa [hs] using hf.measure_self_or_compl_eq_zero hs hs'
#align pre_ergodic.prob_eq_zero_or_one PreErgodic.prob_eq_zero_or_one

#print PreErgodic.of_iterate /-
theorem of_iterate (n : ℕ) (hf : PreErgodic (f^[n]) μ) : PreErgodic f μ :=
  ⟨fun s hs hs' => hf.ae_empty_or_univ hs <| IsFixedPt.preimage_iterate hs' n⟩
#align pre_ergodic.of_iterate PreErgodic.of_iterate
-/

end PreErgodic

namespace MeasureTheory.MeasurePreserving

variable {β : Type _} {m' : MeasurableSpace β} {μ' : Measure β} {s' : Set β} {g : α → β}

/- warning: measure_theory.measure_preserving.pre_ergodic_of_pre_ergodic_conjugate -> MeasureTheory.MeasurePreserving.preErgodic_of_preErgodic_conjugate is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {f : α -> α} {μ : MeasureTheory.Measure.{u1} α m} {β : Type.{u2}} {m' : MeasurableSpace.{u2} β} {μ' : MeasureTheory.Measure.{u2} β m'} {g : α -> β}, (MeasureTheory.MeasurePreserving.{u1, u2} α β m m' g μ μ') -> (PreErgodic.{u1} α m f μ) -> (forall {f' : β -> β}, (Eq.{max (succ u1) (succ u2)} (α -> β) (Function.comp.{succ u1, succ u1, succ u2} α α β g f) (Function.comp.{succ u1, succ u2, succ u2} α β β f' g)) -> (PreErgodic.{u2} β m' f' μ'))
but is expected to have type
  forall {α : Type.{u2}} {m : MeasurableSpace.{u2} α} {f : α -> α} {μ : MeasureTheory.Measure.{u2} α m} {β : Type.{u1}} {m' : MeasurableSpace.{u1} β} {μ' : MeasureTheory.Measure.{u1} β m'} {g : α -> β}, (MeasureTheory.MeasurePreserving.{u2, u1} α β m m' g μ μ') -> (PreErgodic.{u2} α m f μ) -> (forall {f' : β -> β}, (Eq.{max (succ u2) (succ u1)} (α -> β) (Function.comp.{succ u2, succ u2, succ u1} α α β g f) (Function.comp.{succ u2, succ u1, succ u1} α β β f' g)) -> (PreErgodic.{u1} β m' f' μ'))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_preserving.pre_ergodic_of_pre_ergodic_conjugate MeasureTheory.MeasurePreserving.preErgodic_of_preErgodic_conjugateₓ'. -/
theorem preErgodic_of_preErgodic_conjugate (hg : MeasurePreserving g μ μ') (hf : PreErgodic f μ)
    {f' : β → β} (h_comm : g ∘ f = f' ∘ g) : PreErgodic f' μ' :=
  ⟨by
    intro s hs₀ hs₁
    replace hs₁ : f ⁻¹' (g ⁻¹' s) = g ⁻¹' s; · rw [← preimage_comp, h_comm, preimage_comp, hs₁]
    cases' hf.ae_empty_or_univ (hg.measurable hs₀) hs₁ with hs₂ hs₂ <;> [left;right]
    · simpa only [ae_eq_empty, hg.measure_preimage hs₀] using hs₂
    · simpa only [ae_eq_univ, ← preimage_compl, hg.measure_preimage hs₀.compl] using hs₂⟩
#align measure_theory.measure_preserving.pre_ergodic_of_pre_ergodic_conjugate MeasureTheory.MeasurePreserving.preErgodic_of_preErgodic_conjugate

/- warning: measure_theory.measure_preserving.pre_ergodic_conjugate_iff -> MeasureTheory.MeasurePreserving.preErgodic_conjugate_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {f : α -> α} {μ : MeasureTheory.Measure.{u1} α m} {β : Type.{u2}} {m' : MeasurableSpace.{u2} β} {μ' : MeasureTheory.Measure.{u2} β m'} {e : MeasurableEquiv.{u1, u2} α β m m'}, (MeasureTheory.MeasurePreserving.{u1, u2} α β m m' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasurableEquiv.{u1, u2} α β m m') (fun (_x : MeasurableEquiv.{u1, u2} α β m m') => α -> β) (MeasurableEquiv.hasCoeToFun.{u1, u2} α β m m') e) μ μ') -> (Iff (PreErgodic.{u2} β m' (Function.comp.{succ u2, succ u1, succ u2} β α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasurableEquiv.{u1, u2} α β m m') (fun (_x : MeasurableEquiv.{u1, u2} α β m m') => α -> β) (MeasurableEquiv.hasCoeToFun.{u1, u2} α β m m') e) (Function.comp.{succ u2, succ u1, succ u1} β α α f (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MeasurableEquiv.{u2, u1} β α m' m) (fun (_x : MeasurableEquiv.{u2, u1} β α m' m) => β -> α) (MeasurableEquiv.hasCoeToFun.{u2, u1} β α m' m) (MeasurableEquiv.symm.{u1, u2} α β m m' e)))) μ') (PreErgodic.{u1} α m f μ))
but is expected to have type
  forall {α : Type.{u2}} {m : MeasurableSpace.{u2} α} {f : α -> α} {μ : MeasureTheory.Measure.{u2} α m} {β : Type.{u1}} {m' : MeasurableSpace.{u1} β} {μ' : MeasureTheory.Measure.{u1} β m'} {e : MeasurableEquiv.{u2, u1} α β m m'}, (MeasureTheory.MeasurePreserving.{u2, u1} α β m m' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β m m') α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β m m') α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β m m') α β (MeasurableEquiv.instEquivLike.{u2, u1} α β m m'))) e) μ μ') -> (Iff (PreErgodic.{u1} β m' (Function.comp.{succ u1, succ u2, succ u1} β α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β m m') α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β m m') α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β m m') α β (MeasurableEquiv.instEquivLike.{u2, u1} α β m m'))) e) (Function.comp.{succ u1, succ u2, succ u2} β α α f (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α m' m) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α m' m) β α (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α m' m) β α (MeasurableEquiv.instEquivLike.{u1, u2} β α m' m))) (MeasurableEquiv.symm.{u2, u1} α β m m' e)))) μ') (PreErgodic.{u2} α m f μ))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_preserving.pre_ergodic_conjugate_iff MeasureTheory.MeasurePreserving.preErgodic_conjugate_iffₓ'. -/
theorem preErgodic_conjugate_iff {e : α ≃ᵐ β} (h : MeasurePreserving e μ μ') :
    PreErgodic (e ∘ f ∘ e.symm) μ' ↔ PreErgodic f μ :=
  by
  refine'
    ⟨fun hf => pre_ergodic_of_pre_ergodic_conjugate (h.symm e) hf _, fun hf =>
      pre_ergodic_of_pre_ergodic_conjugate h hf _⟩
  · change (e.symm ∘ e) ∘ f ∘ e.symm = f ∘ e.symm
    rw [MeasurableEquiv.symm_comp_self, comp.left_id]
  · change e ∘ f = e ∘ f ∘ e.symm ∘ e
    rw [MeasurableEquiv.symm_comp_self, comp.right_id]
#align measure_theory.measure_preserving.pre_ergodic_conjugate_iff MeasureTheory.MeasurePreserving.preErgodic_conjugate_iff

/- warning: measure_theory.measure_preserving.ergodic_conjugate_iff -> MeasureTheory.MeasurePreserving.ergodic_conjugate_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {f : α -> α} {μ : MeasureTheory.Measure.{u1} α m} {β : Type.{u2}} {m' : MeasurableSpace.{u2} β} {μ' : MeasureTheory.Measure.{u2} β m'} {e : MeasurableEquiv.{u1, u2} α β m m'}, (MeasureTheory.MeasurePreserving.{u1, u2} α β m m' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasurableEquiv.{u1, u2} α β m m') (fun (_x : MeasurableEquiv.{u1, u2} α β m m') => α -> β) (MeasurableEquiv.hasCoeToFun.{u1, u2} α β m m') e) μ μ') -> (Iff (Ergodic.{u2} β m' (Function.comp.{succ u2, succ u1, succ u2} β α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasurableEquiv.{u1, u2} α β m m') (fun (_x : MeasurableEquiv.{u1, u2} α β m m') => α -> β) (MeasurableEquiv.hasCoeToFun.{u1, u2} α β m m') e) (Function.comp.{succ u2, succ u1, succ u1} β α α f (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MeasurableEquiv.{u2, u1} β α m' m) (fun (_x : MeasurableEquiv.{u2, u1} β α m' m) => β -> α) (MeasurableEquiv.hasCoeToFun.{u2, u1} β α m' m) (MeasurableEquiv.symm.{u1, u2} α β m m' e)))) μ') (Ergodic.{u1} α m f μ))
but is expected to have type
  forall {α : Type.{u2}} {m : MeasurableSpace.{u2} α} {f : α -> α} {μ : MeasureTheory.Measure.{u2} α m} {β : Type.{u1}} {m' : MeasurableSpace.{u1} β} {μ' : MeasureTheory.Measure.{u1} β m'} {e : MeasurableEquiv.{u2, u1} α β m m'}, (MeasureTheory.MeasurePreserving.{u2, u1} α β m m' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β m m') α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β m m') α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β m m') α β (MeasurableEquiv.instEquivLike.{u2, u1} α β m m'))) e) μ μ') -> (Iff (Ergodic.{u1} β m' (Function.comp.{succ u1, succ u2, succ u1} β α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β m m') α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β m m') α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β m m') α β (MeasurableEquiv.instEquivLike.{u2, u1} α β m m'))) e) (Function.comp.{succ u1, succ u2, succ u2} β α α f (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α m' m) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α m' m) β α (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α m' m) β α (MeasurableEquiv.instEquivLike.{u1, u2} β α m' m))) (MeasurableEquiv.symm.{u2, u1} α β m m' e)))) μ') (Ergodic.{u2} α m f μ))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_preserving.ergodic_conjugate_iff MeasureTheory.MeasurePreserving.ergodic_conjugate_iffₓ'. -/
theorem ergodic_conjugate_iff {e : α ≃ᵐ β} (h : MeasurePreserving e μ μ') :
    Ergodic (e ∘ f ∘ e.symm) μ' ↔ Ergodic f μ :=
  by
  have : measure_preserving (e ∘ f ∘ e.symm) μ' μ' ↔ measure_preserving f μ μ := by
    rw [h.comp_left_iff, (measure_preserving.symm e h).comp_right_iff]
  replace h : PreErgodic (e ∘ f ∘ e.symm) μ' ↔ PreErgodic f μ := h.pre_ergodic_conjugate_iff
  exact
    ⟨fun hf => { this.mp hf.to_measurePreserving, h.mp hf.to_preErgodic with }, fun hf =>
      { this.mpr hf.to_measurePreserving, h.mpr hf.to_preErgodic with }⟩
#align measure_theory.measure_preserving.ergodic_conjugate_iff MeasureTheory.MeasurePreserving.ergodic_conjugate_iff

end MeasureTheory.MeasurePreserving

namespace QuasiErgodic

#print QuasiErgodic.ae_empty_or_univ' /-
/-- For a quasi ergodic map, sets that are almost invariant (rather than strictly invariant) are
still either almost empty or full. -/
theorem ae_empty_or_univ' (hf : QuasiErgodic f μ) (hs : MeasurableSet s) (hs' : f ⁻¹' s =ᵐ[μ] s) :
    s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ :=
  by
  obtain ⟨t, h₀, h₁, h₂⟩ := hf.to_quasi_measure_preserving.exists_preimage_eq_of_preimage_ae hs hs'
  rcases hf.ae_empty_or_univ h₀ h₂ with (h₃ | h₃) <;> [left;right] <;> exact ae_eq_trans h₁.symm h₃
#align quasi_ergodic.ae_empty_or_univ' QuasiErgodic.ae_empty_or_univ'
-/

end QuasiErgodic

namespace Ergodic

#print Ergodic.quasiErgodic /-
/-- An ergodic map is quasi ergodic. -/
theorem quasiErgodic (hf : Ergodic f μ) : QuasiErgodic f μ :=
  { hf.to_preErgodic, hf.to_measurePreserving.QuasiMeasurePreserving with }
#align ergodic.quasi_ergodic Ergodic.quasiErgodic
-/

/- warning: ergodic.ae_empty_or_univ_of_preimage_ae_le' -> Ergodic.ae_empty_or_univ_of_preimage_ae_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {f : α -> α} {s : Set.{u1} α} {μ : MeasureTheory.Measure.{u1} α m}, (Ergodic.{u1} α m f μ) -> (MeasurableSet.{u1} α m s) -> (Filter.EventuallyLE.{u1, 0} α Prop Prop.le (MeasureTheory.Measure.ae.{u1} α m μ) (Set.preimage.{u1, u1} α α f s) s) -> (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Or (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α m μ) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α m μ) s (Set.univ.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {f : α -> α} {s : Set.{u1} α} {μ : MeasureTheory.Measure.{u1} α m}, (Ergodic.{u1} α m f μ) -> (MeasurableSet.{u1} α m s) -> (Filter.EventuallyLE.{u1, 0} α Prop Prop.le (MeasureTheory.Measure.ae.{u1} α m μ) (Set.preimage.{u1, u1} α α f s) s) -> (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Or (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α m μ) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α m μ) s (Set.univ.{u1} α)))
Case conversion may be inaccurate. Consider using '#align ergodic.ae_empty_or_univ_of_preimage_ae_le' Ergodic.ae_empty_or_univ_of_preimage_ae_le'ₓ'. -/
/-- See also `ergodic.ae_empty_or_univ_of_preimage_ae_le`. -/
theorem ae_empty_or_univ_of_preimage_ae_le' (hf : Ergodic f μ) (hs : MeasurableSet s)
    (hs' : f ⁻¹' s ≤ᵐ[μ] s) (h_fin : μ s ≠ ∞) : s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ :=
  by
  refine' hf.quasi_ergodic.ae_empty_or_univ' hs _
  refine' ae_eq_of_ae_subset_of_measure_ge hs' (hf.measure_preimage hs).symm.le _ h_fin
  exact measurableSet_preimage hf.measurable hs
#align ergodic.ae_empty_or_univ_of_preimage_ae_le' Ergodic.ae_empty_or_univ_of_preimage_ae_le'

/- warning: ergodic.ae_empty_or_univ_of_ae_le_preimage' -> Ergodic.ae_empty_or_univ_of_ae_le_preimage' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {f : α -> α} {s : Set.{u1} α} {μ : MeasureTheory.Measure.{u1} α m}, (Ergodic.{u1} α m f μ) -> (MeasurableSet.{u1} α m s) -> (Filter.EventuallyLE.{u1, 0} α Prop Prop.le (MeasureTheory.Measure.ae.{u1} α m μ) s (Set.preimage.{u1, u1} α α f s)) -> (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Or (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α m μ) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α m μ) s (Set.univ.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {f : α -> α} {s : Set.{u1} α} {μ : MeasureTheory.Measure.{u1} α m}, (Ergodic.{u1} α m f μ) -> (MeasurableSet.{u1} α m s) -> (Filter.EventuallyLE.{u1, 0} α Prop Prop.le (MeasureTheory.Measure.ae.{u1} α m μ) s (Set.preimage.{u1, u1} α α f s)) -> (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Or (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α m μ) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α m μ) s (Set.univ.{u1} α)))
Case conversion may be inaccurate. Consider using '#align ergodic.ae_empty_or_univ_of_ae_le_preimage' Ergodic.ae_empty_or_univ_of_ae_le_preimage'ₓ'. -/
/-- See also `ergodic.ae_empty_or_univ_of_ae_le_preimage`. -/
theorem ae_empty_or_univ_of_ae_le_preimage' (hf : Ergodic f μ) (hs : MeasurableSet s)
    (hs' : s ≤ᵐ[μ] f ⁻¹' s) (h_fin : μ s ≠ ∞) : s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ :=
  by
  replace h_fin : μ (f ⁻¹' s) ≠ ∞; · rwa [hf.measure_preimage hs]
  refine' hf.quasi_ergodic.ae_empty_or_univ' hs _
  exact (ae_eq_of_ae_subset_of_measure_ge hs' (hf.measure_preimage hs).le hs h_fin).symm
#align ergodic.ae_empty_or_univ_of_ae_le_preimage' Ergodic.ae_empty_or_univ_of_ae_le_preimage'

/- warning: ergodic.ae_empty_or_univ_of_image_ae_le' -> Ergodic.ae_empty_or_univ_of_image_ae_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {f : α -> α} {s : Set.{u1} α} {μ : MeasureTheory.Measure.{u1} α m}, (Ergodic.{u1} α m f μ) -> (MeasurableSet.{u1} α m s) -> (Filter.EventuallyLE.{u1, 0} α Prop Prop.le (MeasureTheory.Measure.ae.{u1} α m μ) (Set.image.{u1, u1} α α f s) s) -> (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Or (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α m μ) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α m μ) s (Set.univ.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {f : α -> α} {s : Set.{u1} α} {μ : MeasureTheory.Measure.{u1} α m}, (Ergodic.{u1} α m f μ) -> (MeasurableSet.{u1} α m s) -> (Filter.EventuallyLE.{u1, 0} α Prop Prop.le (MeasureTheory.Measure.ae.{u1} α m μ) (Set.image.{u1, u1} α α f s) s) -> (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Or (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α m μ) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α m μ) s (Set.univ.{u1} α)))
Case conversion may be inaccurate. Consider using '#align ergodic.ae_empty_or_univ_of_image_ae_le' Ergodic.ae_empty_or_univ_of_image_ae_le'ₓ'. -/
/-- See also `ergodic.ae_empty_or_univ_of_image_ae_le`. -/
theorem ae_empty_or_univ_of_image_ae_le' (hf : Ergodic f μ) (hs : MeasurableSet s)
    (hs' : f '' s ≤ᵐ[μ] s) (h_fin : μ s ≠ ∞) : s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ :=
  by
  replace hs' : s ≤ᵐ[μ] f ⁻¹' s :=
    (HasSubset.Subset.eventuallyLE (subset_preimage_image f s)).trans
      (hf.quasi_measure_preserving.preimage_mono_ae hs')
  exact ae_empty_or_univ_of_ae_le_preimage' hf hs hs' h_fin
#align ergodic.ae_empty_or_univ_of_image_ae_le' Ergodic.ae_empty_or_univ_of_image_ae_le'

section IsFiniteMeasure

variable [FiniteMeasure μ]

#print Ergodic.ae_empty_or_univ_of_preimage_ae_le /-
theorem ae_empty_or_univ_of_preimage_ae_le (hf : Ergodic f μ) (hs : MeasurableSet s)
    (hs' : f ⁻¹' s ≤ᵐ[μ] s) : s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ :=
  ae_empty_or_univ_of_preimage_ae_le' hf hs hs' <| measure_ne_top μ s
#align ergodic.ae_empty_or_univ_of_preimage_ae_le Ergodic.ae_empty_or_univ_of_preimage_ae_le
-/

#print Ergodic.ae_empty_or_univ_of_ae_le_preimage /-
theorem ae_empty_or_univ_of_ae_le_preimage (hf : Ergodic f μ) (hs : MeasurableSet s)
    (hs' : s ≤ᵐ[μ] f ⁻¹' s) : s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ :=
  ae_empty_or_univ_of_ae_le_preimage' hf hs hs' <| measure_ne_top μ s
#align ergodic.ae_empty_or_univ_of_ae_le_preimage Ergodic.ae_empty_or_univ_of_ae_le_preimage
-/

#print Ergodic.ae_empty_or_univ_of_image_ae_le /-
theorem ae_empty_or_univ_of_image_ae_le (hf : Ergodic f μ) (hs : MeasurableSet s)
    (hs' : f '' s ≤ᵐ[μ] s) : s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ :=
  ae_empty_or_univ_of_image_ae_le' hf hs hs' <| measure_ne_top μ s
#align ergodic.ae_empty_or_univ_of_image_ae_le Ergodic.ae_empty_or_univ_of_image_ae_le
-/

end IsFiniteMeasure

end Ergodic

