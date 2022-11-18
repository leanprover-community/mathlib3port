/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathbin.Dynamics.Ergodic.MeasurePreserving

/-!
# Ergodic maps and measures

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

variable {α : Type _} {m : MeasurableSpace α} (f : α → α) {s : Set α}

include m

/-- A map `f : α → α` is said to be pre-ergodic with respect to a measure `μ` if any measurable
strictly invariant set is either almost empty or full. -/
structure PreErgodic (μ : Measure α := by exact MeasureTheory.MeasureSpace.volume) : Prop where
  ae_empty_or_univ : ∀ ⦃s⦄, MeasurableSet s → f ⁻¹' s = s → s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ
#align pre_ergodic PreErgodic

/-- A map `f : α → α` is said to be ergodic with respect to a measure `μ` if it is measure
preserving and pre-ergodic. -/
@[nolint has_nonempty_instance]
structure Ergodic (μ : Measure α := by exact MeasureTheory.MeasureSpace.volume) extends MeasurePreserving f μ μ,
  PreErgodic f μ : Prop
#align ergodic Ergodic

/-- A map `f : α → α` is said to be quasi ergodic with respect to a measure `μ` if it is quasi
measure preserving and pre-ergodic. -/
@[nolint has_nonempty_instance]
structure QuasiErgodic (μ : Measure α := by exact MeasureTheory.MeasureSpace.volume) extends
  QuasiMeasurePreserving f μ μ, PreErgodic f μ : Prop
#align quasi_ergodic QuasiErgodic

variable {f} {μ : Measure α}

namespace PreErgodic

theorem measure_self_or_compl_eq_zero (hf : PreErgodic f μ) (hs : MeasurableSet s) (hs' : f ⁻¹' s = s) :
    μ s = 0 ∨ μ (sᶜ) = 0 := by simpa using hf.ae_empty_or_univ hs hs'
#align pre_ergodic.measure_self_or_compl_eq_zero PreErgodic.measure_self_or_compl_eq_zero

/-- On a probability space, the (pre)ergodicity condition is a zero one law. -/
theorem prob_eq_zero_or_one [IsProbabilityMeasure μ] (hf : PreErgodic f μ) (hs : MeasurableSet s) (hs' : f ⁻¹' s = s) :
    μ s = 0 ∨ μ s = 1 := by simpa [hs] using hf.measure_self_or_compl_eq_zero hs hs'
#align pre_ergodic.prob_eq_zero_or_one PreErgodic.prob_eq_zero_or_one

theorem ofIterate (n : ℕ) (hf : PreErgodic (f^[n]) μ) : PreErgodic f μ :=
  ⟨fun s hs hs' => hf.ae_empty_or_univ hs <| IsFixedPt.preimage_iterate hs' n⟩
#align pre_ergodic.of_iterate PreErgodic.ofIterate

end PreErgodic

namespace Ergodic

/-- An ergodic map is quasi ergodic. -/
theorem quasiErgodic (hf : Ergodic f μ) : QuasiErgodic f μ :=
  { hf.toPreErgodic, hf.toMeasurePreserving.QuasiMeasurePreserving with }
#align ergodic.quasi_ergodic Ergodic.quasiErgodic

end Ergodic

namespace QuasiErgodic

/-- For a quasi ergodic map, sets that are almost invariant (rather than strictly invariant) are
still either almost empty or full. -/
theorem ae_empty_or_univ' (hf : QuasiErgodic f μ) (hs : MeasurableSet s) (hs' : f ⁻¹' s =ᵐ[μ] s) :
    s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ := by
  obtain ⟨t, h₀, h₁, h₂⟩ := hf.to_quasi_measure_preserving.exists_preimage_eq_of_preimage_ae hs hs'
  rcases hf.ae_empty_or_univ h₀ h₂ with (h₃ | h₃) <;> [left, right] <;> exact ae_eq_trans h₁.symm h₃
#align quasi_ergodic.ae_empty_or_univ' QuasiErgodic.ae_empty_or_univ'

end QuasiErgodic

