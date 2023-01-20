/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module dynamics.ergodic.measure_preserving
! leanprover-community/mathlib commit 1126441d6bccf98c81214a0780c73d499f6721fe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Measure.AeMeasurable

/-!
# Measure preserving maps

We say that `f : α → β` is a measure preserving map w.r.t. measures `μ : measure α` and
`ν : measure β` if `f` is measurable and `map f μ = ν`. In this file we define the predicate
`measure_theory.measure_preserving` and prove its basic properties.

We use the term "measure preserving" because in many applications `α = β` and `μ = ν`.

## References

Partially based on
[this](https://www.isa-afp.org/browser_info/current/AFP/Ergodic_Theory/Measure_Preserving_Transformations.html)
Isabelle formalization.

## Tags

measure preserving map, measure
-/


variable {α β γ δ : Type _} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ]

namespace MeasureTheory

open Measure Function Set

variable {μa : Measure α} {μb : Measure β} {μc : Measure γ} {μd : Measure δ}

/-- `f` is a measure preserving map w.r.t. measures `μa` and `μb` if `f` is measurable
and `map f μa = μb`. -/
@[protect_proj]
structure MeasurePreserving (f : α → β)
  (μa : Measure α := by exact MeasureTheory.MeasureSpace.volume)
  (μb : Measure β := by exact MeasureTheory.MeasureSpace.volume) : Prop where
  Measurable : Measurable f
  map_eq : map f μa = μb
#align measure_theory.measure_preserving MeasureTheory.MeasurePreserving

protected theorem Measurable.measurePreserving {f : α → β} (h : Measurable f) (μa : Measure α) :
    MeasurePreserving f μa (map f μa) :=
  ⟨h, rfl⟩
#align measurable.measure_preserving Measurable.measurePreserving

namespace MeasurePreserving

protected theorem id (μ : Measure α) : MeasurePreserving id μ μ :=
  ⟨measurable_id, map_id⟩
#align measure_theory.measure_preserving.id MeasureTheory.MeasurePreserving.id

protected theorem aeMeasurable {f : α → β} (hf : MeasurePreserving f μa μb) : AeMeasurable f μa :=
  hf.1.AeMeasurable
#align measure_theory.measure_preserving.ae_measurable MeasureTheory.MeasurePreserving.aeMeasurable

theorem symm (e : α ≃ᵐ β) {μa : Measure α} {μb : Measure β} (h : MeasurePreserving e μa μb) :
    MeasurePreserving e.symm μb μa :=
  ⟨e.symm.Measurable, by
    rw [← h.map_eq, map_map e.symm.measurable e.measurable, e.symm_comp_self, map_id]⟩
#align measure_theory.measure_preserving.symm MeasureTheory.MeasurePreserving.symm

theorem restrictPreimage {f : α → β} (hf : MeasurePreserving f μa μb) {s : Set β}
    (hs : MeasurableSet s) : MeasurePreserving f (μa.restrict (f ⁻¹' s)) (μb.restrict s) :=
  ⟨hf.Measurable, by rw [← hf.map_eq, restrict_map hf.measurable hs]⟩
#align measure_theory.measure_preserving.restrict_preimage MeasureTheory.MeasurePreserving.restrictPreimage

theorem restrictPreimageEmb {f : α → β} (hf : MeasurePreserving f μa μb)
    (h₂ : MeasurableEmbedding f) (s : Set β) :
    MeasurePreserving f (μa.restrict (f ⁻¹' s)) (μb.restrict s) :=
  ⟨hf.Measurable, by rw [← hf.map_eq, h₂.restrict_map]⟩
#align measure_theory.measure_preserving.restrict_preimage_emb MeasureTheory.MeasurePreserving.restrictPreimageEmb

theorem restrictImageEmb {f : α → β} (hf : MeasurePreserving f μa μb) (h₂ : MeasurableEmbedding f)
    (s : Set α) : MeasurePreserving f (μa.restrict s) (μb.restrict (f '' s)) := by
  simpa only [preimage_image_eq _ h₂.injective] using hf.restrict_preimage_emb h₂ (f '' s)
#align measure_theory.measure_preserving.restrict_image_emb MeasureTheory.MeasurePreserving.restrictImageEmb

theorem ae_measurable_comp_iff {f : α → β} (hf : MeasurePreserving f μa μb)
    (h₂ : MeasurableEmbedding f) {g : β → γ} : AeMeasurable (g ∘ f) μa ↔ AeMeasurable g μb := by
  rw [← hf.map_eq, h₂.ae_measurable_map_iff]
#align measure_theory.measure_preserving.ae_measurable_comp_iff MeasureTheory.MeasurePreserving.ae_measurable_comp_iff

protected theorem quasiMeasurePreserving {f : α → β} (hf : MeasurePreserving f μa μb) :
    QuasiMeasurePreserving f μa μb :=
  ⟨hf.1, hf.2.AbsolutelyContinuous⟩
#align measure_theory.measure_preserving.quasi_measure_preserving MeasureTheory.MeasurePreserving.quasiMeasurePreserving

protected theorem comp {g : β → γ} {f : α → β} (hg : MeasurePreserving g μb μc)
    (hf : MeasurePreserving f μa μb) : MeasurePreserving (g ∘ f) μa μc :=
  ⟨hg.1.comp hf.1, by rw [← map_map hg.1 hf.1, hf.2, hg.2]⟩
#align measure_theory.measure_preserving.comp MeasureTheory.MeasurePreserving.comp

protected theorem comp_left_iff {g : α → β} {e : β ≃ᵐ γ} (h : MeasurePreserving e μb μc) :
    MeasurePreserving (e ∘ g) μa μc ↔ MeasurePreserving g μa μb :=
  by
  refine' ⟨fun hg => _, fun hg => h.comp hg⟩
  convert (measure_preserving.symm e h).comp hg
  simp [← Function.comp.assoc e.symm e g]
#align measure_theory.measure_preserving.comp_left_iff MeasureTheory.MeasurePreserving.comp_left_iff

protected theorem comp_right_iff {g : α → β} {e : γ ≃ᵐ α} (h : MeasurePreserving e μc μa) :
    MeasurePreserving (g ∘ e) μc μb ↔ MeasurePreserving g μa μb :=
  by
  refine' ⟨fun hg => _, fun hg => hg.comp h⟩
  convert hg.comp (measure_preserving.symm e h)
  simp [Function.comp.assoc g e e.symm]
#align measure_theory.measure_preserving.comp_right_iff MeasureTheory.MeasurePreserving.comp_right_iff

protected theorem sigmaFinite {f : α → β} (hf : MeasurePreserving f μa μb) [SigmaFinite μb] :
    SigmaFinite μa :=
  SigmaFinite.ofMap μa hf.AeMeasurable (by rwa [hf.map_eq])
#align measure_theory.measure_preserving.sigma_finite MeasureTheory.MeasurePreserving.sigmaFinite

theorem measure_preimage {f : α → β} (hf : MeasurePreserving f μa μb) {s : Set β}
    (hs : MeasurableSet s) : μa (f ⁻¹' s) = μb s := by rw [← hf.map_eq, map_apply hf.1 hs]
#align measure_theory.measure_preserving.measure_preimage MeasureTheory.MeasurePreserving.measure_preimage

theorem measure_preimage_emb {f : α → β} (hf : MeasurePreserving f μa μb)
    (hfe : MeasurableEmbedding f) (s : Set β) : μa (f ⁻¹' s) = μb s := by
  rw [← hf.map_eq, hfe.map_apply]
#align measure_theory.measure_preserving.measure_preimage_emb MeasureTheory.MeasurePreserving.measure_preimage_emb

protected theorem iterate {f : α → α} (hf : MeasurePreserving f μa μa) :
    ∀ n, MeasurePreserving (f^[n]) μa μa
  | 0 => MeasurePreserving.id μa
  | n + 1 => (iterate n).comp hf
#align measure_theory.measure_preserving.iterate MeasureTheory.MeasurePreserving.iterate

variable {μ : Measure α} {f : α → α} {s : Set α}

/-- If `μ univ < n * μ s` and `f` is a map preserving measure `μ`,
then for some `x ∈ s` and `0 < m < n`, `f^[m] x ∈ s`. -/
theorem exists_mem_image_mem_of_volume_lt_mul_volume (hf : MeasurePreserving f μ μ)
    (hs : MeasurableSet s) {n : ℕ} (hvol : μ (univ : Set α) < n * μ s) :
    ∃ x ∈ s, ∃ m ∈ Ioo 0 n, (f^[m]) x ∈ s :=
  by
  have A : ∀ m, MeasurableSet (f^[m] ⁻¹' s) := fun m => (hf.iterate m).Measurable hs
  have B : ∀ m, μ (f^[m] ⁻¹' s) = μ s := fun m => (hf.iterate m).measure_preimage hs
  have : μ (univ : Set α) < (Finset.range n).Sum fun m => μ (f^[m] ⁻¹' s) := by
    simpa only [B, nsmul_eq_mul, Finset.sum_const, Finset.card_range]
  rcases exists_nonempty_inter_of_measure_univ_lt_sum_measure μ (fun m hm => A m) this with
    ⟨i, hi, j, hj, hij, x, hxi, hxj⟩
  -- without `tactic.skip` Lean closes the extra goal but it takes a long time; not sure why
  wlog (discharger := tactic.skip) hlt : i < j := hij.lt_or_lt using i j, j i
  · simp only [Set.mem_preimage, Finset.mem_range] at hi hj hxi hxj
    refine' ⟨(f^[i]) x, hxi, j - i, ⟨tsub_pos_of_lt hlt, lt_of_le_of_lt (j.sub_le i) hj⟩, _⟩
    rwa [← iterate_add_apply, tsub_add_cancel_of_le hlt.le]
  · exact fun hi hj hij hxi hxj => this hj hi hij.symm hxj hxi
#align measure_theory.measure_preserving.exists_mem_image_mem_of_volume_lt_mul_volume MeasureTheory.MeasurePreserving.exists_mem_image_mem_of_volume_lt_mul_volume

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (m «expr ≠ » 0) -/
/-- A self-map preserving a finite measure is conservative: if `μ s ≠ 0`, then at least one point
`x ∈ s` comes back to `s` under iterations of `f`. Actually, a.e. point of `s` comes back to `s`
infinitely many times, see `measure_theory.measure_preserving.conservative` and theorems about
`measure_theory.conservative`. -/
theorem exists_mem_image_mem [IsFiniteMeasure μ] (hf : MeasurePreserving f μ μ)
    (hs : MeasurableSet s) (hs' : μ s ≠ 0) : ∃ x ∈ s, ∃ (m : _)(_ : m ≠ 0), (f^[m]) x ∈ s :=
  by
  rcases Ennreal.exists_nat_mul_gt hs' (measure_ne_top μ (univ : Set α)) with ⟨N, hN⟩
  rcases hf.exists_mem_image_mem_of_volume_lt_mul_volume hs hN with ⟨x, hx, m, hm, hmx⟩
  exact ⟨x, hx, m, hm.1.ne', hmx⟩
#align measure_theory.measure_preserving.exists_mem_image_mem MeasureTheory.MeasurePreserving.exists_mem_image_mem

end MeasurePreserving

namespace MeasurableEquiv

theorem measurePreservingSymm (μ : Measure α) (e : α ≃ᵐ β) : MeasurePreserving e.symm (map e μ) μ :=
  (e.Measurable.MeasurePreserving μ).symm _
#align measure_theory.measurable_equiv.measure_preserving_symm MeasureTheory.MeasurableEquiv.measurePreservingSymm

end MeasurableEquiv

end MeasureTheory

