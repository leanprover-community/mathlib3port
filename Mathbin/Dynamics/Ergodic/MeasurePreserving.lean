/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module dynamics.ergodic.measure_preserving
! leanprover-community/mathlib commit 781cb2eed038c4caf53bdbd8d20a95e5822d77df
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Measure.AeMeasurable

/-!
# Measure preserving maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

#print MeasureTheory.MeasurePreserving /-
/-- `f` is a measure preserving map w.r.t. measures `μa` and `μb` if `f` is measurable
and `map f μa = μb`. -/
@[protect_proj]
structure MeasurePreserving (f : α → β)
  (μa : Measure α := by exact MeasureTheory.MeasureSpace.volume)
  (μb : Measure β := by exact MeasureTheory.MeasureSpace.volume) : Prop where
  Measurable : Measurable f
  map_eq : map f μa = μb
#align measure_theory.measure_preserving MeasureTheory.MeasurePreserving
-/

/- warning: measurable.measure_preserving -> Measurable.measurePreserving is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] {f : α -> β}, (Measurable.{u1, u2} α β _inst_1 _inst_2 f) -> (forall (μa : MeasureTheory.Measure.{u1} α _inst_1), MeasureTheory.MeasurePreserving.{u1, u2} α β _inst_1 _inst_2 f μa (MeasureTheory.Measure.map.{u1, u2} α β _inst_2 _inst_1 f μa))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] {f : α -> β}, (Measurable.{u2, u1} α β _inst_1 _inst_2 f) -> (forall (μa : MeasureTheory.Measure.{u2} α _inst_1), MeasureTheory.MeasurePreserving.{u2, u1} α β _inst_1 _inst_2 f μa (MeasureTheory.Measure.map.{u2, u1} α β _inst_2 _inst_1 f μa))
Case conversion may be inaccurate. Consider using '#align measurable.measure_preserving Measurable.measurePreservingₓ'. -/
protected theorem Measurable.measurePreserving {f : α → β} (h : Measurable f) (μa : Measure α) :
    MeasurePreserving f μa (map f μa) :=
  ⟨h, rfl⟩
#align measurable.measure_preserving Measurable.measurePreserving

namespace MeasurePreserving

#print MeasureTheory.MeasurePreserving.id /-
protected theorem id (μ : Measure α) : MeasurePreserving id μ μ :=
  ⟨measurable_id, map_id⟩
#align measure_theory.measure_preserving.id MeasureTheory.MeasurePreserving.id
-/

/- warning: measure_theory.measure_preserving.ae_measurable -> MeasureTheory.MeasurePreserving.aemeasurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] {μa : MeasureTheory.Measure.{u1} α _inst_1} {μb : MeasureTheory.Measure.{u2} β _inst_2} {f : α -> β}, (MeasureTheory.MeasurePreserving.{u1, u2} α β _inst_1 _inst_2 f μa μb) -> (AEMeasurable.{u1, u2} α β _inst_2 _inst_1 f μa)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] {μa : MeasureTheory.Measure.{u2} α _inst_1} {μb : MeasureTheory.Measure.{u1} β _inst_2} {f : α -> β}, (MeasureTheory.MeasurePreserving.{u2, u1} α β _inst_1 _inst_2 f μa μb) -> (AEMeasurable.{u2, u1} α β _inst_2 _inst_1 f μa)
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_preserving.ae_measurable MeasureTheory.MeasurePreserving.aemeasurableₓ'. -/
protected theorem aemeasurable {f : α → β} (hf : MeasurePreserving f μa μb) : AEMeasurable f μa :=
  hf.1.AEMeasurable
#align measure_theory.measure_preserving.ae_measurable MeasureTheory.MeasurePreserving.aemeasurable

/- warning: measure_theory.measure_preserving.symm -> MeasureTheory.MeasurePreserving.symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] (e : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) {μa : MeasureTheory.Measure.{u1} α _inst_1} {μb : MeasureTheory.Measure.{u2} β _inst_2}, (MeasureTheory.MeasurePreserving.{u1, u2} α β _inst_1 _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (MeasurableEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) μa μb) -> (MeasureTheory.MeasurePreserving.{u2, u1} β α _inst_2 _inst_1 (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MeasurableEquiv.{u2, u1} β α _inst_2 _inst_1) (fun (_x : MeasurableEquiv.{u2, u1} β α _inst_2 _inst_1) => β -> α) (MeasurableEquiv.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (MeasurableEquiv.symm.{u1, u2} α β _inst_1 _inst_2 e)) μb μa)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] (e : MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) {μa : MeasureTheory.Measure.{u2} α _inst_1} {μb : MeasureTheory.Measure.{u1} β _inst_2}, (MeasureTheory.MeasurePreserving.{u2, u1} α β _inst_1 _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (MeasurableEquiv.instEquivLike.{u2, u1} α β _inst_1 _inst_2))) e) μa μb) -> (MeasureTheory.MeasurePreserving.{u1, u2} β α _inst_2 _inst_1 (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α _inst_2 _inst_1) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α _inst_2 _inst_1) β α (MeasurableEquiv.instEquivLike.{u1, u2} β α _inst_2 _inst_1))) (MeasurableEquiv.symm.{u2, u1} α β _inst_1 _inst_2 e)) μb μa)
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_preserving.symm MeasureTheory.MeasurePreserving.symmₓ'. -/
theorem symm (e : α ≃ᵐ β) {μa : Measure α} {μb : Measure β} (h : MeasurePreserving e μa μb) :
    MeasurePreserving e.symm μb μa :=
  ⟨e.symm.Measurable, by
    rw [← h.map_eq, map_map e.symm.measurable e.measurable, e.symm_comp_self, map_id]⟩
#align measure_theory.measure_preserving.symm MeasureTheory.MeasurePreserving.symm

/- warning: measure_theory.measure_preserving.restrict_preimage -> MeasureTheory.MeasurePreserving.restrict_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] {μa : MeasureTheory.Measure.{u1} α _inst_1} {μb : MeasureTheory.Measure.{u2} β _inst_2} {f : α -> β}, (MeasureTheory.MeasurePreserving.{u1, u2} α β _inst_1 _inst_2 f μa μb) -> (forall {s : Set.{u2} β}, (MeasurableSet.{u2} β _inst_2 s) -> (MeasureTheory.MeasurePreserving.{u1, u2} α β _inst_1 _inst_2 f (MeasureTheory.Measure.restrict.{u1} α _inst_1 μa (Set.preimage.{u1, u2} α β f s)) (MeasureTheory.Measure.restrict.{u2} β _inst_2 μb s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] {μa : MeasureTheory.Measure.{u2} α _inst_1} {μb : MeasureTheory.Measure.{u1} β _inst_2} {f : α -> β}, (MeasureTheory.MeasurePreserving.{u2, u1} α β _inst_1 _inst_2 f μa μb) -> (forall {s : Set.{u1} β}, (MeasurableSet.{u1} β _inst_2 s) -> (MeasureTheory.MeasurePreserving.{u2, u1} α β _inst_1 _inst_2 f (MeasureTheory.Measure.restrict.{u2} α _inst_1 μa (Set.preimage.{u2, u1} α β f s)) (MeasureTheory.Measure.restrict.{u1} β _inst_2 μb s)))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_preserving.restrict_preimage MeasureTheory.MeasurePreserving.restrict_preimageₓ'. -/
theorem restrict_preimage {f : α → β} (hf : MeasurePreserving f μa μb) {s : Set β}
    (hs : MeasurableSet s) : MeasurePreserving f (μa.restrict (f ⁻¹' s)) (μb.restrict s) :=
  ⟨hf.Measurable, by rw [← hf.map_eq, restrict_map hf.measurable hs]⟩
#align measure_theory.measure_preserving.restrict_preimage MeasureTheory.MeasurePreserving.restrict_preimage

/- warning: measure_theory.measure_preserving.restrict_preimage_emb -> MeasureTheory.MeasurePreserving.restrict_preimage_emb is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] {μa : MeasureTheory.Measure.{u1} α _inst_1} {μb : MeasureTheory.Measure.{u2} β _inst_2} {f : α -> β}, (MeasureTheory.MeasurePreserving.{u1, u2} α β _inst_1 _inst_2 f μa μb) -> (MeasurableEmbedding.{u1, u2} α β _inst_1 _inst_2 f) -> (forall (s : Set.{u2} β), MeasureTheory.MeasurePreserving.{u1, u2} α β _inst_1 _inst_2 f (MeasureTheory.Measure.restrict.{u1} α _inst_1 μa (Set.preimage.{u1, u2} α β f s)) (MeasureTheory.Measure.restrict.{u2} β _inst_2 μb s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] {μa : MeasureTheory.Measure.{u2} α _inst_1} {μb : MeasureTheory.Measure.{u1} β _inst_2} {f : α -> β}, (MeasureTheory.MeasurePreserving.{u2, u1} α β _inst_1 _inst_2 f μa μb) -> (MeasurableEmbedding.{u2, u1} α β _inst_1 _inst_2 f) -> (forall (s : Set.{u1} β), MeasureTheory.MeasurePreserving.{u2, u1} α β _inst_1 _inst_2 f (MeasureTheory.Measure.restrict.{u2} α _inst_1 μa (Set.preimage.{u2, u1} α β f s)) (MeasureTheory.Measure.restrict.{u1} β _inst_2 μb s))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_preserving.restrict_preimage_emb MeasureTheory.MeasurePreserving.restrict_preimage_embₓ'. -/
theorem restrict_preimage_emb {f : α → β} (hf : MeasurePreserving f μa μb)
    (h₂ : MeasurableEmbedding f) (s : Set β) :
    MeasurePreserving f (μa.restrict (f ⁻¹' s)) (μb.restrict s) :=
  ⟨hf.Measurable, by rw [← hf.map_eq, h₂.restrict_map]⟩
#align measure_theory.measure_preserving.restrict_preimage_emb MeasureTheory.MeasurePreserving.restrict_preimage_emb

/- warning: measure_theory.measure_preserving.restrict_image_emb -> MeasureTheory.MeasurePreserving.restrict_image_emb is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] {μa : MeasureTheory.Measure.{u1} α _inst_1} {μb : MeasureTheory.Measure.{u2} β _inst_2} {f : α -> β}, (MeasureTheory.MeasurePreserving.{u1, u2} α β _inst_1 _inst_2 f μa μb) -> (MeasurableEmbedding.{u1, u2} α β _inst_1 _inst_2 f) -> (forall (s : Set.{u1} α), MeasureTheory.MeasurePreserving.{u1, u2} α β _inst_1 _inst_2 f (MeasureTheory.Measure.restrict.{u1} α _inst_1 μa s) (MeasureTheory.Measure.restrict.{u2} β _inst_2 μb (Set.image.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] {μa : MeasureTheory.Measure.{u2} α _inst_1} {μb : MeasureTheory.Measure.{u1} β _inst_2} {f : α -> β}, (MeasureTheory.MeasurePreserving.{u2, u1} α β _inst_1 _inst_2 f μa μb) -> (MeasurableEmbedding.{u2, u1} α β _inst_1 _inst_2 f) -> (forall (s : Set.{u2} α), MeasureTheory.MeasurePreserving.{u2, u1} α β _inst_1 _inst_2 f (MeasureTheory.Measure.restrict.{u2} α _inst_1 μa s) (MeasureTheory.Measure.restrict.{u1} β _inst_2 μb (Set.image.{u2, u1} α β f s)))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_preserving.restrict_image_emb MeasureTheory.MeasurePreserving.restrict_image_embₓ'. -/
theorem restrict_image_emb {f : α → β} (hf : MeasurePreserving f μa μb) (h₂ : MeasurableEmbedding f)
    (s : Set α) : MeasurePreserving f (μa.restrict s) (μb.restrict (f '' s)) := by
  simpa only [preimage_image_eq _ h₂.injective] using hf.restrict_preimage_emb h₂ (f '' s)
#align measure_theory.measure_preserving.restrict_image_emb MeasureTheory.MeasurePreserving.restrict_image_emb

/- warning: measure_theory.measure_preserving.ae_measurable_comp_iff -> MeasureTheory.MeasurePreserving.aemeasurable_comp_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] [_inst_3 : MeasurableSpace.{u3} γ] {μa : MeasureTheory.Measure.{u1} α _inst_1} {μb : MeasureTheory.Measure.{u2} β _inst_2} {f : α -> β}, (MeasureTheory.MeasurePreserving.{u1, u2} α β _inst_1 _inst_2 f μa μb) -> (MeasurableEmbedding.{u1, u2} α β _inst_1 _inst_2 f) -> (forall {g : β -> γ}, Iff (AEMeasurable.{u1, u3} α γ _inst_3 _inst_1 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) μa) (AEMeasurable.{u2, u3} β γ _inst_3 _inst_2 g μb))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u3} α] [_inst_2 : MeasurableSpace.{u2} β] [_inst_3 : MeasurableSpace.{u1} γ] {μa : MeasureTheory.Measure.{u3} α _inst_1} {μb : MeasureTheory.Measure.{u2} β _inst_2} {f : α -> β}, (MeasureTheory.MeasurePreserving.{u3, u2} α β _inst_1 _inst_2 f μa μb) -> (MeasurableEmbedding.{u3, u2} α β _inst_1 _inst_2 f) -> (forall {g : β -> γ}, Iff (AEMeasurable.{u3, u1} α γ _inst_3 _inst_1 (Function.comp.{succ u3, succ u2, succ u1} α β γ g f) μa) (AEMeasurable.{u2, u1} β γ _inst_3 _inst_2 g μb))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_preserving.ae_measurable_comp_iff MeasureTheory.MeasurePreserving.aemeasurable_comp_iffₓ'. -/
theorem aemeasurable_comp_iff {f : α → β} (hf : MeasurePreserving f μa μb)
    (h₂ : MeasurableEmbedding f) {g : β → γ} : AEMeasurable (g ∘ f) μa ↔ AEMeasurable g μb := by
  rw [← hf.map_eq, h₂.ae_measurable_map_iff]
#align measure_theory.measure_preserving.ae_measurable_comp_iff MeasureTheory.MeasurePreserving.aemeasurable_comp_iff

/- warning: measure_theory.measure_preserving.quasi_measure_preserving -> MeasureTheory.MeasurePreserving.quasiMeasurePreserving is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] {μa : MeasureTheory.Measure.{u1} α _inst_1} {μb : MeasureTheory.Measure.{u2} β _inst_2} {f : α -> β}, (MeasureTheory.MeasurePreserving.{u1, u2} α β _inst_1 _inst_2 f μa μb) -> (MeasureTheory.Measure.QuasiMeasurePreserving.{u1, u2} α β _inst_2 _inst_1 f μa μb)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] {μa : MeasureTheory.Measure.{u2} α _inst_1} {μb : MeasureTheory.Measure.{u1} β _inst_2} {f : α -> β}, (MeasureTheory.MeasurePreserving.{u2, u1} α β _inst_1 _inst_2 f μa μb) -> (MeasureTheory.Measure.QuasiMeasurePreserving.{u2, u1} α β _inst_2 _inst_1 f μa μb)
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_preserving.quasi_measure_preserving MeasureTheory.MeasurePreserving.quasiMeasurePreservingₓ'. -/
protected theorem quasiMeasurePreserving {f : α → β} (hf : MeasurePreserving f μa μb) :
    QuasiMeasurePreserving f μa μb :=
  ⟨hf.1, hf.2.AbsolutelyContinuous⟩
#align measure_theory.measure_preserving.quasi_measure_preserving MeasureTheory.MeasurePreserving.quasiMeasurePreserving

/- warning: measure_theory.measure_preserving.comp -> MeasureTheory.MeasurePreserving.comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] [_inst_3 : MeasurableSpace.{u3} γ] {μa : MeasureTheory.Measure.{u1} α _inst_1} {μb : MeasureTheory.Measure.{u2} β _inst_2} {μc : MeasureTheory.Measure.{u3} γ _inst_3} {g : β -> γ} {f : α -> β}, (MeasureTheory.MeasurePreserving.{u2, u3} β γ _inst_2 _inst_3 g μb μc) -> (MeasureTheory.MeasurePreserving.{u1, u2} α β _inst_1 _inst_2 f μa μb) -> (MeasureTheory.MeasurePreserving.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) μa μc)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u3} β] [_inst_3 : MeasurableSpace.{u2} γ] {μa : MeasureTheory.Measure.{u1} α _inst_1} {μb : MeasureTheory.Measure.{u3} β _inst_2} {μc : MeasureTheory.Measure.{u2} γ _inst_3} {g : β -> γ} {f : α -> β}, (MeasureTheory.MeasurePreserving.{u3, u2} β γ _inst_2 _inst_3 g μb μc) -> (MeasureTheory.MeasurePreserving.{u1, u3} α β _inst_1 _inst_2 f μa μb) -> (MeasureTheory.MeasurePreserving.{u1, u2} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u3, succ u2} α β γ g f) μa μc)
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_preserving.comp MeasureTheory.MeasurePreserving.compₓ'. -/
protected theorem comp {g : β → γ} {f : α → β} (hg : MeasurePreserving g μb μc)
    (hf : MeasurePreserving f μa μb) : MeasurePreserving (g ∘ f) μa μc :=
  ⟨hg.1.comp hf.1, by rw [← map_map hg.1 hf.1, hf.2, hg.2]⟩
#align measure_theory.measure_preserving.comp MeasureTheory.MeasurePreserving.comp

/- warning: measure_theory.measure_preserving.comp_left_iff -> MeasureTheory.MeasurePreserving.comp_left_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] [_inst_3 : MeasurableSpace.{u3} γ] {μa : MeasureTheory.Measure.{u1} α _inst_1} {μb : MeasureTheory.Measure.{u2} β _inst_2} {μc : MeasureTheory.Measure.{u3} γ _inst_3} {g : α -> β} {e : MeasurableEquiv.{u2, u3} β γ _inst_2 _inst_3}, (MeasureTheory.MeasurePreserving.{u2, u3} β γ _inst_2 _inst_3 (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (MeasurableEquiv.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : MeasurableEquiv.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (MeasurableEquiv.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) e) μb μc) -> (Iff (MeasureTheory.MeasurePreserving.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (MeasurableEquiv.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : MeasurableEquiv.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (MeasurableEquiv.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) e) g) μa μc) (MeasureTheory.MeasurePreserving.{u1, u2} α β _inst_1 _inst_2 g μa μb))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u3} β] [_inst_3 : MeasurableSpace.{u2} γ] {μa : MeasureTheory.Measure.{u1} α _inst_1} {μb : MeasureTheory.Measure.{u3} β _inst_2} {μc : MeasureTheory.Measure.{u2} γ _inst_3} {g : α -> β} {e : MeasurableEquiv.{u3, u2} β γ _inst_2 _inst_3}, (MeasureTheory.MeasurePreserving.{u3, u2} β γ _inst_2 _inst_3 (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MeasurableEquiv.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (MeasurableEquiv.{u3, u2} β γ _inst_2 _inst_3) β γ (EquivLike.toEmbeddingLike.{max (succ u3) (succ u2), succ u3, succ u2} (MeasurableEquiv.{u3, u2} β γ _inst_2 _inst_3) β γ (MeasurableEquiv.instEquivLike.{u3, u2} β γ _inst_2 _inst_3))) e) μb μc) -> (Iff (MeasureTheory.MeasurePreserving.{u1, u2} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u3, succ u2} α β γ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MeasurableEquiv.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (MeasurableEquiv.{u3, u2} β γ _inst_2 _inst_3) β γ (EquivLike.toEmbeddingLike.{max (succ u3) (succ u2), succ u3, succ u2} (MeasurableEquiv.{u3, u2} β γ _inst_2 _inst_3) β γ (MeasurableEquiv.instEquivLike.{u3, u2} β γ _inst_2 _inst_3))) e) g) μa μc) (MeasureTheory.MeasurePreserving.{u1, u3} α β _inst_1 _inst_2 g μa μb))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_preserving.comp_left_iff MeasureTheory.MeasurePreserving.comp_left_iffₓ'. -/
protected theorem comp_left_iff {g : α → β} {e : β ≃ᵐ γ} (h : MeasurePreserving e μb μc) :
    MeasurePreserving (e ∘ g) μa μc ↔ MeasurePreserving g μa μb :=
  by
  refine' ⟨fun hg => _, fun hg => h.comp hg⟩
  convert(measure_preserving.symm e h).comp hg
  simp [← Function.comp.assoc e.symm e g]
#align measure_theory.measure_preserving.comp_left_iff MeasureTheory.MeasurePreserving.comp_left_iff

/- warning: measure_theory.measure_preserving.comp_right_iff -> MeasureTheory.MeasurePreserving.comp_right_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] [_inst_3 : MeasurableSpace.{u3} γ] {μa : MeasureTheory.Measure.{u1} α _inst_1} {μb : MeasureTheory.Measure.{u2} β _inst_2} {μc : MeasureTheory.Measure.{u3} γ _inst_3} {g : α -> β} {e : MeasurableEquiv.{u3, u1} γ α _inst_3 _inst_1}, (MeasureTheory.MeasurePreserving.{u3, u1} γ α _inst_3 _inst_1 (coeFn.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (MeasurableEquiv.{u3, u1} γ α _inst_3 _inst_1) (fun (_x : MeasurableEquiv.{u3, u1} γ α _inst_3 _inst_1) => γ -> α) (MeasurableEquiv.hasCoeToFun.{u3, u1} γ α _inst_3 _inst_1) e) μc μa) -> (Iff (MeasureTheory.MeasurePreserving.{u3, u2} γ β _inst_3 _inst_2 (Function.comp.{succ u3, succ u1, succ u2} γ α β g (coeFn.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (MeasurableEquiv.{u3, u1} γ α _inst_3 _inst_1) (fun (_x : MeasurableEquiv.{u3, u1} γ α _inst_3 _inst_1) => γ -> α) (MeasurableEquiv.hasCoeToFun.{u3, u1} γ α _inst_3 _inst_1) e)) μc μb) (MeasureTheory.MeasurePreserving.{u1, u2} α β _inst_1 _inst_2 g μa μb))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] [_inst_3 : MeasurableSpace.{u3} γ] {μa : MeasureTheory.Measure.{u2} α _inst_1} {μb : MeasureTheory.Measure.{u1} β _inst_2} {μc : MeasureTheory.Measure.{u3} γ _inst_3} {g : α -> β} {e : MeasurableEquiv.{u3, u2} γ α _inst_3 _inst_1}, (MeasureTheory.MeasurePreserving.{u3, u2} γ α _inst_3 _inst_1 (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (MeasurableEquiv.{u3, u2} γ α _inst_3 _inst_1) γ (fun (_x : γ) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : γ) => α) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u3), succ u3, succ u2} (MeasurableEquiv.{u3, u2} γ α _inst_3 _inst_1) γ α (EquivLike.toEmbeddingLike.{max (succ u2) (succ u3), succ u3, succ u2} (MeasurableEquiv.{u3, u2} γ α _inst_3 _inst_1) γ α (MeasurableEquiv.instEquivLike.{u3, u2} γ α _inst_3 _inst_1))) e) μc μa) -> (Iff (MeasureTheory.MeasurePreserving.{u3, u1} γ β _inst_3 _inst_2 (Function.comp.{succ u3, succ u2, succ u1} γ α β g (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (MeasurableEquiv.{u3, u2} γ α _inst_3 _inst_1) γ (fun (_x : γ) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : γ) => α) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u3), succ u3, succ u2} (MeasurableEquiv.{u3, u2} γ α _inst_3 _inst_1) γ α (EquivLike.toEmbeddingLike.{max (succ u2) (succ u3), succ u3, succ u2} (MeasurableEquiv.{u3, u2} γ α _inst_3 _inst_1) γ α (MeasurableEquiv.instEquivLike.{u3, u2} γ α _inst_3 _inst_1))) e)) μc μb) (MeasureTheory.MeasurePreserving.{u2, u1} α β _inst_1 _inst_2 g μa μb))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_preserving.comp_right_iff MeasureTheory.MeasurePreserving.comp_right_iffₓ'. -/
protected theorem comp_right_iff {g : α → β} {e : γ ≃ᵐ α} (h : MeasurePreserving e μc μa) :
    MeasurePreserving (g ∘ e) μc μb ↔ MeasurePreserving g μa μb :=
  by
  refine' ⟨fun hg => _, fun hg => hg.comp h⟩
  convert hg.comp (measure_preserving.symm e h)
  simp [Function.comp.assoc g e e.symm]
#align measure_theory.measure_preserving.comp_right_iff MeasureTheory.MeasurePreserving.comp_right_iff

/- warning: measure_theory.measure_preserving.sigma_finite -> MeasureTheory.MeasurePreserving.sigmaFinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] {μa : MeasureTheory.Measure.{u1} α _inst_1} {μb : MeasureTheory.Measure.{u2} β _inst_2} {f : α -> β}, (MeasureTheory.MeasurePreserving.{u1, u2} α β _inst_1 _inst_2 f μa μb) -> (forall [_inst_5 : MeasureTheory.SigmaFinite.{u2} β _inst_2 μb], MeasureTheory.SigmaFinite.{u1} α _inst_1 μa)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] {μa : MeasureTheory.Measure.{u2} α _inst_1} {μb : MeasureTheory.Measure.{u1} β _inst_2} {f : α -> β}, (MeasureTheory.MeasurePreserving.{u2, u1} α β _inst_1 _inst_2 f μa μb) -> (forall [_inst_5 : MeasureTheory.SigmaFinite.{u1} β _inst_2 μb], MeasureTheory.SigmaFinite.{u2} α _inst_1 μa)
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_preserving.sigma_finite MeasureTheory.MeasurePreserving.sigmaFiniteₓ'. -/
protected theorem sigmaFinite {f : α → β} (hf : MeasurePreserving f μa μb) [SigmaFinite μb] :
    SigmaFinite μa :=
  SigmaFinite.of_map μa hf.AEMeasurable (by rwa [hf.map_eq])
#align measure_theory.measure_preserving.sigma_finite MeasureTheory.MeasurePreserving.sigmaFinite

/- warning: measure_theory.measure_preserving.measure_preimage -> MeasureTheory.MeasurePreserving.measure_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] {μa : MeasureTheory.Measure.{u1} α _inst_1} {μb : MeasureTheory.Measure.{u2} β _inst_2} {f : α -> β}, (MeasureTheory.MeasurePreserving.{u1, u2} α β _inst_1 _inst_2 f μa μb) -> (forall {s : Set.{u2} β}, (MeasurableSet.{u2} β _inst_2 s) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μa (Set.preimage.{u1, u2} α β f s)) (coeFn.{succ u2, succ u2} (MeasureTheory.Measure.{u2} β _inst_2) (fun (_x : MeasureTheory.Measure.{u2} β _inst_2) => (Set.{u2} β) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u2} β _inst_2) μb s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] {μa : MeasureTheory.Measure.{u2} α _inst_1} {μb : MeasureTheory.Measure.{u1} β _inst_2} {f : α -> β}, (MeasureTheory.MeasurePreserving.{u2, u1} α β _inst_1 _inst_2 f μa μb) -> (forall {s : Set.{u1} β}, (MeasurableSet.{u1} β _inst_2 s) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u2} α (MeasureTheory.Measure.toOuterMeasure.{u2} α _inst_1 μa) (Set.preimage.{u2, u1} α β f s)) (MeasureTheory.OuterMeasure.measureOf.{u1} β (MeasureTheory.Measure.toOuterMeasure.{u1} β _inst_2 μb) s)))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_preserving.measure_preimage MeasureTheory.MeasurePreserving.measure_preimageₓ'. -/
theorem measure_preimage {f : α → β} (hf : MeasurePreserving f μa μb) {s : Set β}
    (hs : MeasurableSet s) : μa (f ⁻¹' s) = μb s := by rw [← hf.map_eq, map_apply hf.1 hs]
#align measure_theory.measure_preserving.measure_preimage MeasureTheory.MeasurePreserving.measure_preimage

/- warning: measure_theory.measure_preserving.measure_preimage_emb -> MeasureTheory.MeasurePreserving.measure_preimage_emb is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] {μa : MeasureTheory.Measure.{u1} α _inst_1} {μb : MeasureTheory.Measure.{u2} β _inst_2} {f : α -> β}, (MeasureTheory.MeasurePreserving.{u1, u2} α β _inst_1 _inst_2 f μa μb) -> (MeasurableEmbedding.{u1, u2} α β _inst_1 _inst_2 f) -> (forall (s : Set.{u2} β), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μa (Set.preimage.{u1, u2} α β f s)) (coeFn.{succ u2, succ u2} (MeasureTheory.Measure.{u2} β _inst_2) (fun (_x : MeasureTheory.Measure.{u2} β _inst_2) => (Set.{u2} β) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u2} β _inst_2) μb s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] {μa : MeasureTheory.Measure.{u2} α _inst_1} {μb : MeasureTheory.Measure.{u1} β _inst_2} {f : α -> β}, (MeasureTheory.MeasurePreserving.{u2, u1} α β _inst_1 _inst_2 f μa μb) -> (MeasurableEmbedding.{u2, u1} α β _inst_1 _inst_2 f) -> (forall (s : Set.{u1} β), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u2} α (MeasureTheory.Measure.toOuterMeasure.{u2} α _inst_1 μa) (Set.preimage.{u2, u1} α β f s)) (MeasureTheory.OuterMeasure.measureOf.{u1} β (MeasureTheory.Measure.toOuterMeasure.{u1} β _inst_2 μb) s))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_preserving.measure_preimage_emb MeasureTheory.MeasurePreserving.measure_preimage_embₓ'. -/
theorem measure_preimage_emb {f : α → β} (hf : MeasurePreserving f μa μb)
    (hfe : MeasurableEmbedding f) (s : Set β) : μa (f ⁻¹' s) = μb s := by
  rw [← hf.map_eq, hfe.map_apply]
#align measure_theory.measure_preserving.measure_preimage_emb MeasureTheory.MeasurePreserving.measure_preimage_emb

#print MeasureTheory.MeasurePreserving.iterate /-
protected theorem iterate {f : α → α} (hf : MeasurePreserving f μa μa) :
    ∀ n, MeasurePreserving (f^[n]) μa μa
  | 0 => MeasurePreserving.id μa
  | n + 1 => (iterate n).comp hf
#align measure_theory.measure_preserving.iterate MeasureTheory.MeasurePreserving.iterate
-/

variable {μ : Measure α} {f : α → α} {s : Set α}

/- warning: measure_theory.measure_preserving.exists_mem_image_mem_of_volume_lt_mul_volume -> MeasureTheory.MeasurePreserving.exists_mem_image_mem_of_volume_lt_mul_volume is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {f : α -> α} {s : Set.{u1} α}, (MeasureTheory.MeasurePreserving.{u1, u1} α α _inst_1 _inst_1 f μ μ) -> (MeasurableSet.{u1} α _inst_1 s) -> (forall {n : Nat}, (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (Set.univ.{u1} α)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat ENNReal (HasLiftT.mk.{1, 1} Nat ENNReal (CoeTCₓ.coe.{1, 1} Nat ENNReal (Nat.castCoe.{0} ENNReal (AddMonoidWithOne.toNatCast.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))) n) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s))) -> (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => Exists.{1} Nat (fun (m : Nat) => Exists.{0} (Membership.Mem.{0, 0} Nat (Set.{0} Nat) (Set.hasMem.{0} Nat) m (Set.Ioo.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n)) (fun (H : Membership.Mem.{0, 0} Nat (Set.{0} Nat) (Set.hasMem.{0} Nat) m (Set.Ioo.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n)) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Nat.iterate.{succ u1} α f m x) s))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {f : α -> α} {s : Set.{u1} α}, (MeasureTheory.MeasurePreserving.{u1, u1} α α _inst_1 _inst_1 f μ μ) -> (MeasurableSet.{u1} α _inst_1 s) -> (forall {n : Nat}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (Set.univ.{u1} α)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (Nat.cast.{0} ENNReal (CanonicallyOrderedCommSemiring.toNatCast.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) n) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s))) -> (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (Exists.{1} Nat (fun (m : Nat) => And (Membership.mem.{0, 0} Nat (Set.{0} Nat) (Set.instMembershipSet.{0} Nat) m (Set.Ioo.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n)) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (Nat.iterate.{succ u1} α f m x) s))))))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_preserving.exists_mem_image_mem_of_volume_lt_mul_volume MeasureTheory.MeasurePreserving.exists_mem_image_mem_of_volume_lt_mul_volumeₓ'. -/
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
  wlog hlt : i < j generalizing i j
  · exact this j hj i hi hij.symm hxj hxi (hij.lt_or_lt.resolve_left hlt)
  simp only [Set.mem_preimage, Finset.mem_range] at hi hj hxi hxj
  refine' ⟨(f^[i]) x, hxi, j - i, ⟨tsub_pos_of_lt hlt, lt_of_le_of_lt (j.sub_le i) hj⟩, _⟩
  rwa [← iterate_add_apply, tsub_add_cancel_of_le hlt.le]
#align measure_theory.measure_preserving.exists_mem_image_mem_of_volume_lt_mul_volume MeasureTheory.MeasurePreserving.exists_mem_image_mem_of_volume_lt_mul_volume

/- warning: measure_theory.measure_preserving.exists_mem_image_mem -> MeasureTheory.MeasurePreserving.exists_mem_image_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {f : α -> α} {s : Set.{u1} α} [_inst_5 : MeasureTheory.FiniteMeasure.{u1} α _inst_1 μ], (MeasureTheory.MeasurePreserving.{u1, u1} α α _inst_1 _inst_1 f μ μ) -> (MeasurableSet.{u1} α _inst_1 s) -> (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => Exists.{1} Nat (fun (m : Nat) => Exists.{0} (Ne.{1} Nat m (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (fun (H : Ne.{1} Nat m (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Nat.iterate.{succ u1} α f m x) s)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {f : α -> α} {s : Set.{u1} α} [_inst_5 : MeasureTheory.FiniteMeasure.{u1} α _inst_1 μ], (MeasureTheory.MeasurePreserving.{u1, u1} α α _inst_1 _inst_1 f μ μ) -> (MeasurableSet.{u1} α _inst_1 s) -> (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (Exists.{1} Nat (fun (m : Nat) => Exists.{0} (Ne.{1} Nat m (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (fun (x._@.Mathlib.Dynamics.Ergodic.MeasurePreserving._hyg.1885 : Ne.{1} Nat m (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (Nat.iterate.{succ u1} α f m x) s)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_preserving.exists_mem_image_mem MeasureTheory.MeasurePreserving.exists_mem_image_memₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (m «expr ≠ » 0) -/
/-- A self-map preserving a finite measure is conservative: if `μ s ≠ 0`, then at least one point
`x ∈ s` comes back to `s` under iterations of `f`. Actually, a.e. point of `s` comes back to `s`
infinitely many times, see `measure_theory.measure_preserving.conservative` and theorems about
`measure_theory.conservative`. -/
theorem exists_mem_image_mem [FiniteMeasure μ] (hf : MeasurePreserving f μ μ) (hs : MeasurableSet s)
    (hs' : μ s ≠ 0) : ∃ x ∈ s, ∃ (m : _)(_ : m ≠ 0), (f^[m]) x ∈ s :=
  by
  rcases ENNReal.exists_nat_mul_gt hs' (measure_ne_top μ (univ : Set α)) with ⟨N, hN⟩
  rcases hf.exists_mem_image_mem_of_volume_lt_mul_volume hs hN with ⟨x, hx, m, hm, hmx⟩
  exact ⟨x, hx, m, hm.1.ne', hmx⟩
#align measure_theory.measure_preserving.exists_mem_image_mem MeasureTheory.MeasurePreserving.exists_mem_image_mem

end MeasurePreserving

namespace MeasurableEquiv

/- warning: measure_theory.measurable_equiv.measure_preserving_symm -> MeasureTheory.MeasurableEquiv.measurePreserving_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] (μ : MeasureTheory.Measure.{u1} α _inst_1) (e : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2), MeasureTheory.MeasurePreserving.{u2, u1} β α _inst_2 _inst_1 (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MeasurableEquiv.{u2, u1} β α _inst_2 _inst_1) (fun (_x : MeasurableEquiv.{u2, u1} β α _inst_2 _inst_1) => β -> α) (MeasurableEquiv.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (MeasurableEquiv.symm.{u1, u2} α β _inst_1 _inst_2 e)) (MeasureTheory.Measure.map.{u1, u2} α β _inst_2 _inst_1 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : MeasurableEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (MeasurableEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) μ) μ
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] (μ : MeasureTheory.Measure.{u2} α _inst_1) (e : MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2), MeasureTheory.MeasurePreserving.{u1, u2} β α _inst_2 _inst_1 (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α _inst_2 _inst_1) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (MeasurableEquiv.{u1, u2} β α _inst_2 _inst_1) β α (MeasurableEquiv.instEquivLike.{u1, u2} β α _inst_2 _inst_1))) (MeasurableEquiv.symm.{u2, u1} α β _inst_1 _inst_2 e)) (MeasureTheory.Measure.map.{u2, u1} α β _inst_2 _inst_1 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MeasurableEquiv.{u2, u1} α β _inst_1 _inst_2) α β (MeasurableEquiv.instEquivLike.{u2, u1} α β _inst_1 _inst_2))) e) μ) μ
Case conversion may be inaccurate. Consider using '#align measure_theory.measurable_equiv.measure_preserving_symm MeasureTheory.MeasurableEquiv.measurePreserving_symmₓ'. -/
theorem measurePreserving_symm (μ : Measure α) (e : α ≃ᵐ β) :
    MeasurePreserving e.symm (map e μ) μ :=
  (e.Measurable.MeasurePreserving μ).symm _
#align measure_theory.measurable_equiv.measure_preserving_symm MeasureTheory.MeasurableEquiv.measurePreserving_symm

end MeasurableEquiv

end MeasureTheory

