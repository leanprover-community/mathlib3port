/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module measure_theory.measure.ae_measurable
! leanprover-community/mathlib commit a2706b55e8d7f7e9b1f93143f0b88f2e34a11eea
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Measure.MeasureSpace

/-!
# Almost everywhere measurable functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A function is almost everywhere measurable if it coincides almost everywhere with a measurable
function. This property, called `ae_measurable f μ`, is defined in the file `measure_space_def`.
We discuss several of its properties that are analogous to properties of measurable functions.
-/


open MeasureTheory MeasureTheory.Measure Filter Set Function

open MeasureTheory Filter Classical ENNReal Interval

variable {ι α β γ δ R : Type _} {m0 : MeasurableSpace α} [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ] {f g : α → β} {μ ν : Measure α}

include m0

section

/- warning: subsingleton.ae_measurable -> Subsingleton.aemeasurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] {f : α -> β} {μ : MeasureTheory.Measure.{u1} α m0} [_inst_4 : Subsingleton.{succ u1} α], AEMeasurable.{u1, u2} α β _inst_1 m0 f μ
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m0 : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {f : α -> β} {μ : MeasureTheory.Measure.{u2} α m0} [_inst_4 : Subsingleton.{succ u2} α], AEMeasurable.{u2, u1} α β _inst_1 m0 f μ
Case conversion may be inaccurate. Consider using '#align subsingleton.ae_measurable Subsingleton.aemeasurableₓ'. -/
@[nontriviality, measurability]
theorem Subsingleton.aemeasurable [Subsingleton α] : AEMeasurable f μ :=
  Subsingleton.measurable.AEMeasurable
#align subsingleton.ae_measurable Subsingleton.aemeasurable

#print aemeasurable_of_subsingleton_codomain /-
@[nontriviality, measurability]
theorem aemeasurable_of_subsingleton_codomain [Subsingleton β] : AEMeasurable f μ :=
  (measurable_of_subsingleton_codomain f).AEMeasurable
#align ae_measurable_of_subsingleton_codomain aemeasurable_of_subsingleton_codomain
-/

/- warning: ae_measurable_zero_measure -> aemeasurable_zero_measure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] {f : α -> β}, AEMeasurable.{u1, u2} α β _inst_1 m0 f (OfNat.ofNat.{u1} (MeasureTheory.Measure.{u1} α m0) 0 (OfNat.mk.{u1} (MeasureTheory.Measure.{u1} α m0) 0 (Zero.zero.{u1} (MeasureTheory.Measure.{u1} α m0) (MeasureTheory.Measure.instZero.{u1} α m0))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m0 : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {f : α -> β}, AEMeasurable.{u2, u1} α β _inst_1 m0 f (OfNat.ofNat.{u2} (MeasureTheory.Measure.{u2} α m0) 0 (Zero.toOfNat0.{u2} (MeasureTheory.Measure.{u2} α m0) (MeasureTheory.Measure.instZero.{u2} α m0)))
Case conversion may be inaccurate. Consider using '#align ae_measurable_zero_measure aemeasurable_zero_measureₓ'. -/
@[simp, measurability]
theorem aemeasurable_zero_measure : AEMeasurable f (0 : Measure α) :=
  by
  nontriviality α; inhabit α
  exact ⟨fun x => f default, measurable_const, rfl⟩
#align ae_measurable_zero_measure aemeasurable_zero_measure

namespace AEMeasurable

/- warning: ae_measurable.mono_measure -> AEMeasurable.mono_measure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] {f : α -> β} {μ : MeasureTheory.Measure.{u1} α m0} {ν : MeasureTheory.Measure.{u1} α m0}, (AEMeasurable.{u1, u2} α β _inst_1 m0 f μ) -> (LE.le.{u1} (MeasureTheory.Measure.{u1} α m0) (Preorder.toHasLe.{u1} (MeasureTheory.Measure.{u1} α m0) (PartialOrder.toPreorder.{u1} (MeasureTheory.Measure.{u1} α m0) (MeasureTheory.Measure.instPartialOrder.{u1} α m0))) ν μ) -> (AEMeasurable.{u1, u2} α β _inst_1 m0 f ν)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m0 : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {f : α -> β} {μ : MeasureTheory.Measure.{u2} α m0} {ν : MeasureTheory.Measure.{u2} α m0}, (AEMeasurable.{u2, u1} α β _inst_1 m0 f μ) -> (LE.le.{u2} (MeasureTheory.Measure.{u2} α m0) (Preorder.toLE.{u2} (MeasureTheory.Measure.{u2} α m0) (PartialOrder.toPreorder.{u2} (MeasureTheory.Measure.{u2} α m0) (MeasureTheory.Measure.instPartialOrder.{u2} α m0))) ν μ) -> (AEMeasurable.{u2, u1} α β _inst_1 m0 f ν)
Case conversion may be inaccurate. Consider using '#align ae_measurable.mono_measure AEMeasurable.mono_measureₓ'. -/
theorem mono_measure (h : AEMeasurable f μ) (h' : ν ≤ μ) : AEMeasurable f ν :=
  ⟨h.mk f, h.measurable_mk, Eventually.filter_mono (ae_mono h') h.ae_eq_mk⟩
#align ae_measurable.mono_measure AEMeasurable.mono_measure

/- warning: ae_measurable.mono_set -> AEMeasurable.mono_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] {f : α -> β} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (AEMeasurable.{u1, u2} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u1} α m0 μ t)) -> (AEMeasurable.{u1, u2} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u1} α m0 μ s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m0 : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {f : α -> β} {μ : MeasureTheory.Measure.{u2} α m0} {s : Set.{u2} α} {t : Set.{u2} α}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s t) -> (AEMeasurable.{u2, u1} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u2} α m0 μ t)) -> (AEMeasurable.{u2, u1} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u2} α m0 μ s))
Case conversion may be inaccurate. Consider using '#align ae_measurable.mono_set AEMeasurable.mono_setₓ'. -/
theorem mono_set {s t} (h : s ⊆ t) (ht : AEMeasurable f (μ.restrict t)) :
    AEMeasurable f (μ.restrict s) :=
  ht.mono_measure (restrict_mono h le_rfl)
#align ae_measurable.mono_set AEMeasurable.mono_set

/- warning: ae_measurable.mono' -> AEMeasurable.mono' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] {f : α -> β} {μ : MeasureTheory.Measure.{u1} α m0} {ν : MeasureTheory.Measure.{u1} α m0}, (AEMeasurable.{u1, u2} α β _inst_1 m0 f μ) -> (MeasureTheory.Measure.AbsolutelyContinuous.{u1} α m0 ν μ) -> (AEMeasurable.{u1, u2} α β _inst_1 m0 f ν)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m0 : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {f : α -> β} {μ : MeasureTheory.Measure.{u2} α m0} {ν : MeasureTheory.Measure.{u2} α m0}, (AEMeasurable.{u2, u1} α β _inst_1 m0 f μ) -> (MeasureTheory.Measure.AbsolutelyContinuous.{u2} α m0 ν μ) -> (AEMeasurable.{u2, u1} α β _inst_1 m0 f ν)
Case conversion may be inaccurate. Consider using '#align ae_measurable.mono' AEMeasurable.mono'ₓ'. -/
protected theorem mono' (h : AEMeasurable f μ) (h' : ν ≪ μ) : AEMeasurable f ν :=
  ⟨h.mk f, h.measurable_mk, h' h.ae_eq_mk⟩
#align ae_measurable.mono' AEMeasurable.mono'

/- warning: ae_measurable.ae_mem_imp_eq_mk -> AEMeasurable.ae_mem_imp_eq_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] {f : α -> β} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α} (h : AEMeasurable.{u1, u2} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u1} α m0 μ s)), Filter.Eventually.{u1} α (fun (x : α) => (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Eq.{succ u2} β (f x) (AEMeasurable.mk.{u1, u2} α β m0 _inst_1 (MeasureTheory.Measure.restrict.{u1} α m0 μ s) f h x))) (MeasureTheory.Measure.ae.{u1} α m0 μ)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m0 : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {f : α -> β} {μ : MeasureTheory.Measure.{u2} α m0} {s : Set.{u2} α} (h : AEMeasurable.{u2, u1} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u2} α m0 μ s)), Filter.Eventually.{u2} α (fun (x : α) => (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (Eq.{succ u1} β (f x) (AEMeasurable.mk.{u2, u1} α β m0 _inst_1 (MeasureTheory.Measure.restrict.{u2} α m0 μ s) f h x))) (MeasureTheory.Measure.ae.{u2} α m0 μ)
Case conversion may be inaccurate. Consider using '#align ae_measurable.ae_mem_imp_eq_mk AEMeasurable.ae_mem_imp_eq_mkₓ'. -/
theorem ae_mem_imp_eq_mk {s} (h : AEMeasurable f (μ.restrict s)) :
    ∀ᵐ x ∂μ, x ∈ s → f x = h.mk f x :=
  ae_imp_of_ae_restrict h.ae_eq_mk
#align ae_measurable.ae_mem_imp_eq_mk AEMeasurable.ae_mem_imp_eq_mk

/- warning: ae_measurable.ae_inf_principal_eq_mk -> AEMeasurable.ae_inf_principal_eq_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] {f : α -> β} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α} (h : AEMeasurable.{u1, u2} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u1} α m0 μ s)), Filter.EventuallyEq.{u1, u2} α β (Inf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) (MeasureTheory.Measure.ae.{u1} α m0 μ) (Filter.principal.{u1} α s)) f (AEMeasurable.mk.{u1, u2} α β m0 _inst_1 (MeasureTheory.Measure.restrict.{u1} α m0 μ s) f h)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m0 : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {f : α -> β} {μ : MeasureTheory.Measure.{u2} α m0} {s : Set.{u2} α} (h : AEMeasurable.{u2, u1} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u2} α m0 μ s)), Filter.EventuallyEq.{u2, u1} α β (Inf.inf.{u2} (Filter.{u2} α) (Filter.instInfFilter.{u2} α) (MeasureTheory.Measure.ae.{u2} α m0 μ) (Filter.principal.{u2} α s)) f (AEMeasurable.mk.{u2, u1} α β m0 _inst_1 (MeasureTheory.Measure.restrict.{u2} α m0 μ s) f h)
Case conversion may be inaccurate. Consider using '#align ae_measurable.ae_inf_principal_eq_mk AEMeasurable.ae_inf_principal_eq_mkₓ'. -/
theorem ae_inf_principal_eq_mk {s} (h : AEMeasurable f (μ.restrict s)) : f =ᶠ[μ.ae ⊓ 𝓟 s] h.mk f :=
  le_ae_restrict h.ae_eq_mk
#align ae_measurable.ae_inf_principal_eq_mk AEMeasurable.ae_inf_principal_eq_mk

/- warning: ae_measurable.sum_measure -> AEMeasurable.sum_measure is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {m0 : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u3} β] {f : α -> β} [_inst_4 : Countable.{succ u1} ι] {μ : ι -> (MeasureTheory.Measure.{u2} α m0)}, (forall (i : ι), AEMeasurable.{u2, u3} α β _inst_1 m0 f (μ i)) -> (AEMeasurable.{u2, u3} α β _inst_1 m0 f (MeasureTheory.Measure.sum.{u2, u1} α ι m0 μ))
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} {m0 : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {f : α -> β} [_inst_4 : Countable.{succ u3} ι] {μ : ι -> (MeasureTheory.Measure.{u2} α m0)}, (forall (i : ι), AEMeasurable.{u2, u1} α β _inst_1 m0 f (μ i)) -> (AEMeasurable.{u2, u1} α β _inst_1 m0 f (MeasureTheory.Measure.sum.{u2, u3} α ι m0 μ))
Case conversion may be inaccurate. Consider using '#align ae_measurable.sum_measure AEMeasurable.sum_measureₓ'. -/
@[measurability]
theorem sum_measure [Countable ι] {μ : ι → Measure α} (h : ∀ i, AEMeasurable f (μ i)) :
    AEMeasurable f (Sum μ) := by
  nontriviality β; inhabit β
  set s : ι → Set α := fun i => to_measurable (μ i) { x | f x ≠ (h i).mk f x }
  have hsμ : ∀ i, μ i (s i) = 0 := by intro i; rw [measure_to_measurable]; exact (h i).ae_eq_mk
  have hsm : MeasurableSet (⋂ i, s i) :=
    MeasurableSet.iInter fun i => measurable_set_to_measurable _ _
  have hs : ∀ i x, x ∉ s i → f x = (h i).mk f x := by intro i x hx; contrapose! hx;
    exact subset_to_measurable _ _ hx
  set g : α → β := (⋂ i, s i).piecewise (const α default) f
  refine' ⟨g, measurable_of_restrict_of_restrict_compl hsm _ _, ae_sum_iff.mpr fun i => _⟩
  · rw [restrict_piecewise]; simp only [Set.restrict, const]; exact measurable_const
  · rw [restrict_piecewise_compl, compl_Inter]
    intro t ht
    refine'
      ⟨⋃ i, (h i).mk f ⁻¹' t ∩ s iᶜ,
        MeasurableSet.iUnion fun i =>
          (measurable_mk _ ht).inter (measurable_set_to_measurable _ _).compl,
        _⟩
    ext ⟨x, hx⟩
    simp only [mem_preimage, mem_Union, Subtype.coe_mk, Set.restrict, mem_inter_iff,
      mem_compl_iff] at hx⊢
    constructor
    · rintro ⟨i, hxt, hxs⟩; rwa [hs _ _ hxs]
    · rcases hx with ⟨i, hi⟩; rw [hs _ _ hi]; exact fun h => ⟨i, h, hi⟩
  · refine' measure_mono_null (fun x (hx : f x ≠ g x) => _) (hsμ i)
    contrapose! hx; refine' (piecewise_eq_of_not_mem _ _ _ _).symm
    exact fun h => hx (mem_Inter.1 h i)
#align ae_measurable.sum_measure AEMeasurable.sum_measure

/- warning: ae_measurable_sum_measure_iff -> aemeasurable_sum_measure_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {m0 : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u3} β] {f : α -> β} [_inst_4 : Countable.{succ u1} ι] {μ : ι -> (MeasureTheory.Measure.{u2} α m0)}, Iff (AEMeasurable.{u2, u3} α β _inst_1 m0 f (MeasureTheory.Measure.sum.{u2, u1} α ι m0 μ)) (forall (i : ι), AEMeasurable.{u2, u3} α β _inst_1 m0 f (μ i))
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} {m0 : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {f : α -> β} [_inst_4 : Countable.{succ u3} ι] {μ : ι -> (MeasureTheory.Measure.{u2} α m0)}, Iff (AEMeasurable.{u2, u1} α β _inst_1 m0 f (MeasureTheory.Measure.sum.{u2, u3} α ι m0 μ)) (forall (i : ι), AEMeasurable.{u2, u1} α β _inst_1 m0 f (μ i))
Case conversion may be inaccurate. Consider using '#align ae_measurable_sum_measure_iff aemeasurable_sum_measure_iffₓ'. -/
@[simp]
theorem aemeasurable_sum_measure_iff [Countable ι] {μ : ι → Measure α} :
    AEMeasurable f (Sum μ) ↔ ∀ i, AEMeasurable f (μ i) :=
  ⟨fun h i => h.mono_measure (le_sum _ _), sum_measure⟩
#align ae_measurable_sum_measure_iff aemeasurable_sum_measure_iff

/- warning: ae_measurable_add_measure_iff -> aemeasurable_add_measure_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ae_measurable_add_measure_iff aemeasurable_add_measure_iffₓ'. -/
@[simp]
theorem aemeasurable_add_measure_iff :
    AEMeasurable f (μ + ν) ↔ AEMeasurable f μ ∧ AEMeasurable f ν := by
  rw [← sum_cond, aemeasurable_sum_measure_iff, Bool.forall_bool, and_comm]; rfl
#align ae_measurable_add_measure_iff aemeasurable_add_measure_iff

/- warning: ae_measurable.add_measure -> AEMeasurable.add_measure is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ae_measurable.add_measure AEMeasurable.add_measureₓ'. -/
@[measurability]
theorem add_measure {f : α → β} (hμ : AEMeasurable f μ) (hν : AEMeasurable f ν) :
    AEMeasurable f (μ + ν) :=
  aemeasurable_add_measure_iff.2 ⟨hμ, hν⟩
#align ae_measurable.add_measure AEMeasurable.add_measure

/- warning: ae_measurable.Union -> AEMeasurable.iUnion is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {m0 : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u3} β] {f : α -> β} {μ : MeasureTheory.Measure.{u2} α m0} [_inst_4 : Countable.{succ u1} ι] {s : ι -> (Set.{u2} α)}, (forall (i : ι), AEMeasurable.{u2, u3} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u2} α m0 μ (s i))) -> (AEMeasurable.{u2, u3} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u2} α m0 μ (Set.iUnion.{u2, succ u1} α ι (fun (i : ι) => s i))))
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} {m0 : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {f : α -> β} {μ : MeasureTheory.Measure.{u2} α m0} [_inst_4 : Countable.{succ u3} ι] {s : ι -> (Set.{u2} α)}, (forall (i : ι), AEMeasurable.{u2, u1} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u2} α m0 μ (s i))) -> (AEMeasurable.{u2, u1} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u2} α m0 μ (Set.iUnion.{u2, succ u3} α ι (fun (i : ι) => s i))))
Case conversion may be inaccurate. Consider using '#align ae_measurable.Union AEMeasurable.iUnionₓ'. -/
@[measurability]
protected theorem iUnion [Countable ι] {s : ι → Set α}
    (h : ∀ i, AEMeasurable f (μ.restrict (s i))) : AEMeasurable f (μ.restrict (⋃ i, s i)) :=
  (sum_measure h).mono_measure <| restrict_iUnion_le
#align ae_measurable.Union AEMeasurable.iUnion

/- warning: ae_measurable_Union_iff -> aemeasurable_iUnion_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {m0 : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u3} β] {f : α -> β} {μ : MeasureTheory.Measure.{u2} α m0} [_inst_4 : Countable.{succ u1} ι] {s : ι -> (Set.{u2} α)}, Iff (AEMeasurable.{u2, u3} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u2} α m0 μ (Set.iUnion.{u2, succ u1} α ι (fun (i : ι) => s i)))) (forall (i : ι), AEMeasurable.{u2, u3} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u2} α m0 μ (s i)))
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} {m0 : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {f : α -> β} {μ : MeasureTheory.Measure.{u2} α m0} [_inst_4 : Countable.{succ u3} ι] {s : ι -> (Set.{u2} α)}, Iff (AEMeasurable.{u2, u1} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u2} α m0 μ (Set.iUnion.{u2, succ u3} α ι (fun (i : ι) => s i)))) (forall (i : ι), AEMeasurable.{u2, u1} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u2} α m0 μ (s i)))
Case conversion may be inaccurate. Consider using '#align ae_measurable_Union_iff aemeasurable_iUnion_iffₓ'. -/
@[simp]
theorem aemeasurable_iUnion_iff [Countable ι] {s : ι → Set α} :
    AEMeasurable f (μ.restrict (⋃ i, s i)) ↔ ∀ i, AEMeasurable f (μ.restrict (s i)) :=
  ⟨fun h i => h.mono_measure <| restrict_mono (subset_iUnion _ _) le_rfl, AEMeasurable.iUnion⟩
#align ae_measurable_Union_iff aemeasurable_iUnion_iff

/- warning: ae_measurable_union_iff -> aemeasurable_union_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] {f : α -> β} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (AEMeasurable.{u1, u2} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u1} α m0 μ (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t))) (And (AEMeasurable.{u1, u2} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u1} α m0 μ s)) (AEMeasurable.{u1, u2} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u1} α m0 μ t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m0 : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {f : α -> β} {μ : MeasureTheory.Measure.{u2} α m0} {s : Set.{u2} α} {t : Set.{u2} α}, Iff (AEMeasurable.{u2, u1} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u2} α m0 μ (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s t))) (And (AEMeasurable.{u2, u1} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u2} α m0 μ s)) (AEMeasurable.{u2, u1} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u2} α m0 μ t)))
Case conversion may be inaccurate. Consider using '#align ae_measurable_union_iff aemeasurable_union_iffₓ'. -/
@[simp]
theorem aemeasurable_union_iff {s t : Set α} :
    AEMeasurable f (μ.restrict (s ∪ t)) ↔
      AEMeasurable f (μ.restrict s) ∧ AEMeasurable f (μ.restrict t) :=
  by simp only [union_eq_Union, aemeasurable_iUnion_iff, Bool.forall_bool, cond, and_comm]
#align ae_measurable_union_iff aemeasurable_union_iff

/- warning: ae_measurable.smul_measure -> AEMeasurable.smul_measure is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ae_measurable.smul_measure AEMeasurable.smul_measureₓ'. -/
@[measurability]
theorem smul_measure [Monoid R] [DistribMulAction R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (h : AEMeasurable f μ) (c : R) : AEMeasurable f (c • μ) :=
  ⟨h.mk f, h.measurable_mk, ae_smul_measure h.ae_eq_mk c⟩
#align ae_measurable.smul_measure AEMeasurable.smul_measure

#print AEMeasurable.comp_aemeasurable /-
theorem comp_aemeasurable {f : α → δ} {g : δ → β} (hg : AEMeasurable g (μ.map f))
    (hf : AEMeasurable f μ) : AEMeasurable (g ∘ f) μ :=
  ⟨hg.mk g ∘ hf.mk f, hg.measurable_mk.comp hf.measurable_mk,
    (ae_eq_comp hf hg.ae_eq_mk).trans (hf.ae_eq_mk.fun_comp (mk g hg))⟩
#align ae_measurable.comp_ae_measurable AEMeasurable.comp_aemeasurable
-/

#print AEMeasurable.comp_measurable /-
theorem comp_measurable {f : α → δ} {g : δ → β} (hg : AEMeasurable g (μ.map f))
    (hf : Measurable f) : AEMeasurable (g ∘ f) μ :=
  hg.comp_aemeasurable hf.AEMeasurable
#align ae_measurable.comp_measurable AEMeasurable.comp_measurable
-/

#print AEMeasurable.comp_quasiMeasurePreserving /-
theorem comp_quasiMeasurePreserving {ν : Measure δ} {f : α → δ} {g : δ → β} (hg : AEMeasurable g ν)
    (hf : QuasiMeasurePreserving f μ ν) : AEMeasurable (g ∘ f) μ :=
  (hg.mono' hf.AbsolutelyContinuous).comp_measurable hf.Measurable
#align ae_measurable.comp_quasi_measure_preserving AEMeasurable.comp_quasiMeasurePreserving
-/

/- warning: ae_measurable.map_map_of_ae_measurable -> AEMeasurable.map_map_of_aemeasurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m0 : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] [_inst_2 : MeasurableSpace.{u3} γ] {μ : MeasureTheory.Measure.{u1} α m0} {g : β -> γ} {f : α -> β}, (AEMeasurable.{u2, u3} β γ _inst_2 _inst_1 g (MeasureTheory.Measure.map.{u1, u2} α β _inst_1 m0 f μ)) -> (AEMeasurable.{u1, u2} α β _inst_1 m0 f μ) -> (Eq.{succ u3} (MeasureTheory.Measure.{u3} γ _inst_2) (MeasureTheory.Measure.map.{u2, u3} β γ _inst_2 _inst_1 g (MeasureTheory.Measure.map.{u1, u2} α β _inst_1 m0 f μ)) (MeasureTheory.Measure.map.{u1, u3} α γ _inst_2 m0 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) μ))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {m0 : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u3} β] [_inst_2 : MeasurableSpace.{u2} γ] {μ : MeasureTheory.Measure.{u1} α m0} {g : β -> γ} {f : α -> β}, (AEMeasurable.{u3, u2} β γ _inst_2 _inst_1 g (MeasureTheory.Measure.map.{u1, u3} α β _inst_1 m0 f μ)) -> (AEMeasurable.{u1, u3} α β _inst_1 m0 f μ) -> (Eq.{succ u2} (MeasureTheory.Measure.{u2} γ _inst_2) (MeasureTheory.Measure.map.{u3, u2} β γ _inst_2 _inst_1 g (MeasureTheory.Measure.map.{u1, u3} α β _inst_1 m0 f μ)) (MeasureTheory.Measure.map.{u1, u2} α γ _inst_2 m0 (Function.comp.{succ u1, succ u3, succ u2} α β γ g f) μ))
Case conversion may be inaccurate. Consider using '#align ae_measurable.map_map_of_ae_measurable AEMeasurable.map_map_of_aemeasurableₓ'. -/
theorem map_map_of_aemeasurable {g : β → γ} {f : α → β} (hg : AEMeasurable g (Measure.map f μ))
    (hf : AEMeasurable f μ) : (μ.map f).map g = μ.map (g ∘ f) :=
  by
  ext1 s hs
  let g' := hg.mk g
  have A : map g (map f μ) = map g' (map f μ) :=
    by
    apply MeasureTheory.Measure.map_congr
    exact hg.ae_eq_mk
  have B : map (g ∘ f) μ = map (g' ∘ f) μ :=
    by
    apply MeasureTheory.Measure.map_congr
    exact ae_of_ae_map hf hg.ae_eq_mk
  simp only [A, B, hs, hg.measurable_mk.ae_measurable.comp_ae_measurable hf, hg.measurable_mk,
    hg.measurable_mk hs, hf, map_apply, map_apply_of_ae_measurable]
  rfl
#align ae_measurable.map_map_of_ae_measurable AEMeasurable.map_map_of_aemeasurable

/- warning: ae_measurable.prod_mk -> AEMeasurable.prod_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m0 : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] [_inst_2 : MeasurableSpace.{u3} γ] {μ : MeasureTheory.Measure.{u1} α m0} {f : α -> β} {g : α -> γ}, (AEMeasurable.{u1, u2} α β _inst_1 m0 f μ) -> (AEMeasurable.{u1, u3} α γ _inst_2 m0 g μ) -> (AEMeasurable.{u1, max u2 u3} α (Prod.{u2, u3} β γ) (Prod.instMeasurableSpace.{u2, u3} β γ _inst_1 _inst_2) m0 (fun (x : α) => Prod.mk.{u2, u3} β γ (f x) (g x)) μ)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {m0 : MeasurableSpace.{u3} α} [_inst_1 : MeasurableSpace.{u2} β] [_inst_2 : MeasurableSpace.{u1} γ] {μ : MeasureTheory.Measure.{u3} α m0} {f : α -> β} {g : α -> γ}, (AEMeasurable.{u3, u2} α β _inst_1 m0 f μ) -> (AEMeasurable.{u3, u1} α γ _inst_2 m0 g μ) -> (AEMeasurable.{u3, max u1 u2} α (Prod.{u2, u1} β γ) (Prod.instMeasurableSpace.{u2, u1} β γ _inst_1 _inst_2) m0 (fun (x : α) => Prod.mk.{u2, u1} β γ (f x) (g x)) μ)
Case conversion may be inaccurate. Consider using '#align ae_measurable.prod_mk AEMeasurable.prod_mkₓ'. -/
@[measurability]
theorem prod_mk {f : α → β} {g : α → γ} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun x => (f x, g x)) μ :=
  ⟨fun a => (hf.mk f a, hg.mk g a), hf.measurable_mk.prod_mk hg.measurable_mk,
    EventuallyEq.prod_mk hf.ae_eq_mk hg.ae_eq_mk⟩
#align ae_measurable.prod_mk AEMeasurable.prod_mk

/- warning: ae_measurable.exists_ae_eq_range_subset -> AEMeasurable.exists_ae_eq_range_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] {f : α -> β} {μ : MeasureTheory.Measure.{u1} α m0}, (AEMeasurable.{u1, u2} α β _inst_1 m0 f μ) -> (forall {t : Set.{u2} β}, (Filter.Eventually.{u1} α (fun (x : α) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f x) t) (MeasureTheory.Measure.ae.{u1} α m0 μ)) -> (Set.Nonempty.{u2} β t) -> (Exists.{max (succ u1) (succ u2)} (α -> β) (fun (g : α -> β) => And (Measurable.{u1, u2} α β m0 _inst_1 g) (And (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.range.{u2, succ u1} β α g) t) (Filter.EventuallyEq.{u1, u2} α β (MeasureTheory.Measure.ae.{u1} α m0 μ) f g)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m0 : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {f : α -> β} {μ : MeasureTheory.Measure.{u2} α m0}, (AEMeasurable.{u2, u1} α β _inst_1 m0 f μ) -> (forall {t : Set.{u1} β}, (Filter.Eventually.{u2} α (fun (x : α) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (f x) t) (MeasureTheory.Measure.ae.{u2} α m0 μ)) -> (Set.Nonempty.{u1} β t) -> (Exists.{max (succ u1) (succ u2)} (α -> β) (fun (g : α -> β) => And (Measurable.{u2, u1} α β m0 _inst_1 g) (And (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Set.range.{u1, succ u2} β α g) t) (Filter.EventuallyEq.{u2, u1} α β (MeasureTheory.Measure.ae.{u2} α m0 μ) f g)))))
Case conversion may be inaccurate. Consider using '#align ae_measurable.exists_ae_eq_range_subset AEMeasurable.exists_ae_eq_range_subsetₓ'. -/
theorem exists_ae_eq_range_subset (H : AEMeasurable f μ) {t : Set β} (ht : ∀ᵐ x ∂μ, f x ∈ t)
    (h₀ : t.Nonempty) : ∃ g, Measurable g ∧ range g ⊆ t ∧ f =ᵐ[μ] g :=
  by
  let s : Set α := to_measurable μ ({ x | f x = H.mk f x ∧ f x ∈ t }ᶜ)
  let g : α → β := piecewise s (fun x => h₀.some) (H.mk f)
  refine' ⟨g, _, _, _⟩
  · exact Measurable.piecewise (measurable_set_to_measurable _ _) measurable_const H.measurable_mk
  · rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ s
    · simpa [g, hx] using h₀.some_mem
    · simp only [g, hx, piecewise_eq_of_not_mem, not_false_iff]
      contrapose! hx
      apply subset_to_measurable
      simp (config := { contextual := true }) only [hx, mem_compl_iff, mem_set_of_eq, not_and,
        not_false_iff, imp_true_iff]
  · have A : μ (to_measurable μ ({ x | f x = H.mk f x ∧ f x ∈ t }ᶜ)) = 0 :=
      by
      rw [measure_to_measurable, ← compl_mem_ae_iff, compl_compl]
      exact H.ae_eq_mk.and ht
    filter_upwards [compl_mem_ae_iff.2 A]with x hx
    rw [mem_compl_iff] at hx
    simp only [g, hx, piecewise_eq_of_not_mem, not_false_iff]
    contrapose! hx
    apply subset_to_measurable
    simp only [hx, mem_compl_iff, mem_set_of_eq, false_and_iff, not_false_iff]
#align ae_measurable.exists_ae_eq_range_subset AEMeasurable.exists_ae_eq_range_subset

/- warning: ae_measurable.exists_measurable_nonneg -> AEMeasurable.exists_measurable_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {β : Type.{u2}} [_inst_4 : Preorder.{u2} β] [_inst_5 : Zero.{u2} β] {mβ : MeasurableSpace.{u2} β} {f : α -> β}, (AEMeasurable.{u1, u2} α β mβ m0 f μ) -> (Filter.Eventually.{u1} α (fun (t : α) => LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_4) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_5))) (f t)) (MeasureTheory.Measure.ae.{u1} α m0 μ)) -> (Exists.{max (succ u1) (succ u2)} (α -> β) (fun (g : α -> β) => And (Measurable.{u1, u2} α β m0 mβ g) (And (LE.le.{max u1 u2} (α -> β) (Pi.hasLe.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => Preorder.toHasLe.{u2} β _inst_4)) (OfNat.ofNat.{max u1 u2} (α -> β) 0 (OfNat.mk.{max u1 u2} (α -> β) 0 (Zero.zero.{max u1 u2} (α -> β) (Pi.instZero.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => _inst_5))))) g) (Filter.EventuallyEq.{u1, u2} α β (MeasureTheory.Measure.ae.{u1} α m0 μ) f g))))
but is expected to have type
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {β : Type.{u2}} [_inst_4 : Preorder.{u2} β] [_inst_5 : Zero.{u2} β] {mβ : MeasurableSpace.{u2} β} {f : α -> β}, (AEMeasurable.{u1, u2} α β mβ m0 f μ) -> (Filter.Eventually.{u1} α (fun (t : α) => LE.le.{u2} β (Preorder.toLE.{u2} β _inst_4) (OfNat.ofNat.{u2} β 0 (Zero.toOfNat0.{u2} β _inst_5)) (f t)) (MeasureTheory.Measure.ae.{u1} α m0 μ)) -> (Exists.{max (succ u2) (succ u1)} (α -> β) (fun (g : α -> β) => And (Measurable.{u1, u2} α β m0 mβ g) (And (LE.le.{max u2 u1} (α -> β) (Pi.hasLe.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => Preorder.toLE.{u2} β _inst_4)) (OfNat.ofNat.{max u2 u1} (α -> β) 0 (Zero.toOfNat0.{max u1 u2} (α -> β) (Pi.instZero.{u1, u2} α (fun (a._@.Mathlib.MeasureTheory.MeasurableSpaceDef._hyg.5446 : α) => β) (fun (i : α) => _inst_5)))) g) (Filter.EventuallyEq.{u1, u2} α β (MeasureTheory.Measure.ae.{u1} α m0 μ) f g))))
Case conversion may be inaccurate. Consider using '#align ae_measurable.exists_measurable_nonneg AEMeasurable.exists_measurable_nonnegₓ'. -/
theorem exists_measurable_nonneg {β} [Preorder β] [Zero β] {mβ : MeasurableSpace β} {f : α → β}
    (hf : AEMeasurable f μ) (f_nn : ∀ᵐ t ∂μ, 0 ≤ f t) : ∃ g, Measurable g ∧ 0 ≤ g ∧ f =ᵐ[μ] g :=
  by
  obtain ⟨G, hG_meas, hG_mem, hG_ae_eq⟩ := hf.exists_ae_eq_range_subset f_nn ⟨0, le_rfl⟩
  exact ⟨G, hG_meas, fun x => hG_mem (mem_range_self x), hG_ae_eq⟩
#align ae_measurable.exists_measurable_nonneg AEMeasurable.exists_measurable_nonneg

/- warning: ae_measurable.subtype_mk -> AEMeasurable.subtype_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] {f : α -> β} {μ : MeasureTheory.Measure.{u1} α m0}, (AEMeasurable.{u1, u2} α β _inst_1 m0 f μ) -> (forall {s : Set.{u2} β} {hfs : forall (x : α), Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f x) s}, AEMeasurable.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) (Subtype.instMeasurableSpace.{u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) _inst_1) m0 (Set.codRestrict.{u2, succ u1} β α f s hfs) μ)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m0 : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {f : α -> β} {μ : MeasureTheory.Measure.{u2} α m0}, (AEMeasurable.{u2, u1} α β _inst_1 m0 f μ) -> (forall {s : Set.{u1} β} {hfs : forall (x : α), Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (f x) s}, AEMeasurable.{u2, u1} α (Set.Elem.{u1} β s) (Subtype.instMeasurableSpace.{u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x s) _inst_1) m0 (Set.codRestrict.{u1, succ u2} β α f s hfs) μ)
Case conversion may be inaccurate. Consider using '#align ae_measurable.subtype_mk AEMeasurable.subtype_mkₓ'. -/
theorem subtype_mk (h : AEMeasurable f μ) {s : Set β} {hfs : ∀ x, f x ∈ s} :
    AEMeasurable (codRestrict f s hfs) μ :=
  by
  nontriviality α; inhabit α
  obtain ⟨g, g_meas, hg, fg⟩ : ∃ g : α → β, Measurable g ∧ range g ⊆ s ∧ f =ᵐ[μ] g :=
    h.exists_ae_eq_range_subset (eventually_of_forall hfs) ⟨_, hfs default⟩
  refine' ⟨cod_restrict g s fun x => hg (mem_range_self _), Measurable.subtype_mk g_meas, _⟩
  filter_upwards [fg]with x hx
  simpa [Subtype.ext_iff]
#align ae_measurable.subtype_mk AEMeasurable.subtype_mk

/- warning: ae_measurable.null_measurable -> AEMeasurable.nullMeasurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] {f : α -> β} {μ : MeasureTheory.Measure.{u1} α m0}, (AEMeasurable.{u1, u2} α β _inst_1 m0 f μ) -> (MeasureTheory.NullMeasurable.{u1, u2} α β m0 _inst_1 f μ)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m0 : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {f : α -> β} {μ : MeasureTheory.Measure.{u2} α m0}, (AEMeasurable.{u2, u1} α β _inst_1 m0 f μ) -> (MeasureTheory.NullMeasurable.{u2, u1} α β m0 _inst_1 f μ)
Case conversion may be inaccurate. Consider using '#align ae_measurable.null_measurable AEMeasurable.nullMeasurableₓ'. -/
protected theorem nullMeasurable (h : AEMeasurable f μ) : NullMeasurable f μ :=
  let ⟨g, hgm, hg⟩ := h
  hgm.NullMeasurable.congr hg.symm
#align ae_measurable.null_measurable AEMeasurable.nullMeasurable

end AEMeasurable

/- warning: ae_measurable_const' -> aemeasurable_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] {f : α -> β} {μ : MeasureTheory.Measure.{u1} α m0}, (Filter.Eventually.{u1} α (fun (x : α) => Filter.Eventually.{u1} α (fun (y : α) => Eq.{succ u2} β (f x) (f y)) (MeasureTheory.Measure.ae.{u1} α m0 μ)) (MeasureTheory.Measure.ae.{u1} α m0 μ)) -> (AEMeasurable.{u1, u2} α β _inst_1 m0 f μ)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m0 : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {f : α -> β} {μ : MeasureTheory.Measure.{u2} α m0}, (Filter.Eventually.{u2} α (fun (x : α) => Filter.Eventually.{u2} α (fun (y : α) => Eq.{succ u1} β (f x) (f y)) (MeasureTheory.Measure.ae.{u2} α m0 μ)) (MeasureTheory.Measure.ae.{u2} α m0 μ)) -> (AEMeasurable.{u2, u1} α β _inst_1 m0 f μ)
Case conversion may be inaccurate. Consider using '#align ae_measurable_const' aemeasurable_const'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x y) -/
theorem aemeasurable_const' (h : ∀ᵐ (x) (y) ∂μ, f x = f y) : AEMeasurable f μ :=
  by
  rcases eq_or_ne μ 0 with (rfl | hμ)
  · exact aemeasurable_zero_measure
  · haveI := ae_ne_bot.2 hμ
    rcases h.exists with ⟨x, hx⟩
    exact ⟨const α (f x), measurable_const, eventually_eq.symm hx⟩
#align ae_measurable_const' aemeasurable_const'

/- warning: ae_measurable_uIoc_iff -> aemeasurable_uIoc_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] {μ : MeasureTheory.Measure.{u1} α m0} [_inst_4 : LinearOrder.{u1} α] {f : α -> β} {a : α} {b : α}, Iff (AEMeasurable.{u1, u2} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u1} α m0 μ (Set.uIoc.{u1} α _inst_4 a b))) (And (AEMeasurable.{u1, u2} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u1} α m0 μ (Set.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_4)))) a b))) (AEMeasurable.{u1, u2} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u1} α m0 μ (Set.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_4)))) b a))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m0 : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {μ : MeasureTheory.Measure.{u2} α m0} [_inst_4 : LinearOrder.{u2} α] {f : α -> β} {a : α} {b : α}, Iff (AEMeasurable.{u2, u1} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u2} α m0 μ (Set.uIoc.{u2} α _inst_4 a b))) (And (AEMeasurable.{u2, u1} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u2} α m0 μ (Set.Ioc.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_4))))) a b))) (AEMeasurable.{u2, u1} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u2} α m0 μ (Set.Ioc.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_4))))) b a))))
Case conversion may be inaccurate. Consider using '#align ae_measurable_uIoc_iff aemeasurable_uIoc_iffₓ'. -/
theorem aemeasurable_uIoc_iff [LinearOrder α] {f : α → β} {a b : α} :
    (AEMeasurable f <| μ.restrict <| Ι a b) ↔
      (AEMeasurable f <| μ.restrict <| Ioc a b) ∧ (AEMeasurable f <| μ.restrict <| Ioc b a) :=
  by rw [uIoc_eq_union, aemeasurable_union_iff]
#align ae_measurable_uIoc_iff aemeasurable_uIoc_iff

/- warning: ae_measurable_iff_measurable -> aemeasurable_iff_measurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] {f : α -> β} {μ : MeasureTheory.Measure.{u1} α m0} [_inst_4 : MeasureTheory.Measure.IsComplete.{u1} α m0 μ], Iff (AEMeasurable.{u1, u2} α β _inst_1 m0 f μ) (Measurable.{u1, u2} α β m0 _inst_1 f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m0 : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {f : α -> β} {μ : MeasureTheory.Measure.{u2} α m0} [_inst_4 : MeasureTheory.Measure.IsComplete.{u2} α m0 μ], Iff (AEMeasurable.{u2, u1} α β _inst_1 m0 f μ) (Measurable.{u2, u1} α β m0 _inst_1 f)
Case conversion may be inaccurate. Consider using '#align ae_measurable_iff_measurable aemeasurable_iff_measurableₓ'. -/
theorem aemeasurable_iff_measurable [μ.IsComplete] : AEMeasurable f μ ↔ Measurable f :=
  ⟨fun h => h.NullMeasurable.measurable_of_complete, fun h => h.AEMeasurable⟩
#align ae_measurable_iff_measurable aemeasurable_iff_measurable

/- warning: measurable_embedding.ae_measurable_map_iff -> MeasurableEmbedding.aemeasurable_map_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m0 : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] [_inst_2 : MeasurableSpace.{u3} γ] {f : α -> β} {μ : MeasureTheory.Measure.{u1} α m0} {g : β -> γ}, (MeasurableEmbedding.{u1, u2} α β m0 _inst_1 f) -> (Iff (AEMeasurable.{u2, u3} β γ _inst_2 _inst_1 g (MeasureTheory.Measure.map.{u1, u2} α β _inst_1 m0 f μ)) (AEMeasurable.{u1, u3} α γ _inst_2 m0 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) μ))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {m0 : MeasurableSpace.{u3} α} [_inst_1 : MeasurableSpace.{u2} β] [_inst_2 : MeasurableSpace.{u1} γ] {f : α -> β} {μ : MeasureTheory.Measure.{u3} α m0} {g : β -> γ}, (MeasurableEmbedding.{u3, u2} α β m0 _inst_1 f) -> (Iff (AEMeasurable.{u2, u1} β γ _inst_2 _inst_1 g (MeasureTheory.Measure.map.{u3, u2} α β _inst_1 m0 f μ)) (AEMeasurable.{u3, u1} α γ _inst_2 m0 (Function.comp.{succ u3, succ u2, succ u1} α β γ g f) μ))
Case conversion may be inaccurate. Consider using '#align measurable_embedding.ae_measurable_map_iff MeasurableEmbedding.aemeasurable_map_iffₓ'. -/
theorem MeasurableEmbedding.aemeasurable_map_iff {g : β → γ} (hf : MeasurableEmbedding f) :
    AEMeasurable g (μ.map f) ↔ AEMeasurable (g ∘ f) μ :=
  by
  refine' ⟨fun H => H.comp_measurable hf.measurable, _⟩
  rintro ⟨g₁, hgm₁, heq⟩
  rcases hf.exists_measurable_extend hgm₁ fun x => ⟨g x⟩ with ⟨g₂, hgm₂, rfl⟩
  exact ⟨g₂, hgm₂, hf.ae_map_iff.2 HEq⟩
#align measurable_embedding.ae_measurable_map_iff MeasurableEmbedding.aemeasurable_map_iff

/- warning: measurable_embedding.ae_measurable_comp_iff -> MeasurableEmbedding.aemeasurable_comp_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m0 : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] [_inst_2 : MeasurableSpace.{u3} γ] {f : α -> β} {g : β -> γ}, (MeasurableEmbedding.{u2, u3} β γ _inst_1 _inst_2 g) -> (forall {μ : MeasureTheory.Measure.{u1} α m0}, Iff (AEMeasurable.{u1, u3} α γ _inst_2 m0 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) μ) (AEMeasurable.{u1, u2} α β _inst_1 m0 f μ))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {m0 : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u3} β] [_inst_2 : MeasurableSpace.{u2} γ] {f : α -> β} {g : β -> γ}, (MeasurableEmbedding.{u3, u2} β γ _inst_1 _inst_2 g) -> (forall {μ : MeasureTheory.Measure.{u1} α m0}, Iff (AEMeasurable.{u1, u2} α γ _inst_2 m0 (Function.comp.{succ u1, succ u3, succ u2} α β γ g f) μ) (AEMeasurable.{u1, u3} α β _inst_1 m0 f μ))
Case conversion may be inaccurate. Consider using '#align measurable_embedding.ae_measurable_comp_iff MeasurableEmbedding.aemeasurable_comp_iffₓ'. -/
theorem MeasurableEmbedding.aemeasurable_comp_iff {g : β → γ} (hg : MeasurableEmbedding g)
    {μ : Measure α} : AEMeasurable (g ∘ f) μ ↔ AEMeasurable f μ :=
  by
  refine' ⟨fun H => _, hg.measurable.comp_ae_measurable⟩
  suffices AEMeasurable ((range_splitting g ∘ range_factorization g) ∘ f) μ by
    rwa [(right_inverse_range_splitting hg.injective).comp_eq_id] at this
  exact hg.measurable_range_splitting.comp_ae_measurable H.subtype_mk
#align measurable_embedding.ae_measurable_comp_iff MeasurableEmbedding.aemeasurable_comp_iff

/- warning: ae_measurable_restrict_iff_comap_subtype -> aemeasurable_restrict_iff_comap_subtype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] {s : Set.{u1} α}, (MeasurableSet.{u1} α m0 s) -> (forall {μ : MeasureTheory.Measure.{u1} α m0} {f : α -> β}, Iff (AEMeasurable.{u1, u2} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u1} α m0 μ s)) (AEMeasurable.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β _inst_1 (Subtype.instMeasurableSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) m0) (Function.comp.{succ u1, succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α β f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))))) (MeasureTheory.Measure.comap.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α m0 (Subtype.instMeasurableSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) m0) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)))))) μ)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m0 : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {s : Set.{u2} α}, (MeasurableSet.{u2} α m0 s) -> (forall {μ : MeasureTheory.Measure.{u2} α m0} {f : α -> β}, Iff (AEMeasurable.{u2, u1} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u2} α m0 μ s)) (AEMeasurable.{u2, u1} (Set.Elem.{u2} α s) β _inst_1 (Subtype.instMeasurableSpace.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) m0) (Function.comp.{succ u2, succ u2, succ u1} (Set.Elem.{u2} α s) α β f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s))) (MeasureTheory.Measure.comap.{u2, u2} (Set.Elem.{u2} α s) α m0 (Subtype.instMeasurableSpace.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) m0) (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s)) μ)))
Case conversion may be inaccurate. Consider using '#align ae_measurable_restrict_iff_comap_subtype aemeasurable_restrict_iff_comap_subtypeₓ'. -/
theorem aemeasurable_restrict_iff_comap_subtype {s : Set α} (hs : MeasurableSet s) {μ : Measure α}
    {f : α → β} : AEMeasurable f (μ.restrict s) ↔ AEMeasurable (f ∘ coe : s → β) (comap coe μ) := by
  rw [← map_comap_subtype_coe hs, (MeasurableEmbedding.subtype_coe hs).aemeasurable_map_iff]
#align ae_measurable_restrict_iff_comap_subtype aemeasurable_restrict_iff_comap_subtype

#print aemeasurable_one /-
@[simp, to_additive]
theorem aemeasurable_one [One β] : AEMeasurable (fun a : α => (1 : β)) μ :=
  measurable_one.AEMeasurable
#align ae_measurable_one aemeasurable_one
#align ae_measurable_zero aemeasurable_zero
-/

/- warning: ae_measurable_smul_measure_iff -> aemeasurable_smul_measure_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ae_measurable_smul_measure_iff aemeasurable_smul_measure_iffₓ'. -/
@[simp]
theorem aemeasurable_smul_measure_iff {c : ℝ≥0∞} (hc : c ≠ 0) :
    AEMeasurable f (c • μ) ↔ AEMeasurable f μ :=
  ⟨fun h => ⟨h.mk f, h.measurable_mk, (ae_smul_measure_iff hc).1 h.ae_eq_mk⟩, fun h =>
    ⟨h.mk f, h.measurable_mk, (ae_smul_measure_iff hc).2 h.ae_eq_mk⟩⟩
#align ae_measurable_smul_measure_iff aemeasurable_smul_measure_iff

#print aemeasurable_of_aemeasurable_trim /-
theorem aemeasurable_of_aemeasurable_trim {α} {m m0 : MeasurableSpace α} {μ : Measure α}
    (hm : m ≤ m0) {f : α → β} (hf : AEMeasurable f (μ.trim hm)) : AEMeasurable f μ :=
  ⟨hf.mk f, Measurable.mono hf.measurable_mk hm le_rfl, ae_eq_of_ae_eq_trim hf.ae_eq_mk⟩
#align ae_measurable_of_ae_measurable_trim aemeasurable_of_aemeasurable_trim
-/

/- warning: ae_measurable_restrict_of_measurable_subtype -> aemeasurable_restrict_of_measurable_subtype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] {f : α -> β} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α}, (MeasurableSet.{u1} α m0 s) -> (Measurable.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.instMeasurableSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) m0) _inst_1 (fun (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) => f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) x))) -> (AEMeasurable.{u1, u2} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u1} α m0 μ s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m0 : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {f : α -> β} {μ : MeasureTheory.Measure.{u2} α m0} {s : Set.{u2} α}, (MeasurableSet.{u2} α m0 s) -> (Measurable.{u2, u1} (Set.Elem.{u2} α s) β (Subtype.instMeasurableSpace.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) m0) _inst_1 (fun (x : Set.Elem.{u2} α s) => f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x))) -> (AEMeasurable.{u2, u1} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u2} α m0 μ s))
Case conversion may be inaccurate. Consider using '#align ae_measurable_restrict_of_measurable_subtype aemeasurable_restrict_of_measurable_subtypeₓ'. -/
theorem aemeasurable_restrict_of_measurable_subtype {s : Set α} (hs : MeasurableSet s)
    (hf : Measurable fun x : s => f x) : AEMeasurable f (μ.restrict s) :=
  (aemeasurable_restrict_iff_comap_subtype hs).2 hf.AEMeasurable
#align ae_measurable_restrict_of_measurable_subtype aemeasurable_restrict_of_measurable_subtype

/- warning: ae_measurable_map_equiv_iff -> aemeasurable_map_equiv_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m0 : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] [_inst_2 : MeasurableSpace.{u3} γ] {μ : MeasureTheory.Measure.{u1} α m0} (e : MeasurableEquiv.{u1, u2} α β m0 _inst_1) {f : β -> γ}, Iff (AEMeasurable.{u2, u3} β γ _inst_2 _inst_1 f (MeasureTheory.Measure.map.{u1, u2} α β _inst_1 m0 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasurableEquiv.{u1, u2} α β m0 _inst_1) (fun (_x : MeasurableEquiv.{u1, u2} α β m0 _inst_1) => α -> β) (MeasurableEquiv.hasCoeToFun.{u1, u2} α β m0 _inst_1) e) μ)) (AEMeasurable.{u1, u3} α γ _inst_2 m0 (Function.comp.{succ u1, succ u2, succ u3} α β γ f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasurableEquiv.{u1, u2} α β m0 _inst_1) (fun (_x : MeasurableEquiv.{u1, u2} α β m0 _inst_1) => α -> β) (MeasurableEquiv.hasCoeToFun.{u1, u2} α β m0 _inst_1) e)) μ)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {m0 : MeasurableSpace.{u3} α} [_inst_1 : MeasurableSpace.{u2} β] [_inst_2 : MeasurableSpace.{u1} γ] {μ : MeasureTheory.Measure.{u3} α m0} (e : MeasurableEquiv.{u3, u2} α β m0 _inst_1) {f : β -> γ}, Iff (AEMeasurable.{u2, u1} β γ _inst_2 _inst_1 f (MeasureTheory.Measure.map.{u3, u2} α β _inst_1 m0 (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MeasurableEquiv.{u3, u2} α β m0 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (MeasurableEquiv.{u3, u2} α β m0 _inst_1) α β (EquivLike.toEmbeddingLike.{max (succ u3) (succ u2), succ u3, succ u2} (MeasurableEquiv.{u3, u2} α β m0 _inst_1) α β (MeasurableEquiv.instEquivLike.{u3, u2} α β m0 _inst_1))) e) μ)) (AEMeasurable.{u3, u1} α γ _inst_2 m0 (Function.comp.{succ u3, succ u2, succ u1} α β γ f (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MeasurableEquiv.{u3, u2} α β m0 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (MeasurableEquiv.{u3, u2} α β m0 _inst_1) α β (EquivLike.toEmbeddingLike.{max (succ u3) (succ u2), succ u3, succ u2} (MeasurableEquiv.{u3, u2} α β m0 _inst_1) α β (MeasurableEquiv.instEquivLike.{u3, u2} α β m0 _inst_1))) e)) μ)
Case conversion may be inaccurate. Consider using '#align ae_measurable_map_equiv_iff aemeasurable_map_equiv_iffₓ'. -/
theorem aemeasurable_map_equiv_iff (e : α ≃ᵐ β) {f : β → γ} :
    AEMeasurable f (μ.map e) ↔ AEMeasurable (f ∘ e) μ :=
  e.MeasurableEmbedding.aemeasurable_map_iff
#align ae_measurable_map_equiv_iff aemeasurable_map_equiv_iff

end

/- warning: ae_measurable.restrict -> AEMeasurable.restrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] {f : α -> β} {μ : MeasureTheory.Measure.{u1} α m0}, (AEMeasurable.{u1, u2} α β _inst_1 m0 f μ) -> (forall {s : Set.{u1} α}, AEMeasurable.{u1, u2} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u1} α m0 μ s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m0 : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {f : α -> β} {μ : MeasureTheory.Measure.{u2} α m0}, (AEMeasurable.{u2, u1} α β _inst_1 m0 f μ) -> (forall {s : Set.{u2} α}, AEMeasurable.{u2, u1} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u2} α m0 μ s))
Case conversion may be inaccurate. Consider using '#align ae_measurable.restrict AEMeasurable.restrictₓ'. -/
theorem AEMeasurable.restrict (hfm : AEMeasurable f μ) {s} : AEMeasurable f (μ.restrict s) :=
  ⟨AEMeasurable.mk f hfm, hfm.measurable_mk, ae_restrict_of_ae hfm.ae_eq_mk⟩
#align ae_measurable.restrict AEMeasurable.restrict

/- warning: ae_measurable_Ioi_of_forall_Ioc -> aemeasurable_Ioi_of_forall_Ioc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {β : Type.{u2}} {mβ : MeasurableSpace.{u2} β} [_inst_4 : LinearOrder.{u1} α] [_inst_5 : Filter.IsCountablyGenerated.{u1} α (Filter.atTop.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_4)))))] {x : α} {g : α -> β}, (forall (t : α), (GT.gt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_4))))) t x) -> (AEMeasurable.{u1, u2} α β mβ m0 g (MeasureTheory.Measure.restrict.{u1} α m0 μ (Set.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_4)))) x t)))) -> (AEMeasurable.{u1, u2} α β mβ m0 g (MeasureTheory.Measure.restrict.{u1} α m0 μ (Set.Ioi.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_4)))) x)))
but is expected to have type
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {β : Type.{u2}} {mβ : MeasurableSpace.{u2} β} [_inst_4 : LinearOrder.{u1} α] [_inst_5 : Filter.IsCountablyGenerated.{u1} α (Filter.atTop.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_4))))))] {x : α} {g : α -> β}, (forall (t : α), (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_4)))))) t x) -> (AEMeasurable.{u1, u2} α β mβ m0 g (MeasureTheory.Measure.restrict.{u1} α m0 μ (Set.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_4))))) x t)))) -> (AEMeasurable.{u1, u2} α β mβ m0 g (MeasureTheory.Measure.restrict.{u1} α m0 μ (Set.Ioi.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_4))))) x)))
Case conversion may be inaccurate. Consider using '#align ae_measurable_Ioi_of_forall_Ioc aemeasurable_Ioi_of_forall_Iocₓ'. -/
theorem aemeasurable_Ioi_of_forall_Ioc {β} {mβ : MeasurableSpace β} [LinearOrder α]
    [(atTop : Filter α).IsCountablyGenerated] {x : α} {g : α → β}
    (g_meas : ∀ t > x, AEMeasurable g (μ.restrict (Ioc x t))) :
    AEMeasurable g (μ.restrict (Ioi x)) :=
  by
  haveI : Nonempty α := ⟨x⟩
  obtain ⟨u, hu_tendsto⟩ := exists_seq_tendsto (at_top : Filter α)
  have Ioi_eq_Union : Ioi x = ⋃ n : ℕ, Ioc x (u n) :=
    by
    rw [Union_Ioc_eq_Ioi_self_iff.mpr _]
    exact fun y _ => (hu_tendsto.eventually (eventually_ge_at_top y)).exists
  rw [Ioi_eq_Union, aemeasurable_iUnion_iff]
  intro n
  cases lt_or_le x (u n)
  · exact g_meas (u n) h
  · rw [Ioc_eq_empty (not_lt.mpr h), measure.restrict_empty]
    exact aemeasurable_zero_measure
#align ae_measurable_Ioi_of_forall_Ioc aemeasurable_Ioi_of_forall_Ioc

variable [Zero β]

/- warning: ae_measurable_indicator_iff -> aemeasurable_indicator_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] {f : α -> β} {μ : MeasureTheory.Measure.{u1} α m0} [_inst_4 : Zero.{u2} β] {s : Set.{u1} α}, (MeasurableSet.{u1} α m0 s) -> (Iff (AEMeasurable.{u1, u2} α β _inst_1 m0 (Set.indicator.{u1, u2} α β _inst_4 s f) μ) (AEMeasurable.{u1, u2} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u1} α m0 μ s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m0 : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {f : α -> β} {μ : MeasureTheory.Measure.{u2} α m0} [_inst_4 : Zero.{u1} β] {s : Set.{u2} α}, (MeasurableSet.{u2} α m0 s) -> (Iff (AEMeasurable.{u2, u1} α β _inst_1 m0 (Set.indicator.{u2, u1} α β _inst_4 s f) μ) (AEMeasurable.{u2, u1} α β _inst_1 m0 f (MeasureTheory.Measure.restrict.{u2} α m0 μ s)))
Case conversion may be inaccurate. Consider using '#align ae_measurable_indicator_iff aemeasurable_indicator_iffₓ'. -/
theorem aemeasurable_indicator_iff {s} (hs : MeasurableSet s) :
    AEMeasurable (indicator s f) μ ↔ AEMeasurable f (μ.restrict s) :=
  by
  constructor
  · intro h
    exact (h.mono_measure measure.restrict_le_self).congr (indicator_ae_eq_restrict hs)
  · intro h
    refine' ⟨indicator s (h.mk f), h.measurable_mk.indicator hs, _⟩
    have A : s.indicator f =ᵐ[μ.restrict s] s.indicator (AEMeasurable.mk f h) :=
      (indicator_ae_eq_restrict hs).trans (h.ae_eq_mk.trans <| (indicator_ae_eq_restrict hs).symm)
    have B : s.indicator f =ᵐ[μ.restrict (sᶜ)] s.indicator (AEMeasurable.mk f h) :=
      (indicator_ae_eq_restrict_compl hs).trans (indicator_ae_eq_restrict_compl hs).symm
    exact ae_of_ae_restrict_of_ae_restrict_compl _ A B
#align ae_measurable_indicator_iff aemeasurable_indicator_iff

/- warning: ae_measurable.indicator -> AEMeasurable.indicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} [_inst_1 : MeasurableSpace.{u2} β] {f : α -> β} {μ : MeasureTheory.Measure.{u1} α m0} [_inst_4 : Zero.{u2} β], (AEMeasurable.{u1, u2} α β _inst_1 m0 f μ) -> (forall {s : Set.{u1} α}, (MeasurableSet.{u1} α m0 s) -> (AEMeasurable.{u1, u2} α β _inst_1 m0 (Set.indicator.{u1, u2} α β _inst_4 s f) μ))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m0 : MeasurableSpace.{u2} α} [_inst_1 : MeasurableSpace.{u1} β] {f : α -> β} {μ : MeasureTheory.Measure.{u2} α m0} [_inst_4 : Zero.{u1} β], (AEMeasurable.{u2, u1} α β _inst_1 m0 f μ) -> (forall {s : Set.{u2} α}, (MeasurableSet.{u2} α m0 s) -> (AEMeasurable.{u2, u1} α β _inst_1 m0 (Set.indicator.{u2, u1} α β _inst_4 s f) μ))
Case conversion may be inaccurate. Consider using '#align ae_measurable.indicator AEMeasurable.indicatorₓ'. -/
@[measurability]
theorem AEMeasurable.indicator (hfm : AEMeasurable f μ) {s} (hs : MeasurableSet s) :
    AEMeasurable (s.indicator f) μ :=
  (aemeasurable_indicator_iff hs).mpr hfm.restrict
#align ae_measurable.indicator AEMeasurable.indicator

/- warning: measure_theory.measure.restrict_map_of_ae_measurable -> MeasureTheory.Measure.restrict_map_of_aemeasurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : Type.{u2}} {m0 : MeasurableSpace.{u1} α} [_inst_3 : MeasurableSpace.{u2} δ] {μ : MeasureTheory.Measure.{u1} α m0} {f : α -> δ}, (AEMeasurable.{u1, u2} α δ _inst_3 m0 f μ) -> (forall {s : Set.{u2} δ}, (MeasurableSet.{u2} δ _inst_3 s) -> (Eq.{succ u2} (MeasureTheory.Measure.{u2} δ _inst_3) (MeasureTheory.Measure.restrict.{u2} δ _inst_3 (MeasureTheory.Measure.map.{u1, u2} α δ _inst_3 m0 f μ) s) (MeasureTheory.Measure.map.{u1, u2} α δ _inst_3 m0 f (MeasureTheory.Measure.restrict.{u1} α m0 μ (Set.preimage.{u1, u2} α δ f s)))))
but is expected to have type
  forall {α : Type.{u2}} {δ : Type.{u1}} {m0 : MeasurableSpace.{u2} α} [_inst_3 : MeasurableSpace.{u1} δ] {μ : MeasureTheory.Measure.{u2} α m0} {f : α -> δ}, (AEMeasurable.{u2, u1} α δ _inst_3 m0 f μ) -> (forall {s : Set.{u1} δ}, (MeasurableSet.{u1} δ _inst_3 s) -> (Eq.{succ u1} (MeasureTheory.Measure.{u1} δ _inst_3) (MeasureTheory.Measure.restrict.{u1} δ _inst_3 (MeasureTheory.Measure.map.{u2, u1} α δ _inst_3 m0 f μ) s) (MeasureTheory.Measure.map.{u2, u1} α δ _inst_3 m0 f (MeasureTheory.Measure.restrict.{u2} α m0 μ (Set.preimage.{u2, u1} α δ f s)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.restrict_map_of_ae_measurable MeasureTheory.Measure.restrict_map_of_aemeasurableₓ'. -/
theorem MeasureTheory.Measure.restrict_map_of_aemeasurable {f : α → δ} (hf : AEMeasurable f μ)
    {s : Set δ} (hs : MeasurableSet s) : (μ.map f).restrict s = (μ.restrict <| f ⁻¹' s).map f :=
  calc
    (μ.map f).restrict s = (μ.map (hf.mk f)).restrict s := by congr 1;
      apply measure.map_congr hf.ae_eq_mk
    _ = (μ.restrict <| hf.mk f ⁻¹' s).map (hf.mk f) := (Measure.restrict_map hf.measurable_mk hs)
    _ = (μ.restrict <| hf.mk f ⁻¹' s).map f :=
      (Measure.map_congr (ae_restrict_of_ae hf.ae_eq_mk.symm))
    _ = (μ.restrict <| f ⁻¹' s).map f := by
      apply congr_arg
      ext1 t ht
      simp only [ht, measure.restrict_apply]
      apply measure_congr
      apply (eventually_eq.refl _ _).inter (hf.ae_eq_mk.symm.preimage s)
    
#align measure_theory.measure.restrict_map_of_ae_measurable MeasureTheory.Measure.restrict_map_of_aemeasurable

/- warning: measure_theory.measure.map_mono_of_ae_measurable -> MeasureTheory.Measure.map_mono_of_aemeasurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : Type.{u2}} {m0 : MeasurableSpace.{u1} α} [_inst_3 : MeasurableSpace.{u2} δ] {μ : MeasureTheory.Measure.{u1} α m0} {ν : MeasureTheory.Measure.{u1} α m0} {f : α -> δ}, (LE.le.{u1} (MeasureTheory.Measure.{u1} α m0) (Preorder.toHasLe.{u1} (MeasureTheory.Measure.{u1} α m0) (PartialOrder.toPreorder.{u1} (MeasureTheory.Measure.{u1} α m0) (MeasureTheory.Measure.instPartialOrder.{u1} α m0))) μ ν) -> (AEMeasurable.{u1, u2} α δ _inst_3 m0 f ν) -> (LE.le.{u2} (MeasureTheory.Measure.{u2} δ _inst_3) (Preorder.toHasLe.{u2} (MeasureTheory.Measure.{u2} δ _inst_3) (PartialOrder.toPreorder.{u2} (MeasureTheory.Measure.{u2} δ _inst_3) (MeasureTheory.Measure.instPartialOrder.{u2} δ _inst_3))) (MeasureTheory.Measure.map.{u1, u2} α δ _inst_3 m0 f μ) (MeasureTheory.Measure.map.{u1, u2} α δ _inst_3 m0 f ν))
but is expected to have type
  forall {α : Type.{u2}} {δ : Type.{u1}} {m0 : MeasurableSpace.{u2} α} [_inst_3 : MeasurableSpace.{u1} δ] {μ : MeasureTheory.Measure.{u2} α m0} {ν : MeasureTheory.Measure.{u2} α m0} {f : α -> δ}, (LE.le.{u2} (MeasureTheory.Measure.{u2} α m0) (Preorder.toLE.{u2} (MeasureTheory.Measure.{u2} α m0) (PartialOrder.toPreorder.{u2} (MeasureTheory.Measure.{u2} α m0) (MeasureTheory.Measure.instPartialOrder.{u2} α m0))) μ ν) -> (AEMeasurable.{u2, u1} α δ _inst_3 m0 f ν) -> (LE.le.{u1} (MeasureTheory.Measure.{u1} δ _inst_3) (Preorder.toLE.{u1} (MeasureTheory.Measure.{u1} δ _inst_3) (PartialOrder.toPreorder.{u1} (MeasureTheory.Measure.{u1} δ _inst_3) (MeasureTheory.Measure.instPartialOrder.{u1} δ _inst_3))) (MeasureTheory.Measure.map.{u2, u1} α δ _inst_3 m0 f μ) (MeasureTheory.Measure.map.{u2, u1} α δ _inst_3 m0 f ν))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.map_mono_of_ae_measurable MeasureTheory.Measure.map_mono_of_aemeasurableₓ'. -/
theorem MeasureTheory.Measure.map_mono_of_aemeasurable {f : α → δ} (h : μ ≤ ν)
    (hf : AEMeasurable f ν) : μ.map f ≤ ν.map f := fun s hs => by
  simpa [hf, hs, hf.mono_measure h] using measure.le_iff'.1 h (f ⁻¹' s)
#align measure_theory.measure.map_mono_of_ae_measurable MeasureTheory.Measure.map_mono_of_aemeasurable

