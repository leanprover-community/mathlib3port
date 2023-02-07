/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module topology.local_extr
! leanprover-community/mathlib commit 0a0ec35061ed9960bf0e7ffb0335f44447b58977
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Filter.Extr
import Mathbin.Topology.ContinuousOn

/-!
# Local extrema of functions on topological spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

This file defines special versions of `is_*_filter f a l`, `*=min/max/extr`,
from `order/filter/extr` for two kinds of filters: `nhds_within` and `nhds`.
These versions are called `is_local_*_on` and `is_local_*`, respectively.

## Main statements

Many lemmas in this file restate those from `order/filter/extr`, and you can find
a detailed documentation there. These convenience lemmas are provided only to make the dot notation
return propositions of expected types, not just `is_*_filter`.

Here is the list of statements specific to these two types of filters:

* `is_local_*.on`, `is_local_*_on.on_subset`: restrict to a subset;
* `is_local_*_on.inter` : intersect the set with another one;
* `is_*_on.localize` : a global extremum is a local extremum too.
* `is_[local_]*_on.is_local_*` : if we have `is_local_*_on f s a` and `s ∈ 𝓝 a`,
  then we have `is_local_* f a`.

-/


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} [TopologicalSpace α]

open Set Filter

open Topology Filter

section Preorder

variable [Preorder β] [Preorder γ] (f : α → β) (s : Set α) (a : α)

#print IsLocalMinOn /-
/-- `is_local_min_on f s a` means that `f a ≤ f x` for all `x ∈ s` in some neighborhood of `a`. -/
def IsLocalMinOn :=
  IsMinFilter f (𝓝[s] a) a
#align is_local_min_on IsLocalMinOn
-/

#print IsLocalMaxOn /-
/-- `is_local_max_on f s a` means that `f x ≤ f a` for all `x ∈ s` in some neighborhood of `a`. -/
def IsLocalMaxOn :=
  IsMaxFilter f (𝓝[s] a) a
#align is_local_max_on IsLocalMaxOn
-/

#print IsLocalExtrOn /-
/-- `is_local_extr_on f s a` means `is_local_min_on f s a ∨ is_local_max_on f s a`. -/
def IsLocalExtrOn :=
  IsExtrFilter f (𝓝[s] a) a
#align is_local_extr_on IsLocalExtrOn
-/

#print IsLocalMin /-
/-- `is_local_min f a` means that `f a ≤ f x` for all `x` in some neighborhood of `a`. -/
def IsLocalMin :=
  IsMinFilter f (𝓝 a) a
#align is_local_min IsLocalMin
-/

#print IsLocalMax /-
/-- `is_local_max f a` means that `f x ≤ f a` for all `x ∈ s` in some neighborhood of `a`. -/
def IsLocalMax :=
  IsMaxFilter f (𝓝 a) a
#align is_local_max IsLocalMax
-/

#print IsLocalExtr /-
/-- `is_local_extr_on f s a` means `is_local_min_on f s a ∨ is_local_max_on f s a`. -/
def IsLocalExtr :=
  IsExtrFilter f (𝓝 a) a
#align is_local_extr IsLocalExtr
-/

variable {f s a}

#print IsLocalExtrOn.elim /-
theorem IsLocalExtrOn.elim {p : Prop} :
    IsLocalExtrOn f s a → (IsLocalMinOn f s a → p) → (IsLocalMaxOn f s a → p) → p :=
  Or.elim
#align is_local_extr_on.elim IsLocalExtrOn.elim
-/

#print IsLocalExtr.elim /-
theorem IsLocalExtr.elim {p : Prop} :
    IsLocalExtr f a → (IsLocalMin f a → p) → (IsLocalMax f a → p) → p :=
  Or.elim
#align is_local_extr.elim IsLocalExtr.elim
-/

/-! ### Restriction to (sub)sets -/


#print IsLocalMin.on /-
theorem IsLocalMin.on (h : IsLocalMin f a) (s) : IsLocalMinOn f s a :=
  h.filter_inf _
#align is_local_min.on IsLocalMin.on
-/

#print IsLocalMax.on /-
theorem IsLocalMax.on (h : IsLocalMax f a) (s) : IsLocalMaxOn f s a :=
  h.filter_inf _
#align is_local_max.on IsLocalMax.on
-/

#print IsLocalExtr.on /-
theorem IsLocalExtr.on (h : IsLocalExtr f a) (s) : IsLocalExtrOn f s a :=
  h.filter_inf _
#align is_local_extr.on IsLocalExtr.on
-/

#print IsLocalMinOn.on_subset /-
theorem IsLocalMinOn.on_subset {t : Set α} (hf : IsLocalMinOn f t a) (h : s ⊆ t) :
    IsLocalMinOn f s a :=
  hf.filter_mono <| nhdsWithin_mono a h
#align is_local_min_on.on_subset IsLocalMinOn.on_subset
-/

#print IsLocalMaxOn.on_subset /-
theorem IsLocalMaxOn.on_subset {t : Set α} (hf : IsLocalMaxOn f t a) (h : s ⊆ t) :
    IsLocalMaxOn f s a :=
  hf.filter_mono <| nhdsWithin_mono a h
#align is_local_max_on.on_subset IsLocalMaxOn.on_subset
-/

#print IsLocalExtrOn.on_subset /-
theorem IsLocalExtrOn.on_subset {t : Set α} (hf : IsLocalExtrOn f t a) (h : s ⊆ t) :
    IsLocalExtrOn f s a :=
  hf.filter_mono <| nhdsWithin_mono a h
#align is_local_extr_on.on_subset IsLocalExtrOn.on_subset
-/

/- warning: is_local_min_on.inter -> IsLocalMinOn.inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {s : Set.{u1} α} {a : α}, (IsLocalMinOn.{u1, u2} α β _inst_1 _inst_2 f s a) -> (forall (t : Set.{u1} α), IsLocalMinOn.{u1, u2} α β _inst_1 _inst_2 f (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {s : Set.{u1} α} {a : α}, (IsLocalMinOn.{u1, u2} α β _inst_1 _inst_2 f s a) -> (forall (t : Set.{u1} α), IsLocalMinOn.{u1, u2} α β _inst_1 _inst_2 f (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) a)
Case conversion may be inaccurate. Consider using '#align is_local_min_on.inter IsLocalMinOn.interₓ'. -/
theorem IsLocalMinOn.inter (hf : IsLocalMinOn f s a) (t) : IsLocalMinOn f (s ∩ t) a :=
  hf.on_subset (inter_subset_left s t)
#align is_local_min_on.inter IsLocalMinOn.inter

/- warning: is_local_max_on.inter -> IsLocalMaxOn.inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {s : Set.{u1} α} {a : α}, (IsLocalMaxOn.{u1, u2} α β _inst_1 _inst_2 f s a) -> (forall (t : Set.{u1} α), IsLocalMaxOn.{u1, u2} α β _inst_1 _inst_2 f (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {s : Set.{u1} α} {a : α}, (IsLocalMaxOn.{u1, u2} α β _inst_1 _inst_2 f s a) -> (forall (t : Set.{u1} α), IsLocalMaxOn.{u1, u2} α β _inst_1 _inst_2 f (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) a)
Case conversion may be inaccurate. Consider using '#align is_local_max_on.inter IsLocalMaxOn.interₓ'. -/
theorem IsLocalMaxOn.inter (hf : IsLocalMaxOn f s a) (t) : IsLocalMaxOn f (s ∩ t) a :=
  hf.on_subset (inter_subset_left s t)
#align is_local_max_on.inter IsLocalMaxOn.inter

/- warning: is_local_extr_on.inter -> IsLocalExtrOn.inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {s : Set.{u1} α} {a : α}, (IsLocalExtrOn.{u1, u2} α β _inst_1 _inst_2 f s a) -> (forall (t : Set.{u1} α), IsLocalExtrOn.{u1, u2} α β _inst_1 _inst_2 f (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {s : Set.{u1} α} {a : α}, (IsLocalExtrOn.{u1, u2} α β _inst_1 _inst_2 f s a) -> (forall (t : Set.{u1} α), IsLocalExtrOn.{u1, u2} α β _inst_1 _inst_2 f (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) a)
Case conversion may be inaccurate. Consider using '#align is_local_extr_on.inter IsLocalExtrOn.interₓ'. -/
theorem IsLocalExtrOn.inter (hf : IsLocalExtrOn f s a) (t) : IsLocalExtrOn f (s ∩ t) a :=
  hf.on_subset (inter_subset_left s t)
#align is_local_extr_on.inter IsLocalExtrOn.inter

#print IsMinOn.localize /-
theorem IsMinOn.localize (hf : IsMinOn f s a) : IsLocalMinOn f s a :=
  hf.filter_mono <| inf_le_right
#align is_min_on.localize IsMinOn.localize
-/

#print IsMaxOn.localize /-
theorem IsMaxOn.localize (hf : IsMaxOn f s a) : IsLocalMaxOn f s a :=
  hf.filter_mono <| inf_le_right
#align is_max_on.localize IsMaxOn.localize
-/

#print IsExtrOn.localize /-
theorem IsExtrOn.localize (hf : IsExtrOn f s a) : IsLocalExtrOn f s a :=
  hf.filter_mono <| inf_le_right
#align is_extr_on.localize IsExtrOn.localize
-/

#print IsLocalMinOn.isLocalMin /-
theorem IsLocalMinOn.isLocalMin (hf : IsLocalMinOn f s a) (hs : s ∈ 𝓝 a) : IsLocalMin f a :=
  have : 𝓝 a ≤ 𝓟 s := le_principal_iff.2 hs
  hf.filter_mono <| le_inf le_rfl this
#align is_local_min_on.is_local_min IsLocalMinOn.isLocalMin
-/

#print IsLocalMaxOn.isLocalMax /-
theorem IsLocalMaxOn.isLocalMax (hf : IsLocalMaxOn f s a) (hs : s ∈ 𝓝 a) : IsLocalMax f a :=
  have : 𝓝 a ≤ 𝓟 s := le_principal_iff.2 hs
  hf.filter_mono <| le_inf le_rfl this
#align is_local_max_on.is_local_max IsLocalMaxOn.isLocalMax
-/

#print IsLocalExtrOn.isLocalExtr /-
theorem IsLocalExtrOn.isLocalExtr (hf : IsLocalExtrOn f s a) (hs : s ∈ 𝓝 a) : IsLocalExtr f a :=
  hf.elim (fun hf => (hf.IsLocalMin hs).isExtr) fun hf => (hf.IsLocalMax hs).isExtr
#align is_local_extr_on.is_local_extr IsLocalExtrOn.isLocalExtr
-/

#print IsMinOn.isLocalMin /-
theorem IsMinOn.isLocalMin (hf : IsMinOn f s a) (hs : s ∈ 𝓝 a) : IsLocalMin f a :=
  hf.localize.IsLocalMin hs
#align is_min_on.is_local_min IsMinOn.isLocalMin
-/

#print IsMaxOn.isLocalMax /-
theorem IsMaxOn.isLocalMax (hf : IsMaxOn f s a) (hs : s ∈ 𝓝 a) : IsLocalMax f a :=
  hf.localize.IsLocalMax hs
#align is_max_on.is_local_max IsMaxOn.isLocalMax
-/

#print IsExtrOn.isLocalExtr /-
theorem IsExtrOn.isLocalExtr (hf : IsExtrOn f s a) (hs : s ∈ 𝓝 a) : IsLocalExtr f a :=
  hf.localize.IsLocalExtr hs
#align is_extr_on.is_local_extr IsExtrOn.isLocalExtr
-/

/- warning: is_local_min_on.not_nhds_le_map -> IsLocalMinOn.not_nhds_le_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {s : Set.{u1} α} {a : α} [_inst_4 : TopologicalSpace.{u2} β], (IsLocalMinOn.{u1, u2} α β _inst_1 _inst_2 f s a) -> (forall [_inst_5 : Filter.NeBot.{u2} β (nhdsWithin.{u2} β _inst_4 (f a) (Set.Iio.{u2} β _inst_2 (f a)))], Not (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (nhds.{u2} β _inst_4 (f a)) (Filter.map.{u1, u2} α β f (nhdsWithin.{u1} α _inst_1 a s))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {s : Set.{u1} α} {a : α} [_inst_4 : TopologicalSpace.{u2} β], (IsLocalMinOn.{u1, u2} α β _inst_1 _inst_2 f s a) -> (forall [_inst_5 : Filter.NeBot.{u2} β (nhdsWithin.{u2} β _inst_4 (f a) (Set.Iio.{u2} β _inst_2 (f a)))], Not (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) (nhds.{u2} β _inst_4 (f a)) (Filter.map.{u1, u2} α β f (nhdsWithin.{u1} α _inst_1 a s))))
Case conversion may be inaccurate. Consider using '#align is_local_min_on.not_nhds_le_map IsLocalMinOn.not_nhds_le_mapₓ'. -/
theorem IsLocalMinOn.not_nhds_le_map [TopologicalSpace β] (hf : IsLocalMinOn f s a)
    [NeBot (𝓝[<] f a)] : ¬𝓝 (f a) ≤ map f (𝓝[s] a) := fun hle =>
  have : ∀ᶠ y in 𝓝[<] f a, f a ≤ y := (eventually_map.2 hf).filter_mono (inf_le_left.trans hle)
  let ⟨y, hy⟩ := (this.And self_mem_nhdsWithin).exists
  hy.1.not_lt hy.2
#align is_local_min_on.not_nhds_le_map IsLocalMinOn.not_nhds_le_map

/- warning: is_local_max_on.not_nhds_le_map -> IsLocalMaxOn.not_nhds_le_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {s : Set.{u1} α} {a : α} [_inst_4 : TopologicalSpace.{u2} β], (IsLocalMaxOn.{u1, u2} α β _inst_1 _inst_2 f s a) -> (forall [_inst_5 : Filter.NeBot.{u2} β (nhdsWithin.{u2} β _inst_4 (f a) (Set.Ioi.{u2} β _inst_2 (f a)))], Not (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (nhds.{u2} β _inst_4 (f a)) (Filter.map.{u1, u2} α β f (nhdsWithin.{u1} α _inst_1 a s))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {s : Set.{u1} α} {a : α} [_inst_4 : TopologicalSpace.{u2} β], (IsLocalMaxOn.{u1, u2} α β _inst_1 _inst_2 f s a) -> (forall [_inst_5 : Filter.NeBot.{u2} β (nhdsWithin.{u2} β _inst_4 (f a) (Set.Ioi.{u2} β _inst_2 (f a)))], Not (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) (nhds.{u2} β _inst_4 (f a)) (Filter.map.{u1, u2} α β f (nhdsWithin.{u1} α _inst_1 a s))))
Case conversion may be inaccurate. Consider using '#align is_local_max_on.not_nhds_le_map IsLocalMaxOn.not_nhds_le_mapₓ'. -/
theorem IsLocalMaxOn.not_nhds_le_map [TopologicalSpace β] (hf : IsLocalMaxOn f s a)
    [NeBot (𝓝[>] f a)] : ¬𝓝 (f a) ≤ map f (𝓝[s] a) :=
  @IsLocalMinOn.not_nhds_le_map α βᵒᵈ _ _ _ _ _ ‹_› hf ‹_›
#align is_local_max_on.not_nhds_le_map IsLocalMaxOn.not_nhds_le_map

/- warning: is_local_extr_on.not_nhds_le_map -> IsLocalExtrOn.not_nhds_le_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {s : Set.{u1} α} {a : α} [_inst_4 : TopologicalSpace.{u2} β], (IsLocalExtrOn.{u1, u2} α β _inst_1 _inst_2 f s a) -> (forall [_inst_5 : Filter.NeBot.{u2} β (nhdsWithin.{u2} β _inst_4 (f a) (Set.Iio.{u2} β _inst_2 (f a)))] [_inst_6 : Filter.NeBot.{u2} β (nhdsWithin.{u2} β _inst_4 (f a) (Set.Ioi.{u2} β _inst_2 (f a)))], Not (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) (nhds.{u2} β _inst_4 (f a)) (Filter.map.{u1, u2} α β f (nhdsWithin.{u1} α _inst_1 a s))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {s : Set.{u1} α} {a : α} [_inst_4 : TopologicalSpace.{u2} β], (IsLocalExtrOn.{u1, u2} α β _inst_1 _inst_2 f s a) -> (forall [_inst_5 : Filter.NeBot.{u2} β (nhdsWithin.{u2} β _inst_4 (f a) (Set.Iio.{u2} β _inst_2 (f a)))] [_inst_6 : Filter.NeBot.{u2} β (nhdsWithin.{u2} β _inst_4 (f a) (Set.Ioi.{u2} β _inst_2 (f a)))], Not (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) (nhds.{u2} β _inst_4 (f a)) (Filter.map.{u1, u2} α β f (nhdsWithin.{u1} α _inst_1 a s))))
Case conversion may be inaccurate. Consider using '#align is_local_extr_on.not_nhds_le_map IsLocalExtrOn.not_nhds_le_mapₓ'. -/
theorem IsLocalExtrOn.not_nhds_le_map [TopologicalSpace β] (hf : IsLocalExtrOn f s a)
    [NeBot (𝓝[<] f a)] [NeBot (𝓝[>] f a)] : ¬𝓝 (f a) ≤ map f (𝓝[s] a) :=
  hf.elim (fun h => h.not_nhds_le_map) fun h => h.not_nhds_le_map
#align is_local_extr_on.not_nhds_le_map IsLocalExtrOn.not_nhds_le_map

/-! ### Constant -/


#print isLocalMinOn_const /-
theorem isLocalMinOn_const {b : β} : IsLocalMinOn (fun _ => b) s a :=
  isMinFilter_const
#align is_local_min_on_const isLocalMinOn_const
-/

#print isLocalMaxOn_const /-
theorem isLocalMaxOn_const {b : β} : IsLocalMaxOn (fun _ => b) s a :=
  isMaxFilter_const
#align is_local_max_on_const isLocalMaxOn_const
-/

#print isLocalExtrOn_const /-
theorem isLocalExtrOn_const {b : β} : IsLocalExtrOn (fun _ => b) s a :=
  isExtrFilter_const
#align is_local_extr_on_const isLocalExtrOn_const
-/

#print isLocalMin_const /-
theorem isLocalMin_const {b : β} : IsLocalMin (fun _ => b) a :=
  isMinFilter_const
#align is_local_min_const isLocalMin_const
-/

#print isLocalMax_const /-
theorem isLocalMax_const {b : β} : IsLocalMax (fun _ => b) a :=
  isMaxFilter_const
#align is_local_max_const isLocalMax_const
-/

#print isLocalExtr_const /-
theorem isLocalExtr_const {b : β} : IsLocalExtr (fun _ => b) a :=
  isExtrFilter_const
#align is_local_extr_const isLocalExtr_const
-/

/-! ### Composition with (anti)monotone functions -/


#print IsLocalMin.comp_mono /-
theorem IsLocalMin.comp_mono (hf : IsLocalMin f a) {g : β → γ} (hg : Monotone g) :
    IsLocalMin (g ∘ f) a :=
  hf.comp_mono hg
#align is_local_min.comp_mono IsLocalMin.comp_mono
-/

#print IsLocalMax.comp_mono /-
theorem IsLocalMax.comp_mono (hf : IsLocalMax f a) {g : β → γ} (hg : Monotone g) :
    IsLocalMax (g ∘ f) a :=
  hf.comp_mono hg
#align is_local_max.comp_mono IsLocalMax.comp_mono
-/

#print IsLocalExtr.comp_mono /-
theorem IsLocalExtr.comp_mono (hf : IsLocalExtr f a) {g : β → γ} (hg : Monotone g) :
    IsLocalExtr (g ∘ f) a :=
  hf.comp_mono hg
#align is_local_extr.comp_mono IsLocalExtr.comp_mono
-/

#print IsLocalMin.comp_antitone /-
theorem IsLocalMin.comp_antitone (hf : IsLocalMin f a) {g : β → γ} (hg : Antitone g) :
    IsLocalMax (g ∘ f) a :=
  hf.comp_antitone hg
#align is_local_min.comp_antitone IsLocalMin.comp_antitone
-/

#print IsLocalMax.comp_antitone /-
theorem IsLocalMax.comp_antitone (hf : IsLocalMax f a) {g : β → γ} (hg : Antitone g) :
    IsLocalMin (g ∘ f) a :=
  hf.comp_antitone hg
#align is_local_max.comp_antitone IsLocalMax.comp_antitone
-/

#print IsLocalExtr.comp_antitone /-
theorem IsLocalExtr.comp_antitone (hf : IsLocalExtr f a) {g : β → γ} (hg : Antitone g) :
    IsLocalExtr (g ∘ f) a :=
  hf.comp_antitone hg
#align is_local_extr.comp_antitone IsLocalExtr.comp_antitone
-/

#print IsLocalMinOn.comp_mono /-
theorem IsLocalMinOn.comp_mono (hf : IsLocalMinOn f s a) {g : β → γ} (hg : Monotone g) :
    IsLocalMinOn (g ∘ f) s a :=
  hf.comp_mono hg
#align is_local_min_on.comp_mono IsLocalMinOn.comp_mono
-/

#print IsLocalMaxOn.comp_mono /-
theorem IsLocalMaxOn.comp_mono (hf : IsLocalMaxOn f s a) {g : β → γ} (hg : Monotone g) :
    IsLocalMaxOn (g ∘ f) s a :=
  hf.comp_mono hg
#align is_local_max_on.comp_mono IsLocalMaxOn.comp_mono
-/

#print IsLocalExtrOn.comp_mono /-
theorem IsLocalExtrOn.comp_mono (hf : IsLocalExtrOn f s a) {g : β → γ} (hg : Monotone g) :
    IsLocalExtrOn (g ∘ f) s a :=
  hf.comp_mono hg
#align is_local_extr_on.comp_mono IsLocalExtrOn.comp_mono
-/

#print IsLocalMinOn.comp_antitone /-
theorem IsLocalMinOn.comp_antitone (hf : IsLocalMinOn f s a) {g : β → γ} (hg : Antitone g) :
    IsLocalMaxOn (g ∘ f) s a :=
  hf.comp_antitone hg
#align is_local_min_on.comp_antitone IsLocalMinOn.comp_antitone
-/

#print IsLocalMaxOn.comp_antitone /-
theorem IsLocalMaxOn.comp_antitone (hf : IsLocalMaxOn f s a) {g : β → γ} (hg : Antitone g) :
    IsLocalMinOn (g ∘ f) s a :=
  hf.comp_antitone hg
#align is_local_max_on.comp_antitone IsLocalMaxOn.comp_antitone
-/

#print IsLocalExtrOn.comp_antitone /-
theorem IsLocalExtrOn.comp_antitone (hf : IsLocalExtrOn f s a) {g : β → γ} (hg : Antitone g) :
    IsLocalExtrOn (g ∘ f) s a :=
  hf.comp_antitone hg
#align is_local_extr_on.comp_antitone IsLocalExtrOn.comp_antitone
-/

#print IsLocalMin.bicomp_mono /-
theorem IsLocalMin.bicomp_mono [Preorder δ] {op : β → γ → δ}
    (hop : ((· ≤ ·) ⇒ (· ≤ ·) ⇒ (· ≤ ·)) op op) (hf : IsLocalMin f a) {g : α → γ}
    (hg : IsLocalMin g a) : IsLocalMin (fun x => op (f x) (g x)) a :=
  hf.bicomp_mono hop hg
#align is_local_min.bicomp_mono IsLocalMin.bicomp_mono
-/

#print IsLocalMax.bicomp_mono /-
theorem IsLocalMax.bicomp_mono [Preorder δ] {op : β → γ → δ}
    (hop : ((· ≤ ·) ⇒ (· ≤ ·) ⇒ (· ≤ ·)) op op) (hf : IsLocalMax f a) {g : α → γ}
    (hg : IsLocalMax g a) : IsLocalMax (fun x => op (f x) (g x)) a :=
  hf.bicomp_mono hop hg
#align is_local_max.bicomp_mono IsLocalMax.bicomp_mono
-/

#print IsLocalMinOn.bicomp_mono /-
-- No `extr` version because we need `hf` and `hg` to be of the same kind
theorem IsLocalMinOn.bicomp_mono [Preorder δ] {op : β → γ → δ}
    (hop : ((· ≤ ·) ⇒ (· ≤ ·) ⇒ (· ≤ ·)) op op) (hf : IsLocalMinOn f s a) {g : α → γ}
    (hg : IsLocalMinOn g s a) : IsLocalMinOn (fun x => op (f x) (g x)) s a :=
  hf.bicomp_mono hop hg
#align is_local_min_on.bicomp_mono IsLocalMinOn.bicomp_mono
-/

#print IsLocalMaxOn.bicomp_mono /-
theorem IsLocalMaxOn.bicomp_mono [Preorder δ] {op : β → γ → δ}
    (hop : ((· ≤ ·) ⇒ (· ≤ ·) ⇒ (· ≤ ·)) op op) (hf : IsLocalMaxOn f s a) {g : α → γ}
    (hg : IsLocalMaxOn g s a) : IsLocalMaxOn (fun x => op (f x) (g x)) s a :=
  hf.bicomp_mono hop hg
#align is_local_max_on.bicomp_mono IsLocalMaxOn.bicomp_mono
-/

/-! ### Composition with `continuous_at` -/


#print IsLocalMin.comp_continuous /-
theorem IsLocalMin.comp_continuous [TopologicalSpace δ] {g : δ → α} {b : δ}
    (hf : IsLocalMin f (g b)) (hg : ContinuousAt g b) : IsLocalMin (f ∘ g) b :=
  hg hf
#align is_local_min.comp_continuous IsLocalMin.comp_continuous
-/

#print IsLocalMax.comp_continuous /-
theorem IsLocalMax.comp_continuous [TopologicalSpace δ] {g : δ → α} {b : δ}
    (hf : IsLocalMax f (g b)) (hg : ContinuousAt g b) : IsLocalMax (f ∘ g) b :=
  hg hf
#align is_local_max.comp_continuous IsLocalMax.comp_continuous
-/

#print IsLocalExtr.comp_continuous /-
theorem IsLocalExtr.comp_continuous [TopologicalSpace δ] {g : δ → α} {b : δ}
    (hf : IsLocalExtr f (g b)) (hg : ContinuousAt g b) : IsLocalExtr (f ∘ g) b :=
  hf.comp_tendsto hg
#align is_local_extr.comp_continuous IsLocalExtr.comp_continuous
-/

#print IsLocalMin.comp_continuousOn /-
theorem IsLocalMin.comp_continuousOn [TopologicalSpace δ] {s : Set δ} {g : δ → α} {b : δ}
    (hf : IsLocalMin f (g b)) (hg : ContinuousOn g s) (hb : b ∈ s) : IsLocalMinOn (f ∘ g) s b :=
  hf.comp_tendsto (hg b hb)
#align is_local_min.comp_continuous_on IsLocalMin.comp_continuousOn
-/

#print IsLocalMax.comp_continuousOn /-
theorem IsLocalMax.comp_continuousOn [TopologicalSpace δ] {s : Set δ} {g : δ → α} {b : δ}
    (hf : IsLocalMax f (g b)) (hg : ContinuousOn g s) (hb : b ∈ s) : IsLocalMaxOn (f ∘ g) s b :=
  hf.comp_tendsto (hg b hb)
#align is_local_max.comp_continuous_on IsLocalMax.comp_continuousOn
-/

#print IsLocalExtr.comp_continuousOn /-
theorem IsLocalExtr.comp_continuousOn [TopologicalSpace δ] {s : Set δ} (g : δ → α) {b : δ}
    (hf : IsLocalExtr f (g b)) (hg : ContinuousOn g s) (hb : b ∈ s) : IsLocalExtrOn (f ∘ g) s b :=
  hf.elim (fun hf => (hf.comp_continuousOn hg hb).isExtr) fun hf =>
    (IsLocalMax.comp_continuousOn hf hg hb).isExtr
#align is_local_extr.comp_continuous_on IsLocalExtr.comp_continuousOn
-/

#print IsLocalMinOn.comp_continuousOn /-
theorem IsLocalMinOn.comp_continuousOn [TopologicalSpace δ] {t : Set α} {s : Set δ} {g : δ → α}
    {b : δ} (hf : IsLocalMinOn f t (g b)) (hst : s ⊆ g ⁻¹' t) (hg : ContinuousOn g s) (hb : b ∈ s) :
    IsLocalMinOn (f ∘ g) s b :=
  hf.comp_tendsto
    (tendsto_nhdsWithin_mono_right (image_subset_iff.mpr hst)
      (ContinuousWithinAt.tendsto_nhdsWithin_image (hg b hb)))
#align is_local_min_on.comp_continuous_on IsLocalMinOn.comp_continuousOn
-/

#print IsLocalMaxOn.comp_continuousOn /-
theorem IsLocalMaxOn.comp_continuousOn [TopologicalSpace δ] {t : Set α} {s : Set δ} {g : δ → α}
    {b : δ} (hf : IsLocalMaxOn f t (g b)) (hst : s ⊆ g ⁻¹' t) (hg : ContinuousOn g s) (hb : b ∈ s) :
    IsLocalMaxOn (f ∘ g) s b :=
  hf.comp_tendsto
    (tendsto_nhdsWithin_mono_right (image_subset_iff.mpr hst)
      (ContinuousWithinAt.tendsto_nhdsWithin_image (hg b hb)))
#align is_local_max_on.comp_continuous_on IsLocalMaxOn.comp_continuousOn
-/

#print IsLocalExtrOn.comp_continuousOn /-
theorem IsLocalExtrOn.comp_continuousOn [TopologicalSpace δ] {t : Set α} {s : Set δ} (g : δ → α)
    {b : δ} (hf : IsLocalExtrOn f t (g b)) (hst : s ⊆ g ⁻¹' t) (hg : ContinuousOn g s)
    (hb : b ∈ s) : IsLocalExtrOn (f ∘ g) s b :=
  hf.elim (fun hf => (hf.comp_continuousOn hst hg hb).isExtr) fun hf =>
    (IsLocalMaxOn.comp_continuousOn hf hst hg hb).isExtr
#align is_local_extr_on.comp_continuous_on IsLocalExtrOn.comp_continuousOn
-/

end Preorder

/-! ### Pointwise addition -/


section OrderedAddCommMonoid

variable [OrderedAddCommMonoid β] {f g : α → β} {a : α} {s : Set α} {l : Filter α}

/- warning: is_local_min.add -> IsLocalMin.add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OrderedAddCommMonoid.{u2} β] {f : α -> β} {g : α -> β} {a : α}, (IsLocalMin.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β _inst_2)) f a) -> (IsLocalMin.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β _inst_2)) g a) -> (IsLocalMin.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β _inst_2)) (fun (x : α) => HAdd.hAdd.{u2, u2, u2} β β β (instHAdd.{u2} β (AddZeroClass.toHasAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (OrderedAddCommMonoid.toAddCommMonoid.{u2} β _inst_2))))) (f x) (g x)) a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OrderedAddCommMonoid.{u2} β] {f : α -> β} {g : α -> β} {a : α}, (IsLocalMin.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β _inst_2)) f a) -> (IsLocalMin.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β _inst_2)) g a) -> (IsLocalMin.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β _inst_2)) (fun (x : α) => HAdd.hAdd.{u2, u2, u2} β β β (instHAdd.{u2} β (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (OrderedAddCommMonoid.toAddCommMonoid.{u2} β _inst_2))))) (f x) (g x)) a)
Case conversion may be inaccurate. Consider using '#align is_local_min.add IsLocalMin.addₓ'. -/
theorem IsLocalMin.add (hf : IsLocalMin f a) (hg : IsLocalMin g a) :
    IsLocalMin (fun x => f x + g x) a :=
  hf.add hg
#align is_local_min.add IsLocalMin.add

/- warning: is_local_max.add -> IsLocalMax.add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OrderedAddCommMonoid.{u2} β] {f : α -> β} {g : α -> β} {a : α}, (IsLocalMax.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β _inst_2)) f a) -> (IsLocalMax.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β _inst_2)) g a) -> (IsLocalMax.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β _inst_2)) (fun (x : α) => HAdd.hAdd.{u2, u2, u2} β β β (instHAdd.{u2} β (AddZeroClass.toHasAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (OrderedAddCommMonoid.toAddCommMonoid.{u2} β _inst_2))))) (f x) (g x)) a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OrderedAddCommMonoid.{u2} β] {f : α -> β} {g : α -> β} {a : α}, (IsLocalMax.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β _inst_2)) f a) -> (IsLocalMax.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β _inst_2)) g a) -> (IsLocalMax.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β _inst_2)) (fun (x : α) => HAdd.hAdd.{u2, u2, u2} β β β (instHAdd.{u2} β (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (OrderedAddCommMonoid.toAddCommMonoid.{u2} β _inst_2))))) (f x) (g x)) a)
Case conversion may be inaccurate. Consider using '#align is_local_max.add IsLocalMax.addₓ'. -/
theorem IsLocalMax.add (hf : IsLocalMax f a) (hg : IsLocalMax g a) :
    IsLocalMax (fun x => f x + g x) a :=
  hf.add hg
#align is_local_max.add IsLocalMax.add

/- warning: is_local_min_on.add -> IsLocalMinOn.add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OrderedAddCommMonoid.{u2} β] {f : α -> β} {g : α -> β} {a : α} {s : Set.{u1} α}, (IsLocalMinOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β _inst_2)) f s a) -> (IsLocalMinOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β _inst_2)) g s a) -> (IsLocalMinOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β _inst_2)) (fun (x : α) => HAdd.hAdd.{u2, u2, u2} β β β (instHAdd.{u2} β (AddZeroClass.toHasAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (OrderedAddCommMonoid.toAddCommMonoid.{u2} β _inst_2))))) (f x) (g x)) s a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OrderedAddCommMonoid.{u2} β] {f : α -> β} {g : α -> β} {a : α} {s : Set.{u1} α}, (IsLocalMinOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β _inst_2)) f s a) -> (IsLocalMinOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β _inst_2)) g s a) -> (IsLocalMinOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β _inst_2)) (fun (x : α) => HAdd.hAdd.{u2, u2, u2} β β β (instHAdd.{u2} β (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (OrderedAddCommMonoid.toAddCommMonoid.{u2} β _inst_2))))) (f x) (g x)) s a)
Case conversion may be inaccurate. Consider using '#align is_local_min_on.add IsLocalMinOn.addₓ'. -/
theorem IsLocalMinOn.add (hf : IsLocalMinOn f s a) (hg : IsLocalMinOn g s a) :
    IsLocalMinOn (fun x => f x + g x) s a :=
  hf.add hg
#align is_local_min_on.add IsLocalMinOn.add

/- warning: is_local_max_on.add -> IsLocalMaxOn.add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OrderedAddCommMonoid.{u2} β] {f : α -> β} {g : α -> β} {a : α} {s : Set.{u1} α}, (IsLocalMaxOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β _inst_2)) f s a) -> (IsLocalMaxOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β _inst_2)) g s a) -> (IsLocalMaxOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β _inst_2)) (fun (x : α) => HAdd.hAdd.{u2, u2, u2} β β β (instHAdd.{u2} β (AddZeroClass.toHasAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (OrderedAddCommMonoid.toAddCommMonoid.{u2} β _inst_2))))) (f x) (g x)) s a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OrderedAddCommMonoid.{u2} β] {f : α -> β} {g : α -> β} {a : α} {s : Set.{u1} α}, (IsLocalMaxOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β _inst_2)) f s a) -> (IsLocalMaxOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β _inst_2)) g s a) -> (IsLocalMaxOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β _inst_2)) (fun (x : α) => HAdd.hAdd.{u2, u2, u2} β β β (instHAdd.{u2} β (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (OrderedAddCommMonoid.toAddCommMonoid.{u2} β _inst_2))))) (f x) (g x)) s a)
Case conversion may be inaccurate. Consider using '#align is_local_max_on.add IsLocalMaxOn.addₓ'. -/
theorem IsLocalMaxOn.add (hf : IsLocalMaxOn f s a) (hg : IsLocalMaxOn g s a) :
    IsLocalMaxOn (fun x => f x + g x) s a :=
  hf.add hg
#align is_local_max_on.add IsLocalMaxOn.add

end OrderedAddCommMonoid

/-! ### Pointwise negation and subtraction -/


section OrderedAddCommGroup

variable [OrderedAddCommGroup β] {f g : α → β} {a : α} {s : Set α} {l : Filter α}

/- warning: is_local_min.neg -> IsLocalMin.neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OrderedAddCommGroup.{u2} β] {f : α -> β} {a : α}, (IsLocalMin.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) f a) -> (IsLocalMax.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) (fun (x : α) => Neg.neg.{u2} β (SubNegMonoid.toHasNeg.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β (OrderedAddCommGroup.toAddCommGroup.{u2} β _inst_2)))) (f x)) a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OrderedAddCommGroup.{u2} β] {f : α -> β} {a : α}, (IsLocalMin.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) f a) -> (IsLocalMax.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) (fun (x : α) => Neg.neg.{u2} β (NegZeroClass.toNeg.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β (OrderedAddCommGroup.toAddCommGroup.{u2} β _inst_2)))))) (f x)) a)
Case conversion may be inaccurate. Consider using '#align is_local_min.neg IsLocalMin.negₓ'. -/
theorem IsLocalMin.neg (hf : IsLocalMin f a) : IsLocalMax (fun x => -f x) a :=
  hf.neg
#align is_local_min.neg IsLocalMin.neg

/- warning: is_local_max.neg -> IsLocalMax.neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OrderedAddCommGroup.{u2} β] {f : α -> β} {a : α}, (IsLocalMax.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) f a) -> (IsLocalMin.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) (fun (x : α) => Neg.neg.{u2} β (SubNegMonoid.toHasNeg.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β (OrderedAddCommGroup.toAddCommGroup.{u2} β _inst_2)))) (f x)) a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OrderedAddCommGroup.{u2} β] {f : α -> β} {a : α}, (IsLocalMax.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) f a) -> (IsLocalMin.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) (fun (x : α) => Neg.neg.{u2} β (NegZeroClass.toNeg.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β (OrderedAddCommGroup.toAddCommGroup.{u2} β _inst_2)))))) (f x)) a)
Case conversion may be inaccurate. Consider using '#align is_local_max.neg IsLocalMax.negₓ'. -/
theorem IsLocalMax.neg (hf : IsLocalMax f a) : IsLocalMin (fun x => -f x) a :=
  hf.neg
#align is_local_max.neg IsLocalMax.neg

/- warning: is_local_extr.neg -> IsLocalExtr.neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OrderedAddCommGroup.{u2} β] {f : α -> β} {a : α}, (IsLocalExtr.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) f a) -> (IsLocalExtr.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) (fun (x : α) => Neg.neg.{u2} β (SubNegMonoid.toHasNeg.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β (OrderedAddCommGroup.toAddCommGroup.{u2} β _inst_2)))) (f x)) a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OrderedAddCommGroup.{u2} β] {f : α -> β} {a : α}, (IsLocalExtr.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) f a) -> (IsLocalExtr.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) (fun (x : α) => Neg.neg.{u2} β (NegZeroClass.toNeg.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β (OrderedAddCommGroup.toAddCommGroup.{u2} β _inst_2)))))) (f x)) a)
Case conversion may be inaccurate. Consider using '#align is_local_extr.neg IsLocalExtr.negₓ'. -/
theorem IsLocalExtr.neg (hf : IsLocalExtr f a) : IsLocalExtr (fun x => -f x) a :=
  hf.neg
#align is_local_extr.neg IsLocalExtr.neg

/- warning: is_local_min_on.neg -> IsLocalMinOn.neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OrderedAddCommGroup.{u2} β] {f : α -> β} {a : α} {s : Set.{u1} α}, (IsLocalMinOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) f s a) -> (IsLocalMaxOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) (fun (x : α) => Neg.neg.{u2} β (SubNegMonoid.toHasNeg.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β (OrderedAddCommGroup.toAddCommGroup.{u2} β _inst_2)))) (f x)) s a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OrderedAddCommGroup.{u2} β] {f : α -> β} {a : α} {s : Set.{u1} α}, (IsLocalMinOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) f s a) -> (IsLocalMaxOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) (fun (x : α) => Neg.neg.{u2} β (NegZeroClass.toNeg.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β (OrderedAddCommGroup.toAddCommGroup.{u2} β _inst_2)))))) (f x)) s a)
Case conversion may be inaccurate. Consider using '#align is_local_min_on.neg IsLocalMinOn.negₓ'. -/
theorem IsLocalMinOn.neg (hf : IsLocalMinOn f s a) : IsLocalMaxOn (fun x => -f x) s a :=
  hf.neg
#align is_local_min_on.neg IsLocalMinOn.neg

/- warning: is_local_max_on.neg -> IsLocalMaxOn.neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OrderedAddCommGroup.{u2} β] {f : α -> β} {a : α} {s : Set.{u1} α}, (IsLocalMaxOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) f s a) -> (IsLocalMinOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) (fun (x : α) => Neg.neg.{u2} β (SubNegMonoid.toHasNeg.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β (OrderedAddCommGroup.toAddCommGroup.{u2} β _inst_2)))) (f x)) s a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OrderedAddCommGroup.{u2} β] {f : α -> β} {a : α} {s : Set.{u1} α}, (IsLocalMaxOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) f s a) -> (IsLocalMinOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) (fun (x : α) => Neg.neg.{u2} β (NegZeroClass.toNeg.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β (OrderedAddCommGroup.toAddCommGroup.{u2} β _inst_2)))))) (f x)) s a)
Case conversion may be inaccurate. Consider using '#align is_local_max_on.neg IsLocalMaxOn.negₓ'. -/
theorem IsLocalMaxOn.neg (hf : IsLocalMaxOn f s a) : IsLocalMinOn (fun x => -f x) s a :=
  hf.neg
#align is_local_max_on.neg IsLocalMaxOn.neg

/- warning: is_local_extr_on.neg -> IsLocalExtrOn.neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OrderedAddCommGroup.{u2} β] {f : α -> β} {a : α} {s : Set.{u1} α}, (IsLocalExtrOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) f s a) -> (IsLocalExtrOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) (fun (x : α) => Neg.neg.{u2} β (SubNegMonoid.toHasNeg.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β (OrderedAddCommGroup.toAddCommGroup.{u2} β _inst_2)))) (f x)) s a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OrderedAddCommGroup.{u2} β] {f : α -> β} {a : α} {s : Set.{u1} α}, (IsLocalExtrOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) f s a) -> (IsLocalExtrOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) (fun (x : α) => Neg.neg.{u2} β (NegZeroClass.toNeg.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β (OrderedAddCommGroup.toAddCommGroup.{u2} β _inst_2)))))) (f x)) s a)
Case conversion may be inaccurate. Consider using '#align is_local_extr_on.neg IsLocalExtrOn.negₓ'. -/
theorem IsLocalExtrOn.neg (hf : IsLocalExtrOn f s a) : IsLocalExtrOn (fun x => -f x) s a :=
  hf.neg
#align is_local_extr_on.neg IsLocalExtrOn.neg

/- warning: is_local_min.sub -> IsLocalMin.sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OrderedAddCommGroup.{u2} β] {f : α -> β} {g : α -> β} {a : α}, (IsLocalMin.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) f a) -> (IsLocalMax.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) g a) -> (IsLocalMin.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) (fun (x : α) => HSub.hSub.{u2, u2, u2} β β β (instHSub.{u2} β (SubNegMonoid.toHasSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β (OrderedAddCommGroup.toAddCommGroup.{u2} β _inst_2))))) (f x) (g x)) a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OrderedAddCommGroup.{u2} β] {f : α -> β} {g : α -> β} {a : α}, (IsLocalMin.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) f a) -> (IsLocalMax.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) g a) -> (IsLocalMin.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) (fun (x : α) => HSub.hSub.{u2, u2, u2} β β β (instHSub.{u2} β (SubNegMonoid.toSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β (OrderedAddCommGroup.toAddCommGroup.{u2} β _inst_2))))) (f x) (g x)) a)
Case conversion may be inaccurate. Consider using '#align is_local_min.sub IsLocalMin.subₓ'. -/
theorem IsLocalMin.sub (hf : IsLocalMin f a) (hg : IsLocalMax g a) :
    IsLocalMin (fun x => f x - g x) a :=
  hf.sub hg
#align is_local_min.sub IsLocalMin.sub

/- warning: is_local_max.sub -> IsLocalMax.sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OrderedAddCommGroup.{u2} β] {f : α -> β} {g : α -> β} {a : α}, (IsLocalMax.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) f a) -> (IsLocalMin.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) g a) -> (IsLocalMax.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) (fun (x : α) => HSub.hSub.{u2, u2, u2} β β β (instHSub.{u2} β (SubNegMonoid.toHasSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β (OrderedAddCommGroup.toAddCommGroup.{u2} β _inst_2))))) (f x) (g x)) a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OrderedAddCommGroup.{u2} β] {f : α -> β} {g : α -> β} {a : α}, (IsLocalMax.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) f a) -> (IsLocalMin.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) g a) -> (IsLocalMax.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) (fun (x : α) => HSub.hSub.{u2, u2, u2} β β β (instHSub.{u2} β (SubNegMonoid.toSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β (OrderedAddCommGroup.toAddCommGroup.{u2} β _inst_2))))) (f x) (g x)) a)
Case conversion may be inaccurate. Consider using '#align is_local_max.sub IsLocalMax.subₓ'. -/
theorem IsLocalMax.sub (hf : IsLocalMax f a) (hg : IsLocalMin g a) :
    IsLocalMax (fun x => f x - g x) a :=
  hf.sub hg
#align is_local_max.sub IsLocalMax.sub

/- warning: is_local_min_on.sub -> IsLocalMinOn.sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OrderedAddCommGroup.{u2} β] {f : α -> β} {g : α -> β} {a : α} {s : Set.{u1} α}, (IsLocalMinOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) f s a) -> (IsLocalMaxOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) g s a) -> (IsLocalMinOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) (fun (x : α) => HSub.hSub.{u2, u2, u2} β β β (instHSub.{u2} β (SubNegMonoid.toHasSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β (OrderedAddCommGroup.toAddCommGroup.{u2} β _inst_2))))) (f x) (g x)) s a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OrderedAddCommGroup.{u2} β] {f : α -> β} {g : α -> β} {a : α} {s : Set.{u1} α}, (IsLocalMinOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) f s a) -> (IsLocalMaxOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) g s a) -> (IsLocalMinOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) (fun (x : α) => HSub.hSub.{u2, u2, u2} β β β (instHSub.{u2} β (SubNegMonoid.toSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β (OrderedAddCommGroup.toAddCommGroup.{u2} β _inst_2))))) (f x) (g x)) s a)
Case conversion may be inaccurate. Consider using '#align is_local_min_on.sub IsLocalMinOn.subₓ'. -/
theorem IsLocalMinOn.sub (hf : IsLocalMinOn f s a) (hg : IsLocalMaxOn g s a) :
    IsLocalMinOn (fun x => f x - g x) s a :=
  hf.sub hg
#align is_local_min_on.sub IsLocalMinOn.sub

/- warning: is_local_max_on.sub -> IsLocalMaxOn.sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OrderedAddCommGroup.{u2} β] {f : α -> β} {g : α -> β} {a : α} {s : Set.{u1} α}, (IsLocalMaxOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) f s a) -> (IsLocalMinOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) g s a) -> (IsLocalMaxOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) (fun (x : α) => HSub.hSub.{u2, u2, u2} β β β (instHSub.{u2} β (SubNegMonoid.toHasSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β (OrderedAddCommGroup.toAddCommGroup.{u2} β _inst_2))))) (f x) (g x)) s a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OrderedAddCommGroup.{u2} β] {f : α -> β} {g : α -> β} {a : α} {s : Set.{u1} α}, (IsLocalMaxOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) f s a) -> (IsLocalMinOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) g s a) -> (IsLocalMaxOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (OrderedAddCommGroup.toPartialOrder.{u2} β _inst_2)) (fun (x : α) => HSub.hSub.{u2, u2, u2} β β β (instHSub.{u2} β (SubNegMonoid.toSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β (OrderedAddCommGroup.toAddCommGroup.{u2} β _inst_2))))) (f x) (g x)) s a)
Case conversion may be inaccurate. Consider using '#align is_local_max_on.sub IsLocalMaxOn.subₓ'. -/
theorem IsLocalMaxOn.sub (hf : IsLocalMaxOn f s a) (hg : IsLocalMinOn g s a) :
    IsLocalMaxOn (fun x => f x - g x) s a :=
  hf.sub hg
#align is_local_max_on.sub IsLocalMaxOn.sub

end OrderedAddCommGroup

/-! ### Pointwise `sup`/`inf` -/


section SemilatticeSup

variable [SemilatticeSup β] {f g : α → β} {a : α} {s : Set α} {l : Filter α}

#print IsLocalMin.sup /-
theorem IsLocalMin.sup (hf : IsLocalMin f a) (hg : IsLocalMin g a) :
    IsLocalMin (fun x => f x ⊔ g x) a :=
  hf.sup hg
#align is_local_min.sup IsLocalMin.sup
-/

#print IsLocalMax.sup /-
theorem IsLocalMax.sup (hf : IsLocalMax f a) (hg : IsLocalMax g a) :
    IsLocalMax (fun x => f x ⊔ g x) a :=
  hf.sup hg
#align is_local_max.sup IsLocalMax.sup
-/

#print IsLocalMinOn.sup /-
theorem IsLocalMinOn.sup (hf : IsLocalMinOn f s a) (hg : IsLocalMinOn g s a) :
    IsLocalMinOn (fun x => f x ⊔ g x) s a :=
  hf.sup hg
#align is_local_min_on.sup IsLocalMinOn.sup
-/

#print IsLocalMaxOn.sup /-
theorem IsLocalMaxOn.sup (hf : IsLocalMaxOn f s a) (hg : IsLocalMaxOn g s a) :
    IsLocalMaxOn (fun x => f x ⊔ g x) s a :=
  hf.sup hg
#align is_local_max_on.sup IsLocalMaxOn.sup
-/

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf β] {f g : α → β} {a : α} {s : Set α} {l : Filter α}

#print IsLocalMin.inf /-
theorem IsLocalMin.inf (hf : IsLocalMin f a) (hg : IsLocalMin g a) :
    IsLocalMin (fun x => f x ⊓ g x) a :=
  hf.inf hg
#align is_local_min.inf IsLocalMin.inf
-/

#print IsLocalMax.inf /-
theorem IsLocalMax.inf (hf : IsLocalMax f a) (hg : IsLocalMax g a) :
    IsLocalMax (fun x => f x ⊓ g x) a :=
  hf.inf hg
#align is_local_max.inf IsLocalMax.inf
-/

#print IsLocalMinOn.inf /-
theorem IsLocalMinOn.inf (hf : IsLocalMinOn f s a) (hg : IsLocalMinOn g s a) :
    IsLocalMinOn (fun x => f x ⊓ g x) s a :=
  hf.inf hg
#align is_local_min_on.inf IsLocalMinOn.inf
-/

#print IsLocalMaxOn.inf /-
theorem IsLocalMaxOn.inf (hf : IsLocalMaxOn f s a) (hg : IsLocalMaxOn g s a) :
    IsLocalMaxOn (fun x => f x ⊓ g x) s a :=
  hf.inf hg
#align is_local_max_on.inf IsLocalMaxOn.inf
-/

end SemilatticeInf

/-! ### Pointwise `min`/`max` -/


section LinearOrder

variable [LinearOrder β] {f g : α → β} {a : α} {s : Set α} {l : Filter α}

/- warning: is_local_min.min -> IsLocalMin.min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LinearOrder.{u2} β] {f : α -> β} {g : α -> β} {a : α}, (IsLocalMin.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) f a) -> (IsLocalMin.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) g a) -> (IsLocalMin.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) (fun (x : α) => LinearOrder.min.{u2} β _inst_2 (f x) (g x)) a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LinearOrder.{u2} β] {f : α -> β} {g : α -> β} {a : α}, (IsLocalMin.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) f a) -> (IsLocalMin.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) g a) -> (IsLocalMin.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) (fun (x : α) => Min.min.{u2} β (LinearOrder.toMin.{u2} β _inst_2) (f x) (g x)) a)
Case conversion may be inaccurate. Consider using '#align is_local_min.min IsLocalMin.minₓ'. -/
theorem IsLocalMin.min (hf : IsLocalMin f a) (hg : IsLocalMin g a) :
    IsLocalMin (fun x => min (f x) (g x)) a :=
  hf.min hg
#align is_local_min.min IsLocalMin.min

/- warning: is_local_max.min -> IsLocalMax.min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LinearOrder.{u2} β] {f : α -> β} {g : α -> β} {a : α}, (IsLocalMax.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) f a) -> (IsLocalMax.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) g a) -> (IsLocalMax.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) (fun (x : α) => LinearOrder.min.{u2} β _inst_2 (f x) (g x)) a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LinearOrder.{u2} β] {f : α -> β} {g : α -> β} {a : α}, (IsLocalMax.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) f a) -> (IsLocalMax.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) g a) -> (IsLocalMax.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) (fun (x : α) => Min.min.{u2} β (LinearOrder.toMin.{u2} β _inst_2) (f x) (g x)) a)
Case conversion may be inaccurate. Consider using '#align is_local_max.min IsLocalMax.minₓ'. -/
theorem IsLocalMax.min (hf : IsLocalMax f a) (hg : IsLocalMax g a) :
    IsLocalMax (fun x => min (f x) (g x)) a :=
  hf.min hg
#align is_local_max.min IsLocalMax.min

/- warning: is_local_min_on.min -> IsLocalMinOn.min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LinearOrder.{u2} β] {f : α -> β} {g : α -> β} {a : α} {s : Set.{u1} α}, (IsLocalMinOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) f s a) -> (IsLocalMinOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) g s a) -> (IsLocalMinOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) (fun (x : α) => LinearOrder.min.{u2} β _inst_2 (f x) (g x)) s a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LinearOrder.{u2} β] {f : α -> β} {g : α -> β} {a : α} {s : Set.{u1} α}, (IsLocalMinOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) f s a) -> (IsLocalMinOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) g s a) -> (IsLocalMinOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) (fun (x : α) => Min.min.{u2} β (LinearOrder.toMin.{u2} β _inst_2) (f x) (g x)) s a)
Case conversion may be inaccurate. Consider using '#align is_local_min_on.min IsLocalMinOn.minₓ'. -/
theorem IsLocalMinOn.min (hf : IsLocalMinOn f s a) (hg : IsLocalMinOn g s a) :
    IsLocalMinOn (fun x => min (f x) (g x)) s a :=
  hf.min hg
#align is_local_min_on.min IsLocalMinOn.min

/- warning: is_local_max_on.min -> IsLocalMaxOn.min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LinearOrder.{u2} β] {f : α -> β} {g : α -> β} {a : α} {s : Set.{u1} α}, (IsLocalMaxOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) f s a) -> (IsLocalMaxOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) g s a) -> (IsLocalMaxOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) (fun (x : α) => LinearOrder.min.{u2} β _inst_2 (f x) (g x)) s a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LinearOrder.{u2} β] {f : α -> β} {g : α -> β} {a : α} {s : Set.{u1} α}, (IsLocalMaxOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) f s a) -> (IsLocalMaxOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) g s a) -> (IsLocalMaxOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) (fun (x : α) => Min.min.{u2} β (LinearOrder.toMin.{u2} β _inst_2) (f x) (g x)) s a)
Case conversion may be inaccurate. Consider using '#align is_local_max_on.min IsLocalMaxOn.minₓ'. -/
theorem IsLocalMaxOn.min (hf : IsLocalMaxOn f s a) (hg : IsLocalMaxOn g s a) :
    IsLocalMaxOn (fun x => min (f x) (g x)) s a :=
  hf.min hg
#align is_local_max_on.min IsLocalMaxOn.min

/- warning: is_local_min.max -> IsLocalMin.max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LinearOrder.{u2} β] {f : α -> β} {g : α -> β} {a : α}, (IsLocalMin.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) f a) -> (IsLocalMin.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) g a) -> (IsLocalMin.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) (fun (x : α) => LinearOrder.max.{u2} β _inst_2 (f x) (g x)) a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LinearOrder.{u2} β] {f : α -> β} {g : α -> β} {a : α}, (IsLocalMin.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) f a) -> (IsLocalMin.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) g a) -> (IsLocalMin.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) (fun (x : α) => Max.max.{u2} β (LinearOrder.toMax.{u2} β _inst_2) (f x) (g x)) a)
Case conversion may be inaccurate. Consider using '#align is_local_min.max IsLocalMin.maxₓ'. -/
theorem IsLocalMin.max (hf : IsLocalMin f a) (hg : IsLocalMin g a) :
    IsLocalMin (fun x => max (f x) (g x)) a :=
  hf.max hg
#align is_local_min.max IsLocalMin.max

/- warning: is_local_max.max -> IsLocalMax.max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LinearOrder.{u2} β] {f : α -> β} {g : α -> β} {a : α}, (IsLocalMax.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) f a) -> (IsLocalMax.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) g a) -> (IsLocalMax.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) (fun (x : α) => LinearOrder.max.{u2} β _inst_2 (f x) (g x)) a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LinearOrder.{u2} β] {f : α -> β} {g : α -> β} {a : α}, (IsLocalMax.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) f a) -> (IsLocalMax.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) g a) -> (IsLocalMax.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) (fun (x : α) => Max.max.{u2} β (LinearOrder.toMax.{u2} β _inst_2) (f x) (g x)) a)
Case conversion may be inaccurate. Consider using '#align is_local_max.max IsLocalMax.maxₓ'. -/
theorem IsLocalMax.max (hf : IsLocalMax f a) (hg : IsLocalMax g a) :
    IsLocalMax (fun x => max (f x) (g x)) a :=
  hf.max hg
#align is_local_max.max IsLocalMax.max

/- warning: is_local_min_on.max -> IsLocalMinOn.max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LinearOrder.{u2} β] {f : α -> β} {g : α -> β} {a : α} {s : Set.{u1} α}, (IsLocalMinOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) f s a) -> (IsLocalMinOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) g s a) -> (IsLocalMinOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) (fun (x : α) => LinearOrder.max.{u2} β _inst_2 (f x) (g x)) s a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LinearOrder.{u2} β] {f : α -> β} {g : α -> β} {a : α} {s : Set.{u1} α}, (IsLocalMinOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) f s a) -> (IsLocalMinOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) g s a) -> (IsLocalMinOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) (fun (x : α) => Max.max.{u2} β (LinearOrder.toMax.{u2} β _inst_2) (f x) (g x)) s a)
Case conversion may be inaccurate. Consider using '#align is_local_min_on.max IsLocalMinOn.maxₓ'. -/
theorem IsLocalMinOn.max (hf : IsLocalMinOn f s a) (hg : IsLocalMinOn g s a) :
    IsLocalMinOn (fun x => max (f x) (g x)) s a :=
  hf.max hg
#align is_local_min_on.max IsLocalMinOn.max

/- warning: is_local_max_on.max -> IsLocalMaxOn.max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LinearOrder.{u2} β] {f : α -> β} {g : α -> β} {a : α} {s : Set.{u1} α}, (IsLocalMaxOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) f s a) -> (IsLocalMaxOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) g s a) -> (IsLocalMaxOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) (fun (x : α) => LinearOrder.max.{u2} β _inst_2 (f x) (g x)) s a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LinearOrder.{u2} β] {f : α -> β} {g : α -> β} {a : α} {s : Set.{u1} α}, (IsLocalMaxOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) f s a) -> (IsLocalMaxOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) g s a) -> (IsLocalMaxOn.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) (fun (x : α) => Max.max.{u2} β (LinearOrder.toMax.{u2} β _inst_2) (f x) (g x)) s a)
Case conversion may be inaccurate. Consider using '#align is_local_max_on.max IsLocalMaxOn.maxₓ'. -/
theorem IsLocalMaxOn.max (hf : IsLocalMaxOn f s a) (hg : IsLocalMaxOn g s a) :
    IsLocalMaxOn (fun x => max (f x) (g x)) s a :=
  hf.max hg
#align is_local_max_on.max IsLocalMaxOn.max

end LinearOrder

section Eventually

/-! ### Relation with `eventually` comparisons of two functions -/


variable [Preorder β] {s : Set α}

#print Filter.EventuallyLe.isLocalMaxOn /-
theorem Filter.EventuallyLe.isLocalMaxOn {f g : α → β} {a : α} (hle : g ≤ᶠ[𝓝[s] a] f)
    (hfga : f a = g a) (h : IsLocalMaxOn f s a) : IsLocalMaxOn g s a :=
  hle.IsMaxFilter hfga h
#align filter.eventually_le.is_local_max_on Filter.EventuallyLe.isLocalMaxOn
-/

#print IsLocalMaxOn.congr /-
theorem IsLocalMaxOn.congr {f g : α → β} {a : α} (h : IsLocalMaxOn f s a) (heq : f =ᶠ[𝓝[s] a] g)
    (hmem : a ∈ s) : IsLocalMaxOn g s a :=
  h.congr HEq <| HEq.eq_of_nhdsWithin hmem
#align is_local_max_on.congr IsLocalMaxOn.congr
-/

#print Filter.EventuallyEq.isLocalMaxOn_iff /-
theorem Filter.EventuallyEq.isLocalMaxOn_iff {f g : α → β} {a : α} (heq : f =ᶠ[𝓝[s] a] g)
    (hmem : a ∈ s) : IsLocalMaxOn f s a ↔ IsLocalMaxOn g s a :=
  HEq.isMaxFilter_iff <| HEq.eq_of_nhdsWithin hmem
#align filter.eventually_eq.is_local_max_on_iff Filter.EventuallyEq.isLocalMaxOn_iff
-/

#print Filter.EventuallyLe.isLocalMinOn /-
theorem Filter.EventuallyLe.isLocalMinOn {f g : α → β} {a : α} (hle : f ≤ᶠ[𝓝[s] a] g)
    (hfga : f a = g a) (h : IsLocalMinOn f s a) : IsLocalMinOn g s a :=
  hle.IsMinFilter hfga h
#align filter.eventually_le.is_local_min_on Filter.EventuallyLe.isLocalMinOn
-/

#print IsLocalMinOn.congr /-
theorem IsLocalMinOn.congr {f g : α → β} {a : α} (h : IsLocalMinOn f s a) (heq : f =ᶠ[𝓝[s] a] g)
    (hmem : a ∈ s) : IsLocalMinOn g s a :=
  h.congr HEq <| HEq.eq_of_nhdsWithin hmem
#align is_local_min_on.congr IsLocalMinOn.congr
-/

#print Filter.EventuallyEq.isLocalMinOn_iff /-
theorem Filter.EventuallyEq.isLocalMinOn_iff {f g : α → β} {a : α} (heq : f =ᶠ[𝓝[s] a] g)
    (hmem : a ∈ s) : IsLocalMinOn f s a ↔ IsLocalMinOn g s a :=
  HEq.isMinFilter_iff <| HEq.eq_of_nhdsWithin hmem
#align filter.eventually_eq.is_local_min_on_iff Filter.EventuallyEq.isLocalMinOn_iff
-/

#print IsLocalExtrOn.congr /-
theorem IsLocalExtrOn.congr {f g : α → β} {a : α} (h : IsLocalExtrOn f s a) (heq : f =ᶠ[𝓝[s] a] g)
    (hmem : a ∈ s) : IsLocalExtrOn g s a :=
  h.congr HEq <| HEq.eq_of_nhdsWithin hmem
#align is_local_extr_on.congr IsLocalExtrOn.congr
-/

#print Filter.EventuallyEq.isLocalExtrOn_iff /-
theorem Filter.EventuallyEq.isLocalExtrOn_iff {f g : α → β} {a : α} (heq : f =ᶠ[𝓝[s] a] g)
    (hmem : a ∈ s) : IsLocalExtrOn f s a ↔ IsLocalExtrOn g s a :=
  HEq.isExtrFilter_iff <| HEq.eq_of_nhdsWithin hmem
#align filter.eventually_eq.is_local_extr_on_iff Filter.EventuallyEq.isLocalExtrOn_iff
-/

#print Filter.EventuallyLe.isLocalMax /-
theorem Filter.EventuallyLe.isLocalMax {f g : α → β} {a : α} (hle : g ≤ᶠ[𝓝 a] f) (hfga : f a = g a)
    (h : IsLocalMax f a) : IsLocalMax g a :=
  hle.IsMaxFilter hfga h
#align filter.eventually_le.is_local_max Filter.EventuallyLe.isLocalMax
-/

#print IsLocalMax.congr /-
theorem IsLocalMax.congr {f g : α → β} {a : α} (h : IsLocalMax f a) (heq : f =ᶠ[𝓝 a] g) :
    IsLocalMax g a :=
  h.congr HEq HEq.eq_of_nhds
#align is_local_max.congr IsLocalMax.congr
-/

#print Filter.EventuallyEq.isLocalMax_iff /-
theorem Filter.EventuallyEq.isLocalMax_iff {f g : α → β} {a : α} (heq : f =ᶠ[𝓝 a] g) :
    IsLocalMax f a ↔ IsLocalMax g a :=
  HEq.isMaxFilter_iff HEq.eq_of_nhds
#align filter.eventually_eq.is_local_max_iff Filter.EventuallyEq.isLocalMax_iff
-/

#print Filter.EventuallyLe.isLocalMin /-
theorem Filter.EventuallyLe.isLocalMin {f g : α → β} {a : α} (hle : f ≤ᶠ[𝓝 a] g) (hfga : f a = g a)
    (h : IsLocalMin f a) : IsLocalMin g a :=
  hle.IsMinFilter hfga h
#align filter.eventually_le.is_local_min Filter.EventuallyLe.isLocalMin
-/

#print IsLocalMin.congr /-
theorem IsLocalMin.congr {f g : α → β} {a : α} (h : IsLocalMin f a) (heq : f =ᶠ[𝓝 a] g) :
    IsLocalMin g a :=
  h.congr HEq HEq.eq_of_nhds
#align is_local_min.congr IsLocalMin.congr
-/

#print Filter.EventuallyEq.isLocalMin_iff /-
theorem Filter.EventuallyEq.isLocalMin_iff {f g : α → β} {a : α} (heq : f =ᶠ[𝓝 a] g) :
    IsLocalMin f a ↔ IsLocalMin g a :=
  HEq.isMinFilter_iff HEq.eq_of_nhds
#align filter.eventually_eq.is_local_min_iff Filter.EventuallyEq.isLocalMin_iff
-/

#print IsLocalExtr.congr /-
theorem IsLocalExtr.congr {f g : α → β} {a : α} (h : IsLocalExtr f a) (heq : f =ᶠ[𝓝 a] g) :
    IsLocalExtr g a :=
  h.congr HEq HEq.eq_of_nhds
#align is_local_extr.congr IsLocalExtr.congr
-/

#print Filter.EventuallyEq.isLocalExtr_iff /-
theorem Filter.EventuallyEq.isLocalExtr_iff {f g : α → β} {a : α} (heq : f =ᶠ[𝓝 a] g) :
    IsLocalExtr f a ↔ IsLocalExtr g a :=
  HEq.isExtrFilter_iff HEq.eq_of_nhds
#align filter.eventually_eq.is_local_extr_iff Filter.EventuallyEq.isLocalExtr_iff
-/

end Eventually

