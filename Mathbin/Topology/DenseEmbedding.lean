/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot

! This file was ported from Lean 3 source module topology.dense_embedding
! leanprover-community/mathlib commit bd9851ca476957ea4549eb19b40e7b5ade9428cc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Separation
import Mathbin.Topology.Bases

/-!
# Dense embeddings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines three properties of functions:

* `dense_range f`      means `f` has dense image;
* `dense_inducing i`   means `i` is also `inducing`;
* `dense_embedding e`  means `e` is also an `embedding`.

The main theorem `continuous_extend` gives a criterion for a function
`f : X → Z` to a T₃ space Z to extend along a dense embedding
`i : X → Y` to a continuous function `g : Y → Z`. Actually `i` only
has to be `dense_inducing` (not necessarily injective).

-/


noncomputable section

open Set Filter

open Classical Topology Filter

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

#print DenseInducing /-
/-- `i : α → β` is "dense inducing" if it has dense range and the topology on `α`
  is the one induced by `i` from the topology on `β`. -/
@[protect_proj]
structure DenseInducing [TopologicalSpace α] [TopologicalSpace β] (i : α → β) extends Inducing i :
  Prop where
  dense : DenseRange i
#align dense_inducing DenseInducing
-/

namespace DenseInducing

variable [TopologicalSpace α] [TopologicalSpace β]

variable {i : α → β} (di : DenseInducing i)

/- warning: dense_inducing.nhds_eq_comap -> DenseInducing.nhds_eq_comap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {i : α -> β}, (DenseInducing.{u1, u2} α β _inst_1 _inst_2 i) -> (forall (a : α), Eq.{succ u1} (Filter.{u1} α) (nhds.{u1} α _inst_1 a) (Filter.comap.{u1, u2} α β i (nhds.{u2} β _inst_2 (i a))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {i : α -> β}, (DenseInducing.{u2, u1} α β _inst_1 _inst_2 i) -> (forall (a : α), Eq.{succ u2} (Filter.{u2} α) (nhds.{u2} α _inst_1 a) (Filter.comap.{u2, u1} α β i (nhds.{u1} β _inst_2 (i a))))
Case conversion may be inaccurate. Consider using '#align dense_inducing.nhds_eq_comap DenseInducing.nhds_eq_comapₓ'. -/
theorem nhds_eq_comap (di : DenseInducing i) : ∀ a : α, 𝓝 a = comap i (𝓝 <| i a) :=
  di.to_inducing.nhds_eq_comap
#align dense_inducing.nhds_eq_comap DenseInducing.nhds_eq_comap

/- warning: dense_inducing.continuous -> DenseInducing.continuous is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {i : α -> β}, (DenseInducing.{u1, u2} α β _inst_1 _inst_2 i) -> (Continuous.{u1, u2} α β _inst_1 _inst_2 i)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {i : α -> β}, (DenseInducing.{u2, u1} α β _inst_1 _inst_2 i) -> (Continuous.{u2, u1} α β _inst_1 _inst_2 i)
Case conversion may be inaccurate. Consider using '#align dense_inducing.continuous DenseInducing.continuousₓ'. -/
protected theorem continuous (di : DenseInducing i) : Continuous i :=
  di.to_inducing.Continuous
#align dense_inducing.continuous DenseInducing.continuous

#print DenseInducing.closure_range /-
theorem closure_range : closure (range i) = univ :=
  di.dense.closure_range
#align dense_inducing.closure_range DenseInducing.closure_range
-/

/- warning: dense_inducing.preconnected_space -> DenseInducing.preconnectedSpace is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {i : α -> β} [_inst_3 : PreconnectedSpace.{u1} α _inst_1], (DenseInducing.{u1, u2} α β _inst_1 _inst_2 i) -> (PreconnectedSpace.{u2} β _inst_2)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {i : α -> β} [_inst_3 : PreconnectedSpace.{u2} α _inst_1], (DenseInducing.{u2, u1} α β _inst_1 _inst_2 i) -> (PreconnectedSpace.{u1} β _inst_2)
Case conversion may be inaccurate. Consider using '#align dense_inducing.preconnected_space DenseInducing.preconnectedSpaceₓ'. -/
protected theorem preconnectedSpace [PreconnectedSpace α] (di : DenseInducing i) :
    PreconnectedSpace β :=
  di.dense.PreconnectedSpace di.Continuous
#align dense_inducing.preconnected_space DenseInducing.preconnectedSpace

/- warning: dense_inducing.closure_image_mem_nhds -> DenseInducing.closure_image_mem_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {i : α -> β} {s : Set.{u1} α} {a : α}, (DenseInducing.{u1, u2} α β _inst_1 _inst_2 i) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhds.{u1} α _inst_1 a)) -> (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) (closure.{u2} β _inst_2 (Set.image.{u1, u2} α β i s)) (nhds.{u2} β _inst_2 (i a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {i : α -> β} {s : Set.{u2} α} {a : α}, (DenseInducing.{u2, u1} α β _inst_1 _inst_2 i) -> (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s (nhds.{u2} α _inst_1 a)) -> (Membership.mem.{u1, u1} (Set.{u1} β) (Filter.{u1} β) (instMembershipSetFilter.{u1} β) (closure.{u1} β _inst_2 (Set.image.{u2, u1} α β i s)) (nhds.{u1} β _inst_2 (i a)))
Case conversion may be inaccurate. Consider using '#align dense_inducing.closure_image_mem_nhds DenseInducing.closure_image_mem_nhdsₓ'. -/
theorem closure_image_mem_nhds {s : Set α} {a : α} (di : DenseInducing i) (hs : s ∈ 𝓝 a) :
    closure (i '' s) ∈ 𝓝 (i a) :=
  by
  rw [di.nhds_eq_comap a, ((nhds_basis_opens _).comap _).mem_iff] at hs
  rcases hs with ⟨U, ⟨haU, hUo⟩, sub : i ⁻¹' U ⊆ s⟩
  refine' mem_of_superset (hUo.mem_nhds haU) _
  calc
    U ⊆ closure (i '' (i ⁻¹' U)) := di.dense.subset_closure_image_preimage_of_is_open hUo
    _ ⊆ closure (i '' s) := closure_mono (image_subset i sub)
    
#align dense_inducing.closure_image_mem_nhds DenseInducing.closure_image_mem_nhds

/- warning: dense_inducing.dense_image -> DenseInducing.dense_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {i : α -> β}, (DenseInducing.{u1, u2} α β _inst_1 _inst_2 i) -> (forall {s : Set.{u1} α}, Iff (Dense.{u2} β _inst_2 (Set.image.{u1, u2} α β i s)) (Dense.{u1} α _inst_1 s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {i : α -> β}, (DenseInducing.{u2, u1} α β _inst_1 _inst_2 i) -> (forall {s : Set.{u2} α}, Iff (Dense.{u1} β _inst_2 (Set.image.{u2, u1} α β i s)) (Dense.{u2} α _inst_1 s))
Case conversion may be inaccurate. Consider using '#align dense_inducing.dense_image DenseInducing.dense_imageₓ'. -/
theorem dense_image (di : DenseInducing i) {s : Set α} : Dense (i '' s) ↔ Dense s :=
  by
  refine' ⟨fun H x => _, di.dense.dense_image di.continuous⟩
  rw [di.to_inducing.closure_eq_preimage_closure_image, H.closure_eq, preimage_univ]
  trivial
#align dense_inducing.dense_image DenseInducing.dense_image

/- warning: dense_inducing.interior_compact_eq_empty -> DenseInducing.interior_compact_eq_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {i : α -> β} [_inst_3 : T2Space.{u2} β _inst_2], (DenseInducing.{u1, u2} α β _inst_1 _inst_2 i) -> (Dense.{u2} β _inst_2 (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (Set.range.{u2, succ u1} β α i))) -> (forall {s : Set.{u1} α}, (IsCompact.{u1} α _inst_1 s) -> (Eq.{succ u1} (Set.{u1} α) (interior.{u1} α _inst_1 s) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {i : α -> β} [_inst_3 : T2Space.{u2} β _inst_2], (DenseInducing.{u1, u2} α β _inst_1 _inst_2 i) -> (Dense.{u2} β _inst_2 (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) (Set.range.{u2, succ u1} β α i))) -> (forall {s : Set.{u1} α}, (IsCompact.{u1} α _inst_1 s) -> (Eq.{succ u1} (Set.{u1} α) (interior.{u1} α _inst_1 s) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))))
Case conversion may be inaccurate. Consider using '#align dense_inducing.interior_compact_eq_empty DenseInducing.interior_compact_eq_emptyₓ'. -/
/-- If `i : α → β` is a dense embedding with dense complement of the range, then any compact set in
`α` has empty interior. -/
theorem interior_compact_eq_empty [T2Space β] (di : DenseInducing i) (hd : Dense (range iᶜ))
    {s : Set α} (hs : IsCompact s) : interior s = ∅ :=
  by
  refine' eq_empty_iff_forall_not_mem.2 fun x hx => _
  rw [mem_interior_iff_mem_nhds] at hx
  have := di.closure_image_mem_nhds hx
  rw [(hs.image di.continuous).IsClosed.closure_eq] at this
  rcases hd.inter_nhds_nonempty this with ⟨y, hyi, hys⟩
  exact hyi (image_subset_range _ _ hys)
#align dense_inducing.interior_compact_eq_empty DenseInducing.interior_compact_eq_empty

/- warning: dense_inducing.prod -> DenseInducing.prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] {e₁ : α -> β} {e₂ : γ -> δ}, (DenseInducing.{u1, u2} α β _inst_1 _inst_2 e₁) -> (DenseInducing.{u3, u4} γ δ _inst_3 _inst_4 e₂) -> (DenseInducing.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (Prod.topologicalSpace.{u1, u3} α γ _inst_1 _inst_3) (Prod.topologicalSpace.{u2, u4} β δ _inst_2 _inst_4) (fun (p : Prod.{u1, u3} α γ) => Prod.mk.{u2, u4} β δ (e₁ (Prod.fst.{u1, u3} α γ p)) (e₂ (Prod.snd.{u1, u3} α γ p))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u4}} {δ : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : TopologicalSpace.{u4} γ] [_inst_4 : TopologicalSpace.{u3} δ] {e₁ : α -> β} {e₂ : γ -> δ}, (DenseInducing.{u2, u1} α β _inst_1 _inst_2 e₁) -> (DenseInducing.{u4, u3} γ δ _inst_3 _inst_4 e₂) -> (DenseInducing.{max u2 u4, max u3 u1} (Prod.{u2, u4} α γ) (Prod.{u1, u3} β δ) (instTopologicalSpaceProd.{u2, u4} α γ _inst_1 _inst_3) (instTopologicalSpaceProd.{u1, u3} β δ _inst_2 _inst_4) (fun (p : Prod.{u2, u4} α γ) => Prod.mk.{u1, u3} β δ (e₁ (Prod.fst.{u2, u4} α γ p)) (e₂ (Prod.snd.{u2, u4} α γ p))))
Case conversion may be inaccurate. Consider using '#align dense_inducing.prod DenseInducing.prodₓ'. -/
/-- The product of two dense inducings is a dense inducing -/
protected theorem prod [TopologicalSpace γ] [TopologicalSpace δ] {e₁ : α → β} {e₂ : γ → δ}
    (de₁ : DenseInducing e₁) (de₂ : DenseInducing e₂) :
    DenseInducing fun p : α × γ => (e₁ p.1, e₂ p.2) :=
  { induced := (de₁.to_inducing.prod_mk de₂.to_inducing).induced
    dense := de₁.dense.Prod_map de₂.dense }
#align dense_inducing.prod DenseInducing.prod

open TopologicalSpace

/- warning: dense_inducing.separable_space -> DenseInducing.separableSpace is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {i : α -> β}, (DenseInducing.{u1, u2} α β _inst_1 _inst_2 i) -> (forall [_inst_3 : TopologicalSpace.SeparableSpace.{u1} α _inst_1], TopologicalSpace.SeparableSpace.{u2} β _inst_2)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {i : α -> β}, (DenseInducing.{u2, u1} α β _inst_1 _inst_2 i) -> (forall [_inst_3 : TopologicalSpace.SeparableSpace.{u2} α _inst_1], TopologicalSpace.SeparableSpace.{u1} β _inst_2)
Case conversion may be inaccurate. Consider using '#align dense_inducing.separable_space DenseInducing.separableSpaceₓ'. -/
/-- If the domain of a `dense_inducing` map is a separable space, then so is the codomain. -/
protected theorem separableSpace [SeparableSpace α] : SeparableSpace β :=
  di.dense.SeparableSpace di.Continuous
#align dense_inducing.separable_space DenseInducing.separableSpace

variable [TopologicalSpace δ] {f : γ → α} {g : γ → δ} {h : δ → β}

/- warning: dense_inducing.tendsto_comap_nhds_nhds -> DenseInducing.tendsto_comap_nhds_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {i : α -> β} [_inst_3 : TopologicalSpace.{u4} δ] {f : γ -> α} {g : γ -> δ} {h : δ -> β} {d : δ} {a : α}, (DenseInducing.{u1, u2} α β _inst_1 _inst_2 i) -> (Filter.Tendsto.{u4, u2} δ β h (nhds.{u4} δ _inst_3 d) (nhds.{u2} β _inst_2 (i a))) -> (Eq.{max (succ u3) (succ u2)} (γ -> β) (Function.comp.{succ u3, succ u4, succ u2} γ δ β h g) (Function.comp.{succ u3, succ u1, succ u2} γ α β i f)) -> (Filter.Tendsto.{u3, u1} γ α f (Filter.comap.{u3, u4} γ δ g (nhds.{u4} δ _inst_3 d)) (nhds.{u1} α _inst_1 a))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u1}} {δ : Type.{u2}} [_inst_1 : TopologicalSpace.{u4} α] [_inst_2 : TopologicalSpace.{u3} β] {i : α -> β} [_inst_3 : TopologicalSpace.{u2} δ] {f : γ -> α} {g : γ -> δ} {h : δ -> β} {d : δ} {a : α}, (DenseInducing.{u4, u3} α β _inst_1 _inst_2 i) -> (Filter.Tendsto.{u2, u3} δ β h (nhds.{u2} δ _inst_3 d) (nhds.{u3} β _inst_2 (i a))) -> (Eq.{max (succ u3) (succ u1)} (γ -> β) (Function.comp.{succ u1, succ u2, succ u3} γ δ β h g) (Function.comp.{succ u1, succ u4, succ u3} γ α β i f)) -> (Filter.Tendsto.{u1, u4} γ α f (Filter.comap.{u1, u2} γ δ g (nhds.{u2} δ _inst_3 d)) (nhds.{u4} α _inst_1 a))
Case conversion may be inaccurate. Consider using '#align dense_inducing.tendsto_comap_nhds_nhds DenseInducing.tendsto_comap_nhds_nhdsₓ'. -/
/-- ```
 γ -f→ α
g↓     ↓e
 δ -h→ β
```
-/
theorem tendsto_comap_nhds_nhds {d : δ} {a : α} (di : DenseInducing i)
    (H : Tendsto h (𝓝 d) (𝓝 (i a))) (comm : h ∘ g = i ∘ f) : Tendsto f (comap g (𝓝 d)) (𝓝 a) :=
  by
  have lim1 : map g (comap g (𝓝 d)) ≤ 𝓝 d := map_comap_le
  replace lim1 : map h (map g (comap g (𝓝 d))) ≤ map h (𝓝 d) := map_mono lim1
  rw [Filter.map_map, comm, ← Filter.map_map, map_le_iff_le_comap] at lim1
  have lim2 : comap i (map h (𝓝 d)) ≤ comap i (𝓝 (i a)) := comap_mono H
  rw [← di.nhds_eq_comap] at lim2
  exact le_trans lim1 lim2
#align dense_inducing.tendsto_comap_nhds_nhds DenseInducing.tendsto_comap_nhds_nhds

/- warning: dense_inducing.nhds_within_ne_bot -> DenseInducing.nhdsWithin_neBot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {i : α -> β}, (DenseInducing.{u1, u2} α β _inst_1 _inst_2 i) -> (forall (b : β), Filter.NeBot.{u2} β (nhdsWithin.{u2} β _inst_2 b (Set.range.{u2, succ u1} β α i)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {i : α -> β}, (DenseInducing.{u2, u1} α β _inst_1 _inst_2 i) -> (forall (b : β), Filter.NeBot.{u1} β (nhdsWithin.{u1} β _inst_2 b (Set.range.{u1, succ u2} β α i)))
Case conversion may be inaccurate. Consider using '#align dense_inducing.nhds_within_ne_bot DenseInducing.nhdsWithin_neBotₓ'. -/
protected theorem nhdsWithin_neBot (di : DenseInducing i) (b : β) : NeBot (𝓝[range i] b) :=
  di.dense.nhdsWithin_neBot b
#align dense_inducing.nhds_within_ne_bot DenseInducing.nhdsWithin_neBot

/- warning: dense_inducing.comap_nhds_ne_bot -> DenseInducing.comap_nhds_neBot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {i : α -> β}, (DenseInducing.{u1, u2} α β _inst_1 _inst_2 i) -> (forall (b : β), Filter.NeBot.{u1} α (Filter.comap.{u1, u2} α β i (nhds.{u2} β _inst_2 b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {i : α -> β}, (DenseInducing.{u2, u1} α β _inst_1 _inst_2 i) -> (forall (b : β), Filter.NeBot.{u2} α (Filter.comap.{u2, u1} α β i (nhds.{u1} β _inst_2 b)))
Case conversion may be inaccurate. Consider using '#align dense_inducing.comap_nhds_ne_bot DenseInducing.comap_nhds_neBotₓ'. -/
theorem comap_nhds_neBot (di : DenseInducing i) (b : β) : NeBot (comap i (𝓝 b)) :=
  comap_neBot fun s hs =>
    let ⟨_, ⟨ha, a, rfl⟩⟩ := mem_closure_iff_nhds.1 (di.dense b) s hs
    ⟨a, ha⟩
#align dense_inducing.comap_nhds_ne_bot DenseInducing.comap_nhds_neBot

variable [TopologicalSpace γ]

#print DenseInducing.extend /-
/-- If `i : α → β` is a dense inducing, then any function `f : α → γ` "extends"
  to a function `g = extend di f : β → γ`. If `γ` is Hausdorff and `f` has a
  continuous extension, then `g` is the unique such extension. In general,
  `g` might not be continuous or even extend `f`. -/
def extend (di : DenseInducing i) (f : α → γ) (b : β) : γ :=
  @limUnder _ ⟨f (di.dense.some b)⟩ (comap i (𝓝 b)) f
#align dense_inducing.extend DenseInducing.extend
-/

/- warning: dense_inducing.extend_eq_of_tendsto -> DenseInducing.extend_eq_of_tendsto is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {i : α -> β} (di : DenseInducing.{u1, u2} α β _inst_1 _inst_2 i) [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : T2Space.{u3} γ _inst_4] {b : β} {c : γ} {f : α -> γ}, (Filter.Tendsto.{u1, u3} α γ f (Filter.comap.{u1, u2} α β i (nhds.{u2} β _inst_2 b)) (nhds.{u3} γ _inst_4 c)) -> (Eq.{succ u3} γ (DenseInducing.extend.{u1, u2, u3} α β γ _inst_1 _inst_2 i _inst_4 di f b) c)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {i : α -> β} (di : DenseInducing.{u2, u1} α β _inst_1 _inst_2 i) [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : T2Space.{u3} γ _inst_4] {b : β} {c : γ} {f : α -> γ}, (Filter.Tendsto.{u2, u3} α γ f (Filter.comap.{u2, u1} α β i (nhds.{u1} β _inst_2 b)) (nhds.{u3} γ _inst_4 c)) -> (Eq.{succ u3} γ (DenseInducing.extend.{u2, u1, u3} α β γ _inst_1 _inst_2 i _inst_4 di f b) c)
Case conversion may be inaccurate. Consider using '#align dense_inducing.extend_eq_of_tendsto DenseInducing.extend_eq_of_tendstoₓ'. -/
theorem extend_eq_of_tendsto [T2Space γ] {b : β} {c : γ} {f : α → γ}
    (hf : Tendsto f (comap i (𝓝 b)) (𝓝 c)) : di.extend f b = c :=
  haveI := di.comap_nhds_ne_bot
  hf.lim_eq
#align dense_inducing.extend_eq_of_tendsto DenseInducing.extend_eq_of_tendsto

/- warning: dense_inducing.extend_eq_at -> DenseInducing.extend_eq_at is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {i : α -> β} (di : DenseInducing.{u1, u2} α β _inst_1 _inst_2 i) [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : T2Space.{u3} γ _inst_4] {f : α -> γ} {a : α}, (ContinuousAt.{u1, u3} α γ _inst_1 _inst_4 f a) -> (Eq.{succ u3} γ (DenseInducing.extend.{u1, u2, u3} α β γ _inst_1 _inst_2 i _inst_4 di f (i a)) (f a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {i : α -> β} (di : DenseInducing.{u2, u1} α β _inst_1 _inst_2 i) [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : T2Space.{u3} γ _inst_4] {f : α -> γ} {a : α}, (ContinuousAt.{u2, u3} α γ _inst_1 _inst_4 f a) -> (Eq.{succ u3} γ (DenseInducing.extend.{u2, u1, u3} α β γ _inst_1 _inst_2 i _inst_4 di f (i a)) (f a))
Case conversion may be inaccurate. Consider using '#align dense_inducing.extend_eq_at DenseInducing.extend_eq_atₓ'. -/
theorem extend_eq_at [T2Space γ] {f : α → γ} {a : α} (hf : ContinuousAt f a) :
    di.extend f (i a) = f a :=
  extend_eq_of_tendsto _ <| di.nhds_eq_comap a ▸ hf
#align dense_inducing.extend_eq_at DenseInducing.extend_eq_at

/- warning: dense_inducing.extend_eq_at' -> DenseInducing.extend_eq_at' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {i : α -> β} (di : DenseInducing.{u1, u2} α β _inst_1 _inst_2 i) [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : T2Space.{u3} γ _inst_4] {f : α -> γ} {a : α} (c : γ), (Filter.Tendsto.{u1, u3} α γ f (nhds.{u1} α _inst_1 a) (nhds.{u3} γ _inst_4 c)) -> (Eq.{succ u3} γ (DenseInducing.extend.{u1, u2, u3} α β γ _inst_1 _inst_2 i _inst_4 di f (i a)) (f a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {i : α -> β} (di : DenseInducing.{u2, u1} α β _inst_1 _inst_2 i) [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : T2Space.{u3} γ _inst_4] {f : α -> γ} {a : α} (c : γ), (Filter.Tendsto.{u2, u3} α γ f (nhds.{u2} α _inst_1 a) (nhds.{u3} γ _inst_4 c)) -> (Eq.{succ u3} γ (DenseInducing.extend.{u2, u1, u3} α β γ _inst_1 _inst_2 i _inst_4 di f (i a)) (f a))
Case conversion may be inaccurate. Consider using '#align dense_inducing.extend_eq_at' DenseInducing.extend_eq_at'ₓ'. -/
theorem extend_eq_at' [T2Space γ] {f : α → γ} {a : α} (c : γ) (hf : Tendsto f (𝓝 a) (𝓝 c)) :
    di.extend f (i a) = f a :=
  di.extend_eq_at (continuousAt_of_tendsto_nhds hf)
#align dense_inducing.extend_eq_at' DenseInducing.extend_eq_at'

/- warning: dense_inducing.extend_eq -> DenseInducing.extend_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {i : α -> β} (di : DenseInducing.{u1, u2} α β _inst_1 _inst_2 i) [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : T2Space.{u3} γ _inst_4] {f : α -> γ}, (Continuous.{u1, u3} α γ _inst_1 _inst_4 f) -> (forall (a : α), Eq.{succ u3} γ (DenseInducing.extend.{u1, u2, u3} α β γ _inst_1 _inst_2 i _inst_4 di f (i a)) (f a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {i : α -> β} (di : DenseInducing.{u2, u1} α β _inst_1 _inst_2 i) [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : T2Space.{u3} γ _inst_4] {f : α -> γ}, (Continuous.{u2, u3} α γ _inst_1 _inst_4 f) -> (forall (a : α), Eq.{succ u3} γ (DenseInducing.extend.{u2, u1, u3} α β γ _inst_1 _inst_2 i _inst_4 di f (i a)) (f a))
Case conversion may be inaccurate. Consider using '#align dense_inducing.extend_eq DenseInducing.extend_eqₓ'. -/
theorem extend_eq [T2Space γ] {f : α → γ} (hf : Continuous f) (a : α) : di.extend f (i a) = f a :=
  di.extend_eq_at hf.ContinuousAt
#align dense_inducing.extend_eq DenseInducing.extend_eq

/- warning: dense_inducing.extend_eq' -> DenseInducing.extend_eq' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {i : α -> β} [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : T2Space.{u3} γ _inst_4] {f : α -> γ} (di : DenseInducing.{u1, u2} α β _inst_1 _inst_2 i), (forall (b : β), Exists.{succ u3} γ (fun (c : γ) => Filter.Tendsto.{u1, u3} α γ f (Filter.comap.{u1, u2} α β i (nhds.{u2} β _inst_2 b)) (nhds.{u3} γ _inst_4 c))) -> (forall (a : α), Eq.{succ u3} γ (DenseInducing.extend.{u1, u2, u3} α β γ _inst_1 _inst_2 i _inst_4 di f (i a)) (f a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {i : α -> β} [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : T2Space.{u3} γ _inst_4] {f : α -> γ} (di : DenseInducing.{u2, u1} α β _inst_1 _inst_2 i), (forall (b : β), Exists.{succ u3} γ (fun (c : γ) => Filter.Tendsto.{u2, u3} α γ f (Filter.comap.{u2, u1} α β i (nhds.{u1} β _inst_2 b)) (nhds.{u3} γ _inst_4 c))) -> (forall (a : α), Eq.{succ u3} γ (DenseInducing.extend.{u2, u1, u3} α β γ _inst_1 _inst_2 i _inst_4 di f (i a)) (f a))
Case conversion may be inaccurate. Consider using '#align dense_inducing.extend_eq' DenseInducing.extend_eq'ₓ'. -/
/-- Variation of `extend_eq` where we ask that `f` has a limit along `comap i (𝓝 b)` for each
`b : β`. This is a strictly stronger assumption than continuity of `f`, but in a lot of cases
you'd have to prove it anyway to use `continuous_extend`, so this avoids doing the work twice. -/
theorem extend_eq' [T2Space γ] {f : α → γ} (di : DenseInducing i)
    (hf : ∀ b, ∃ c, Tendsto f (comap i (𝓝 b)) (𝓝 c)) (a : α) : di.extend f (i a) = f a :=
  by
  rcases hf (i a) with ⟨b, hb⟩
  refine' di.extend_eq_at' b _
  rwa [← di.to_inducing.nhds_eq_comap] at hb
#align dense_inducing.extend_eq' DenseInducing.extend_eq'

/- warning: dense_inducing.extend_unique_at -> DenseInducing.extend_unique_at is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {i : α -> β} [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : T2Space.{u3} γ _inst_4] {b : β} {f : α -> γ} {g : β -> γ} (di : DenseInducing.{u1, u2} α β _inst_1 _inst_2 i), (Filter.Eventually.{u1} α (fun (x : α) => Eq.{succ u3} γ (g (i x)) (f x)) (Filter.comap.{u1, u2} α β i (nhds.{u2} β _inst_2 b))) -> (ContinuousAt.{u2, u3} β γ _inst_2 _inst_4 g b) -> (Eq.{succ u3} γ (DenseInducing.extend.{u1, u2, u3} α β γ _inst_1 _inst_2 i _inst_4 di f b) (g b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {i : α -> β} [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : T2Space.{u3} γ _inst_4] {b : β} {f : α -> γ} {g : β -> γ} (di : DenseInducing.{u2, u1} α β _inst_1 _inst_2 i), (Filter.Eventually.{u2} α (fun (x : α) => Eq.{succ u3} γ (g (i x)) (f x)) (Filter.comap.{u2, u1} α β i (nhds.{u1} β _inst_2 b))) -> (ContinuousAt.{u1, u3} β γ _inst_2 _inst_4 g b) -> (Eq.{succ u3} γ (DenseInducing.extend.{u2, u1, u3} α β γ _inst_1 _inst_2 i _inst_4 di f b) (g b))
Case conversion may be inaccurate. Consider using '#align dense_inducing.extend_unique_at DenseInducing.extend_unique_atₓ'. -/
theorem extend_unique_at [T2Space γ] {b : β} {f : α → γ} {g : β → γ} (di : DenseInducing i)
    (hf : ∀ᶠ x in comap i (𝓝 b), g (i x) = f x) (hg : ContinuousAt g b) : di.extend f b = g b :=
  by
  refine' di.extend_eq_of_tendsto fun s hs => mem_map.2 _
  suffices : ∀ᶠ x : α in comap i (𝓝 b), g (i x) ∈ s
  exact hf.mp (this.mono fun x hgx hfx => hfx ▸ hgx)
  clear hf f
  refine' eventually_comap.2 ((hg.eventually hs).mono _)
  rintro _ hxs x rfl
  exact hxs
#align dense_inducing.extend_unique_at DenseInducing.extend_unique_at

/- warning: dense_inducing.extend_unique -> DenseInducing.extend_unique is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {i : α -> β} [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : T2Space.{u3} γ _inst_4] {f : α -> γ} {g : β -> γ} (di : DenseInducing.{u1, u2} α β _inst_1 _inst_2 i), (forall (x : α), Eq.{succ u3} γ (g (i x)) (f x)) -> (Continuous.{u2, u3} β γ _inst_2 _inst_4 g) -> (Eq.{max (succ u2) (succ u3)} (β -> γ) (DenseInducing.extend.{u1, u2, u3} α β γ _inst_1 _inst_2 i _inst_4 di f) g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {i : α -> β} [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : T2Space.{u3} γ _inst_4] {f : α -> γ} {g : β -> γ} (di : DenseInducing.{u2, u1} α β _inst_1 _inst_2 i), (forall (x : α), Eq.{succ u3} γ (g (i x)) (f x)) -> (Continuous.{u1, u3} β γ _inst_2 _inst_4 g) -> (Eq.{max (succ u1) (succ u3)} (β -> γ) (DenseInducing.extend.{u2, u1, u3} α β γ _inst_1 _inst_2 i _inst_4 di f) g)
Case conversion may be inaccurate. Consider using '#align dense_inducing.extend_unique DenseInducing.extend_uniqueₓ'. -/
theorem extend_unique [T2Space γ] {f : α → γ} {g : β → γ} (di : DenseInducing i)
    (hf : ∀ x, g (i x) = f x) (hg : Continuous g) : di.extend f = g :=
  funext fun b => extend_unique_at di (eventually_of_forall hf) hg.ContinuousAt
#align dense_inducing.extend_unique DenseInducing.extend_unique

/- warning: dense_inducing.continuous_at_extend -> DenseInducing.continuousAt_extend is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {i : α -> β} [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : T3Space.{u3} γ _inst_4] {b : β} {f : α -> γ} (di : DenseInducing.{u1, u2} α β _inst_1 _inst_2 i), (Filter.Eventually.{u2} β (fun (x : β) => Exists.{succ u3} γ (fun (c : γ) => Filter.Tendsto.{u1, u3} α γ f (Filter.comap.{u1, u2} α β i (nhds.{u2} β _inst_2 x)) (nhds.{u3} γ _inst_4 c))) (nhds.{u2} β _inst_2 b)) -> (ContinuousAt.{u2, u3} β γ _inst_2 _inst_4 (DenseInducing.extend.{u1, u2, u3} α β γ _inst_1 _inst_2 i _inst_4 di f) b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {i : α -> β} [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : T3Space.{u3} γ _inst_4] {b : β} {f : α -> γ} (di : DenseInducing.{u2, u1} α β _inst_1 _inst_2 i), (Filter.Eventually.{u1} β (fun (x : β) => Exists.{succ u3} γ (fun (c : γ) => Filter.Tendsto.{u2, u3} α γ f (Filter.comap.{u2, u1} α β i (nhds.{u1} β _inst_2 x)) (nhds.{u3} γ _inst_4 c))) (nhds.{u1} β _inst_2 b)) -> (ContinuousAt.{u1, u3} β γ _inst_2 _inst_4 (DenseInducing.extend.{u2, u1, u3} α β γ _inst_1 _inst_2 i _inst_4 di f) b)
Case conversion may be inaccurate. Consider using '#align dense_inducing.continuous_at_extend DenseInducing.continuousAt_extendₓ'. -/
theorem continuousAt_extend [T3Space γ] {b : β} {f : α → γ} (di : DenseInducing i)
    (hf : ∀ᶠ x in 𝓝 b, ∃ c, Tendsto f (comap i <| 𝓝 x) (𝓝 c)) : ContinuousAt (di.extend f) b :=
  by
  set φ := di.extend f
  haveI := di.comap_nhds_ne_bot
  suffices ∀ V' ∈ 𝓝 (φ b), IsClosed V' → φ ⁻¹' V' ∈ 𝓝 b by
    simpa [ContinuousAt, (closed_nhds_basis _).tendsto_right_iff]
  intro V' V'_in V'_closed
  set V₁ := { x | tendsto f (comap i <| 𝓝 x) (𝓝 <| φ x) }
  have V₁_in : V₁ ∈ 𝓝 b := by
    filter_upwards [hf]
    rintro x ⟨c, hc⟩
    dsimp [V₁, φ]
    rwa [di.extend_eq_of_tendsto hc]
  obtain ⟨V₂, V₂_in, V₂_op, hV₂⟩ : ∃ V₂ ∈ 𝓝 b, IsOpen V₂ ∧ ∀ x ∈ i ⁻¹' V₂, f x ∈ V' := by
    simpa [and_assoc'] using
      ((nhds_basis_opens' b).comap i).tendsto_left_iffₓ.mp (mem_of_mem_nhds V₁_in : b ∈ V₁) V' V'_in
  suffices ∀ x ∈ V₁ ∩ V₂, φ x ∈ V' by filter_upwards [inter_mem V₁_in V₂_in]using this
  rintro x ⟨x_in₁, x_in₂⟩
  have hV₂x : V₂ ∈ 𝓝 x := IsOpen.mem_nhds V₂_op x_in₂
  apply V'_closed.mem_of_tendsto x_in₁
  use V₂
  tauto
#align dense_inducing.continuous_at_extend DenseInducing.continuousAt_extend

/- warning: dense_inducing.continuous_extend -> DenseInducing.continuous_extend is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {i : α -> β} [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : T3Space.{u3} γ _inst_4] {f : α -> γ} (di : DenseInducing.{u1, u2} α β _inst_1 _inst_2 i), (forall (b : β), Exists.{succ u3} γ (fun (c : γ) => Filter.Tendsto.{u1, u3} α γ f (Filter.comap.{u1, u2} α β i (nhds.{u2} β _inst_2 b)) (nhds.{u3} γ _inst_4 c))) -> (Continuous.{u2, u3} β γ _inst_2 _inst_4 (DenseInducing.extend.{u1, u2, u3} α β γ _inst_1 _inst_2 i _inst_4 di f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {i : α -> β} [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : T3Space.{u3} γ _inst_4] {f : α -> γ} (di : DenseInducing.{u2, u1} α β _inst_1 _inst_2 i), (forall (b : β), Exists.{succ u3} γ (fun (c : γ) => Filter.Tendsto.{u2, u3} α γ f (Filter.comap.{u2, u1} α β i (nhds.{u1} β _inst_2 b)) (nhds.{u3} γ _inst_4 c))) -> (Continuous.{u1, u3} β γ _inst_2 _inst_4 (DenseInducing.extend.{u2, u1, u3} α β γ _inst_1 _inst_2 i _inst_4 di f))
Case conversion may be inaccurate. Consider using '#align dense_inducing.continuous_extend DenseInducing.continuous_extendₓ'. -/
theorem continuous_extend [T3Space γ] {f : α → γ} (di : DenseInducing i)
    (hf : ∀ b, ∃ c, Tendsto f (comap i (𝓝 b)) (𝓝 c)) : Continuous (di.extend f) :=
  continuous_iff_continuousAt.mpr fun b => di.continuousAt_extend <| univ_mem' hf
#align dense_inducing.continuous_extend DenseInducing.continuous_extend

/- warning: dense_inducing.mk' -> DenseInducing.mk' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (i : α -> β), (Continuous.{u1, u2} α β _inst_1 _inst_2 i) -> (forall (x : β), Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (closure.{u2} β _inst_2 (Set.range.{u2, succ u1} β α i))) -> (forall (a : α) (s : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhds.{u1} α _inst_1 a)) -> (Exists.{succ u2} (Set.{u2} β) (fun (t : Set.{u2} β) => Exists.{0} (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) t (nhds.{u2} β _inst_2 (i a))) (fun (H : Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) t (nhds.{u2} β _inst_2 (i a))) => forall (b : α), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (i b) t) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s))))) -> (DenseInducing.{u1, u2} α β _inst_1 _inst_2 i)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (i : α -> β), (Continuous.{u2, u1} α β _inst_1 _inst_2 i) -> (forall (x : β), Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (closure.{u1} β _inst_2 (Set.range.{u1, succ u2} β α i))) -> (forall (a : α) (s : Set.{u2} α), (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s (nhds.{u2} α _inst_1 a)) -> (Exists.{succ u1} (Set.{u1} β) (fun (t : Set.{u1} β) => And (Membership.mem.{u1, u1} (Set.{u1} β) (Filter.{u1} β) (instMembershipSetFilter.{u1} β) t (nhds.{u1} β _inst_2 (i a))) (forall (b : α), (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (i b) t) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) b s))))) -> (DenseInducing.{u2, u1} α β _inst_1 _inst_2 i)
Case conversion may be inaccurate. Consider using '#align dense_inducing.mk' DenseInducing.mk'ₓ'. -/
theorem mk' (i : α → β) (c : Continuous i) (dense : ∀ x, x ∈ closure (range i))
    (H : ∀ (a : α), ∀ s ∈ 𝓝 a, ∃ t ∈ 𝓝 (i a), ∀ b, i b ∈ t → b ∈ s) : DenseInducing i :=
  { induced :=
      (induced_iff_nhds_eq i).2 fun a =>
        le_antisymm (tendsto_iff_comap.1 <| c.Tendsto _) (by simpa [Filter.le_def] using H a)
    dense }
#align dense_inducing.mk' DenseInducing.mk'

end DenseInducing

#print DenseEmbedding /-
/-- A dense embedding is an embedding with dense image. -/
structure DenseEmbedding [TopologicalSpace α] [TopologicalSpace β] (e : α → β) extends
  DenseInducing e : Prop where
  inj : Function.Injective e
#align dense_embedding DenseEmbedding
-/

/- warning: dense_embedding.mk' -> DenseEmbedding.mk' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : α -> β), (Continuous.{u1, u2} α β _inst_1 _inst_2 e) -> (DenseRange.{u2, u1} β _inst_2 α e) -> (Function.Injective.{succ u1, succ u2} α β e) -> (forall (a : α) (s : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhds.{u1} α _inst_1 a)) -> (Exists.{succ u2} (Set.{u2} β) (fun (t : Set.{u2} β) => Exists.{0} (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) t (nhds.{u2} β _inst_2 (e a))) (fun (H : Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) t (nhds.{u2} β _inst_2 (e a))) => forall (b : α), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (e b) t) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s))))) -> (DenseEmbedding.{u1, u2} α β _inst_1 _inst_2 e)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (e : α -> β), (Continuous.{u2, u1} α β _inst_1 _inst_2 e) -> (DenseRange.{u1, u2} β _inst_2 α e) -> (Function.Injective.{succ u2, succ u1} α β e) -> (forall (a : α) (s : Set.{u2} α), (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s (nhds.{u2} α _inst_1 a)) -> (Exists.{succ u1} (Set.{u1} β) (fun (t : Set.{u1} β) => And (Membership.mem.{u1, u1} (Set.{u1} β) (Filter.{u1} β) (instMembershipSetFilter.{u1} β) t (nhds.{u1} β _inst_2 (e a))) (forall (b : α), (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (e b) t) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) b s))))) -> (DenseEmbedding.{u2, u1} α β _inst_1 _inst_2 e)
Case conversion may be inaccurate. Consider using '#align dense_embedding.mk' DenseEmbedding.mk'ₓ'. -/
theorem DenseEmbedding.mk' [TopologicalSpace α] [TopologicalSpace β] (e : α → β) (c : Continuous e)
    (dense : DenseRange e) (inj : Function.Injective e)
    (H : ∀ (a : α), ∀ s ∈ 𝓝 a, ∃ t ∈ 𝓝 (e a), ∀ b, e b ∈ t → b ∈ s) : DenseEmbedding e :=
  { DenseInducing.mk' e c Dense H with inj }
#align dense_embedding.mk' DenseEmbedding.mk'

namespace DenseEmbedding

open TopologicalSpace

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

variable {e : α → β} (de : DenseEmbedding e)

#print DenseEmbedding.inj_iff /-
theorem inj_iff {x y} : e x = e y ↔ x = y :=
  de.inj.eq_iff
#align dense_embedding.inj_iff DenseEmbedding.inj_iff
-/

/- warning: dense_embedding.to_embedding -> DenseEmbedding.to_embedding is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : α -> β}, (DenseEmbedding.{u1, u2} α β _inst_1 _inst_2 e) -> (Embedding.{u1, u2} α β _inst_1 _inst_2 e)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : α -> β}, (DenseEmbedding.{u2, u1} α β _inst_1 _inst_2 e) -> (Embedding.{u2, u1} α β _inst_1 _inst_2 e)
Case conversion may be inaccurate. Consider using '#align dense_embedding.to_embedding DenseEmbedding.to_embeddingₓ'. -/
theorem to_embedding : Embedding e :=
  { induced := de.induced
    inj := de.inj }
#align dense_embedding.to_embedding DenseEmbedding.to_embedding

/- warning: dense_embedding.separable_space -> DenseEmbedding.separableSpace is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : α -> β}, (DenseEmbedding.{u1, u2} α β _inst_1 _inst_2 e) -> (forall [_inst_5 : TopologicalSpace.SeparableSpace.{u1} α _inst_1], TopologicalSpace.SeparableSpace.{u2} β _inst_2)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : α -> β}, (DenseEmbedding.{u2, u1} α β _inst_1 _inst_2 e) -> (forall [_inst_5 : TopologicalSpace.SeparableSpace.{u2} α _inst_1], TopologicalSpace.SeparableSpace.{u1} β _inst_2)
Case conversion may be inaccurate. Consider using '#align dense_embedding.separable_space DenseEmbedding.separableSpaceₓ'. -/
/-- If the domain of a `dense_embedding` is a separable space, then so is its codomain. -/
protected theorem separableSpace [SeparableSpace α] : SeparableSpace β :=
  de.to_denseInducing.SeparableSpace
#align dense_embedding.separable_space DenseEmbedding.separableSpace

/- warning: dense_embedding.prod -> DenseEmbedding.prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] {e₁ : α -> β} {e₂ : γ -> δ}, (DenseEmbedding.{u1, u2} α β _inst_1 _inst_2 e₁) -> (DenseEmbedding.{u3, u4} γ δ _inst_3 _inst_4 e₂) -> (DenseEmbedding.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (Prod.topologicalSpace.{u1, u3} α γ _inst_1 _inst_3) (Prod.topologicalSpace.{u2, u4} β δ _inst_2 _inst_4) (fun (p : Prod.{u1, u3} α γ) => Prod.mk.{u2, u4} β δ (e₁ (Prod.fst.{u1, u3} α γ p)) (e₂ (Prod.snd.{u1, u3} α γ p))))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u2}} {δ : Type.{u1}} [_inst_1 : TopologicalSpace.{u4} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] [_inst_4 : TopologicalSpace.{u1} δ] {e₁ : α -> β} {e₂ : γ -> δ}, (DenseEmbedding.{u4, u3} α β _inst_1 _inst_2 e₁) -> (DenseEmbedding.{u2, u1} γ δ _inst_3 _inst_4 e₂) -> (DenseEmbedding.{max u4 u2, max u1 u3} (Prod.{u4, u2} α γ) (Prod.{u3, u1} β δ) (instTopologicalSpaceProd.{u4, u2} α γ _inst_1 _inst_3) (instTopologicalSpaceProd.{u3, u1} β δ _inst_2 _inst_4) (fun (p : Prod.{u4, u2} α γ) => Prod.mk.{u3, u1} β δ (e₁ (Prod.fst.{u4, u2} α γ p)) (e₂ (Prod.snd.{u4, u2} α γ p))))
Case conversion may be inaccurate. Consider using '#align dense_embedding.prod DenseEmbedding.prodₓ'. -/
/-- The product of two dense embeddings is a dense embedding. -/
protected theorem prod {e₁ : α → β} {e₂ : γ → δ} (de₁ : DenseEmbedding e₁)
    (de₂ : DenseEmbedding e₂) : DenseEmbedding fun p : α × γ => (e₁ p.1, e₂ p.2) :=
  { DenseInducing.prod de₁.to_denseInducing de₂.to_denseInducing with
    inj := fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ => by simp <;> exact fun h₁ h₂ => ⟨de₁.inj h₁, de₂.inj h₂⟩ }
#align dense_embedding.prod DenseEmbedding.prod

#print DenseEmbedding.subtypeEmb /-
/-- The dense embedding of a subtype inside its closure. -/
@[simps]
def subtypeEmb {α : Type _} (p : α → Prop) (e : α → β) (x : { x // p x }) :
    { x // x ∈ closure (e '' { x | p x }) } :=
  ⟨e x, subset_closure <| mem_image_of_mem e x.Prop⟩
#align dense_embedding.subtype_emb DenseEmbedding.subtypeEmb
-/

/- warning: dense_embedding.subtype -> DenseEmbedding.subtype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : α -> β}, (DenseEmbedding.{u1, u2} α β _inst_1 _inst_2 e) -> (forall (p : α -> Prop), DenseEmbedding.{u1, u2} (Subtype.{succ u1} α (fun (x : α) => p x)) (Subtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (closure.{u2} β _inst_2 (Set.image.{u1, u2} α β e (setOf.{u1} α (fun (x : α) => p x)))))) (Subtype.topologicalSpace.{u1} α (fun (x : α) => p x) _inst_1) (Subtype.topologicalSpace.{u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (closure.{u2} β _inst_2 (Set.image.{u1, u2} α β e (setOf.{u1} α (fun (x : α) => p x))))) _inst_2) (DenseEmbedding.subtypeEmb.{u2, u1} β _inst_2 α p e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : α -> β}, (DenseEmbedding.{u2, u1} α β _inst_1 _inst_2 e) -> (forall (p : α -> Prop), DenseEmbedding.{u2, u1} (Subtype.{succ u2} α (fun (x : α) => p x)) (Subtype.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (closure.{u1} β _inst_2 (Set.image.{u2, u1} α β e (setOf.{u2} α (fun (x : α) => p x)))))) (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => p x) _inst_1) (instTopologicalSpaceSubtype.{u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (closure.{u1} β _inst_2 (Set.image.{u2, u1} α β e (setOf.{u2} α (fun (x : α) => p x))))) _inst_2) (DenseEmbedding.subtypeEmb.{u1, u2} β _inst_2 α p e))
Case conversion may be inaccurate. Consider using '#align dense_embedding.subtype DenseEmbedding.subtypeₓ'. -/
protected theorem subtype (p : α → Prop) : DenseEmbedding (subtypeEmb p e) :=
  { dense :=
      dense_iff_closure_eq.2 <| by
        ext ⟨x, hx⟩
        rw [image_eq_range] at hx
        simpa [closure_subtype, ← range_comp, (· ∘ ·)]
    inj := (de.inj.comp Subtype.coe_injective).codRestrict _
    induced :=
      (induced_iff_nhds_eq _).2 fun ⟨x, hx⟩ => by
        simp [subtype_emb, nhds_subtype_eq_comap, de.to_inducing.nhds_eq_comap, comap_comap,
          (· ∘ ·)] }
#align dense_embedding.subtype DenseEmbedding.subtype

/- warning: dense_embedding.dense_image -> DenseEmbedding.dense_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {e : α -> β}, (DenseEmbedding.{u1, u2} α β _inst_1 _inst_2 e) -> (forall {s : Set.{u1} α}, Iff (Dense.{u2} β _inst_2 (Set.image.{u1, u2} α β e s)) (Dense.{u1} α _inst_1 s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {e : α -> β}, (DenseEmbedding.{u2, u1} α β _inst_1 _inst_2 e) -> (forall {s : Set.{u2} α}, Iff (Dense.{u1} β _inst_2 (Set.image.{u2, u1} α β e s)) (Dense.{u2} α _inst_1 s))
Case conversion may be inaccurate. Consider using '#align dense_embedding.dense_image DenseEmbedding.dense_imageₓ'. -/
theorem dense_image {s : Set α} : Dense (e '' s) ↔ Dense s :=
  de.to_denseInducing.dense_image
#align dense_embedding.dense_image DenseEmbedding.dense_image

end DenseEmbedding

#print denseEmbedding_id /-
theorem denseEmbedding_id {α : Type _} [TopologicalSpace α] : DenseEmbedding (id : α → α) :=
  { embedding_id with dense := denseRange_id }
#align dense_embedding_id denseEmbedding_id
-/

#print Dense.denseEmbedding_val /-
theorem Dense.denseEmbedding_val [TopologicalSpace α] {s : Set α} (hs : Dense s) :
    DenseEmbedding (coe : s → α) :=
  { embedding_subtype_val with dense := hs.denseRange_val }
#align dense.dense_embedding_coe Dense.denseEmbedding_val
-/

#print isClosed_property /-
theorem isClosed_property [TopologicalSpace β] {e : α → β} {p : β → Prop} (he : DenseRange e)
    (hp : IsClosed { x | p x }) (h : ∀ a, p (e a)) : ∀ b, p b :=
  have : univ ⊆ { b | p b } :=
    calc
      univ = closure (range e) := he.closure_range.symm
      _ ⊆ closure { b | p b } := closure_mono <| range_subset_iff.mpr h
      _ = _ := hp.closure_eq
      
  fun b => this trivial
#align is_closed_property isClosed_property
-/

/- warning: is_closed_property2 -> isClosed_property2 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} β] {e : α -> β} {p : β -> β -> Prop}, (DenseRange.{u2, u1} β _inst_1 α e) -> (IsClosed.{u2} (Prod.{u2, u2} β β) (Prod.topologicalSpace.{u2, u2} β β _inst_1 _inst_1) (setOf.{u2} (Prod.{u2, u2} β β) (fun (q : Prod.{u2, u2} β β) => p (Prod.fst.{u2, u2} β β q) (Prod.snd.{u2, u2} β β q)))) -> (forall (a₁ : α) (a₂ : α), p (e a₁) (e a₂)) -> (forall (b₁ : β) (b₂ : β), p b₁ b₂)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} β] {e : α -> β} {p : β -> β -> Prop}, (DenseRange.{u2, u1} β _inst_1 α e) -> (IsClosed.{u2} (Prod.{u2, u2} β β) (instTopologicalSpaceProd.{u2, u2} β β _inst_1 _inst_1) (setOf.{u2} (Prod.{u2, u2} β β) (fun (q : Prod.{u2, u2} β β) => p (Prod.fst.{u2, u2} β β q) (Prod.snd.{u2, u2} β β q)))) -> (forall (a₁ : α) (a₂ : α), p (e a₁) (e a₂)) -> (forall (b₁ : β) (b₂ : β), p b₁ b₂)
Case conversion may be inaccurate. Consider using '#align is_closed_property2 isClosed_property2ₓ'. -/
theorem isClosed_property2 [TopologicalSpace β] {e : α → β} {p : β → β → Prop} (he : DenseRange e)
    (hp : IsClosed { q : β × β | p q.1 q.2 }) (h : ∀ a₁ a₂, p (e a₁) (e a₂)) : ∀ b₁ b₂, p b₁ b₂ :=
  have : ∀ q : β × β, p q.1 q.2 := isClosed_property (he.Prod_map he) hp fun _ => h _ _
  fun b₁ b₂ => this ⟨b₁, b₂⟩
#align is_closed_property2 isClosed_property2

/- warning: is_closed_property3 -> isClosed_property3 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} β] {e : α -> β} {p : β -> β -> β -> Prop}, (DenseRange.{u2, u1} β _inst_1 α e) -> (IsClosed.{u2} (Prod.{u2, u2} β (Prod.{u2, u2} β β)) (Prod.topologicalSpace.{u2, u2} β (Prod.{u2, u2} β β) _inst_1 (Prod.topologicalSpace.{u2, u2} β β _inst_1 _inst_1)) (setOf.{u2} (Prod.{u2, u2} β (Prod.{u2, u2} β β)) (fun (q : Prod.{u2, u2} β (Prod.{u2, u2} β β)) => p (Prod.fst.{u2, u2} β (Prod.{u2, u2} β β) q) (Prod.fst.{u2, u2} β β (Prod.snd.{u2, u2} β (Prod.{u2, u2} β β) q)) (Prod.snd.{u2, u2} β β (Prod.snd.{u2, u2} β (Prod.{u2, u2} β β) q))))) -> (forall (a₁ : α) (a₂ : α) (a₃ : α), p (e a₁) (e a₂) (e a₃)) -> (forall (b₁ : β) (b₂ : β) (b₃ : β), p b₁ b₂ b₃)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} β] {e : α -> β} {p : β -> β -> β -> Prop}, (DenseRange.{u2, u1} β _inst_1 α e) -> (IsClosed.{u2} (Prod.{u2, u2} β (Prod.{u2, u2} β β)) (instTopologicalSpaceProd.{u2, u2} β (Prod.{u2, u2} β β) _inst_1 (instTopologicalSpaceProd.{u2, u2} β β _inst_1 _inst_1)) (setOf.{u2} (Prod.{u2, u2} β (Prod.{u2, u2} β β)) (fun (q : Prod.{u2, u2} β (Prod.{u2, u2} β β)) => p (Prod.fst.{u2, u2} β (Prod.{u2, u2} β β) q) (Prod.fst.{u2, u2} β β (Prod.snd.{u2, u2} β (Prod.{u2, u2} β β) q)) (Prod.snd.{u2, u2} β β (Prod.snd.{u2, u2} β (Prod.{u2, u2} β β) q))))) -> (forall (a₁ : α) (a₂ : α) (a₃ : α), p (e a₁) (e a₂) (e a₃)) -> (forall (b₁ : β) (b₂ : β) (b₃ : β), p b₁ b₂ b₃)
Case conversion may be inaccurate. Consider using '#align is_closed_property3 isClosed_property3ₓ'. -/
theorem isClosed_property3 [TopologicalSpace β] {e : α → β} {p : β → β → β → Prop}
    (he : DenseRange e) (hp : IsClosed { q : β × β × β | p q.1 q.2.1 q.2.2 })
    (h : ∀ a₁ a₂ a₃, p (e a₁) (e a₂) (e a₃)) : ∀ b₁ b₂ b₃, p b₁ b₂ b₃ :=
  have : ∀ q : β × β × β, p q.1 q.2.1 q.2.2 :=
    isClosed_property (he.Prod_map <| he.Prod_map he) hp fun _ => h _ _ _
  fun b₁ b₂ b₃ => this ⟨b₁, b₂, b₃⟩
#align is_closed_property3 isClosed_property3

#print DenseRange.induction_on /-
@[elab_as_elim]
theorem DenseRange.induction_on [TopologicalSpace β] {e : α → β} (he : DenseRange e) {p : β → Prop}
    (b₀ : β) (hp : IsClosed { b | p b }) (ih : ∀ a : α, p <| e a) : p b₀ :=
  isClosed_property he hp ih b₀
#align dense_range.induction_on DenseRange.induction_on
-/

/- warning: dense_range.induction_on₂ -> DenseRange.induction_on₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} β] {e : α -> β} {p : β -> β -> Prop}, (DenseRange.{u2, u1} β _inst_1 α e) -> (IsClosed.{u2} (Prod.{u2, u2} β β) (Prod.topologicalSpace.{u2, u2} β β _inst_1 _inst_1) (setOf.{u2} (Prod.{u2, u2} β β) (fun (q : Prod.{u2, u2} β β) => p (Prod.fst.{u2, u2} β β q) (Prod.snd.{u2, u2} β β q)))) -> (forall (a₁ : α) (a₂ : α), p (e a₁) (e a₂)) -> (forall (b₁ : β) (b₂ : β), p b₁ b₂)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} β] {e : α -> β} {p : β -> β -> Prop}, (DenseRange.{u2, u1} β _inst_1 α e) -> (IsClosed.{u2} (Prod.{u2, u2} β β) (instTopologicalSpaceProd.{u2, u2} β β _inst_1 _inst_1) (setOf.{u2} (Prod.{u2, u2} β β) (fun (q : Prod.{u2, u2} β β) => p (Prod.fst.{u2, u2} β β q) (Prod.snd.{u2, u2} β β q)))) -> (forall (a₁ : α) (a₂ : α), p (e a₁) (e a₂)) -> (forall (b₁ : β) (b₂ : β), p b₁ b₂)
Case conversion may be inaccurate. Consider using '#align dense_range.induction_on₂ DenseRange.induction_on₂ₓ'. -/
@[elab_as_elim]
theorem DenseRange.induction_on₂ [TopologicalSpace β] {e : α → β} {p : β → β → Prop}
    (he : DenseRange e) (hp : IsClosed { q : β × β | p q.1 q.2 }) (h : ∀ a₁ a₂, p (e a₁) (e a₂))
    (b₁ b₂ : β) : p b₁ b₂ :=
  isClosed_property2 he hp h _ _
#align dense_range.induction_on₂ DenseRange.induction_on₂

/- warning: dense_range.induction_on₃ -> DenseRange.induction_on₃ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} β] {e : α -> β} {p : β -> β -> β -> Prop}, (DenseRange.{u2, u1} β _inst_1 α e) -> (IsClosed.{u2} (Prod.{u2, u2} β (Prod.{u2, u2} β β)) (Prod.topologicalSpace.{u2, u2} β (Prod.{u2, u2} β β) _inst_1 (Prod.topologicalSpace.{u2, u2} β β _inst_1 _inst_1)) (setOf.{u2} (Prod.{u2, u2} β (Prod.{u2, u2} β β)) (fun (q : Prod.{u2, u2} β (Prod.{u2, u2} β β)) => p (Prod.fst.{u2, u2} β (Prod.{u2, u2} β β) q) (Prod.fst.{u2, u2} β β (Prod.snd.{u2, u2} β (Prod.{u2, u2} β β) q)) (Prod.snd.{u2, u2} β β (Prod.snd.{u2, u2} β (Prod.{u2, u2} β β) q))))) -> (forall (a₁ : α) (a₂ : α) (a₃ : α), p (e a₁) (e a₂) (e a₃)) -> (forall (b₁ : β) (b₂ : β) (b₃ : β), p b₁ b₂ b₃)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} β] {e : α -> β} {p : β -> β -> β -> Prop}, (DenseRange.{u2, u1} β _inst_1 α e) -> (IsClosed.{u2} (Prod.{u2, u2} β (Prod.{u2, u2} β β)) (instTopologicalSpaceProd.{u2, u2} β (Prod.{u2, u2} β β) _inst_1 (instTopologicalSpaceProd.{u2, u2} β β _inst_1 _inst_1)) (setOf.{u2} (Prod.{u2, u2} β (Prod.{u2, u2} β β)) (fun (q : Prod.{u2, u2} β (Prod.{u2, u2} β β)) => p (Prod.fst.{u2, u2} β (Prod.{u2, u2} β β) q) (Prod.fst.{u2, u2} β β (Prod.snd.{u2, u2} β (Prod.{u2, u2} β β) q)) (Prod.snd.{u2, u2} β β (Prod.snd.{u2, u2} β (Prod.{u2, u2} β β) q))))) -> (forall (a₁ : α) (a₂ : α) (a₃ : α), p (e a₁) (e a₂) (e a₃)) -> (forall (b₁ : β) (b₂ : β) (b₃ : β), p b₁ b₂ b₃)
Case conversion may be inaccurate. Consider using '#align dense_range.induction_on₃ DenseRange.induction_on₃ₓ'. -/
@[elab_as_elim]
theorem DenseRange.induction_on₃ [TopologicalSpace β] {e : α → β} {p : β → β → β → Prop}
    (he : DenseRange e) (hp : IsClosed { q : β × β × β | p q.1 q.2.1 q.2.2 })
    (h : ∀ a₁ a₂ a₃, p (e a₁) (e a₂) (e a₃)) (b₁ b₂ b₃ : β) : p b₁ b₂ b₃ :=
  isClosed_property3 he hp h _ _ _
#align dense_range.induction_on₃ DenseRange.induction_on₃

section

variable [TopologicalSpace β] [TopologicalSpace γ] [T2Space γ]

variable {f : α → β}

/- warning: dense_range.equalizer -> DenseRange.equalizer is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} β] [_inst_2 : TopologicalSpace.{u3} γ] [_inst_3 : T2Space.{u3} γ _inst_2] {f : α -> β}, (DenseRange.{u2, u1} β _inst_1 α f) -> (forall {g : β -> γ} {h : β -> γ}, (Continuous.{u2, u3} β γ _inst_1 _inst_2 g) -> (Continuous.{u2, u3} β γ _inst_1 _inst_2 h) -> (Eq.{max (succ u1) (succ u3)} (α -> γ) (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) (Function.comp.{succ u1, succ u2, succ u3} α β γ h f)) -> (Eq.{max (succ u2) (succ u3)} (β -> γ) g h))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} β] [_inst_2 : TopologicalSpace.{u1} γ] [_inst_3 : T2Space.{u1} γ _inst_2] {f : α -> β}, (DenseRange.{u3, u2} β _inst_1 α f) -> (forall {g : β -> γ} {h : β -> γ}, (Continuous.{u3, u1} β γ _inst_1 _inst_2 g) -> (Continuous.{u3, u1} β γ _inst_1 _inst_2 h) -> (Eq.{max (succ u2) (succ u1)} (α -> γ) (Function.comp.{succ u2, succ u3, succ u1} α β γ g f) (Function.comp.{succ u2, succ u3, succ u1} α β γ h f)) -> (Eq.{max (succ u3) (succ u1)} (β -> γ) g h))
Case conversion may be inaccurate. Consider using '#align dense_range.equalizer DenseRange.equalizerₓ'. -/
/-- Two continuous functions to a t2-space that agree on the dense range of a function are equal. -/
theorem DenseRange.equalizer (hfd : DenseRange f) {g h : β → γ} (hg : Continuous g)
    (hh : Continuous h) (H : g ∘ f = h ∘ f) : g = h :=
  funext fun y => hfd.inductionOn y (isClosed_eq hg hh) <| congr_fun H
#align dense_range.equalizer DenseRange.equalizer

end

/- warning: filter.has_basis.has_basis_of_dense_inducing -> Filter.HasBasis.hasBasis_of_denseInducing is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : T3Space.{u2} β _inst_2] {ι : Type.{u3}} {s : ι -> (Set.{u1} α)} {p : ι -> Prop} {x : α}, (Filter.HasBasis.{u1, succ u3} α ι (nhds.{u1} α _inst_1 x) p s) -> (forall {f : α -> β}, (DenseInducing.{u1, u2} α β _inst_1 _inst_2 f) -> (Filter.HasBasis.{u2, succ u3} β ι (nhds.{u2} β _inst_2 (f x)) p (fun (i : ι) => closure.{u2} β _inst_2 (Set.image.{u1, u2} α β f (s i)))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : T3Space.{u2} β _inst_2] {ι : Type.{u1}} {s : ι -> (Set.{u3} α)} {p : ι -> Prop} {x : α}, (Filter.HasBasis.{u3, succ u1} α ι (nhds.{u3} α _inst_1 x) p s) -> (forall {f : α -> β}, (DenseInducing.{u3, u2} α β _inst_1 _inst_2 f) -> (Filter.HasBasis.{u2, succ u1} β ι (nhds.{u2} β _inst_2 (f x)) p (fun (i : ι) => closure.{u2} β _inst_2 (Set.image.{u3, u2} α β f (s i)))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.has_basis_of_dense_inducing Filter.HasBasis.hasBasis_of_denseInducingₓ'. -/
-- Bourbaki GT III §3 no.4 Proposition 7 (generalised to any dense-inducing map to a T₃ space)
theorem Filter.HasBasis.hasBasis_of_denseInducing [TopologicalSpace α] [TopologicalSpace β]
    [T3Space β] {ι : Type _} {s : ι → Set α} {p : ι → Prop} {x : α} (h : (𝓝 x).HasBasis p s)
    {f : α → β} (hf : DenseInducing f) : (𝓝 (f x)).HasBasis p fun i => closure <| f '' s i :=
  by
  rw [Filter.hasBasis_iff] at h⊢
  intro T
  refine' ⟨fun hT => _, fun hT => _⟩
  · obtain ⟨T', hT₁, hT₂, hT₃⟩ := exists_mem_nhds_isClosed_subset hT
    have hT₄ : f ⁻¹' T' ∈ 𝓝 x := by
      rw [hf.to_inducing.nhds_eq_comap x]
      exact ⟨T', hT₁, subset.rfl⟩
    obtain ⟨i, hi, hi'⟩ := (h _).mp hT₄
    exact
      ⟨i, hi,
        (closure_mono (image_subset f hi')).trans
          (subset.trans (closure_minimal (image_subset_iff.mpr subset.rfl) hT₂) hT₃)⟩
  · obtain ⟨i, hi, hi'⟩ := hT
    suffices closure (f '' s i) ∈ 𝓝 (f x) by filter_upwards [this]using hi'
    replace h := (h (s i)).mpr ⟨i, hi, subset.rfl⟩
    exact hf.closure_image_mem_nhds h
#align filter.has_basis.has_basis_of_dense_inducing Filter.HasBasis.hasBasis_of_denseInducing

