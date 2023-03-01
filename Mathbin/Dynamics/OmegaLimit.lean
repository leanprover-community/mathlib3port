/-
Copyright (c) 2020 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo

! This file was ported from Lean 3 source module dynamics.omega_limit
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Dynamics.Flow

/-!
# ω-limits

For a function `ϕ : τ → α → β` where `β` is a topological space, we
define the ω-limit under `ϕ` of a set `s` in `α` with respect to
filter `f` on `τ`: an element `y : β` is in the ω-limit of `s` if the
forward images of `s` intersect arbitrarily small neighbourhoods of
`y` frequently "in the direction of `f`".

In practice `ϕ` is often a continuous monoid-act, but the definition
requires only that `ϕ` has a coercion to the appropriate function
type. In the case where `τ` is `ℕ` or `ℝ` and `f` is `at_top`, we
recover the usual definition of the ω-limit set as the set of all `y`
such that there exist sequences `(tₙ)`, `(xₙ)` such that `ϕ tₙ xₙ ⟶ y`
as `n ⟶ ∞`.

## Notations

The `omega_limit` locale provides the localised notation `ω` for
`omega_limit`, as well as `ω⁺` and `ω⁻` for `omega_limit at_top` and
`omega_limit at_bot` respectively for when the acting monoid is
endowed with an order.
-/


open Set Function Filter

open Topology

/-!
### Definition and notation
-/


section omegaLimit

variable {τ : Type _} {α : Type _} {β : Type _} {ι : Type _}

#print omegaLimit /-
/-- The ω-limit of a set `s` under `ϕ` with respect to a filter `f` is
    ⋂ u ∈ f, cl (ϕ u s). -/
def omegaLimit [TopologicalSpace β] (f : Filter τ) (ϕ : τ → α → β) (s : Set α) : Set β :=
  ⋂ u ∈ f, closure (image2 ϕ u s)
#align omega_limit omegaLimit
-/

-- mathport name: omega_limit
scoped[omegaLimit] notation "ω" => omegaLimit

-- mathport name: omega_limit.at_top
scoped[omegaLimit] notation "ω⁺" => omegaLimit Filter.atTop

-- mathport name: omega_limit.at_bot
scoped[omegaLimit] notation "ω⁻" => omegaLimit Filter.atBot

variable [TopologicalSpace β]

variable (f : Filter τ) (ϕ : τ → α → β) (s s₁ s₂ : Set α)

/-!
### Elementary properties
-/


/- warning: omega_limit_def -> omegaLimit_def is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u1} τ) (ϕ : τ -> α -> β) (s : Set.{u2} α), Eq.{succ u3} (Set.{u3} β) (omegaLimit.{u1, u2, u3} τ α β _inst_1 f ϕ s) (Set.interᵢ.{u3, succ u1} β (Set.{u1} τ) (fun (u : Set.{u1} τ) => Set.interᵢ.{u3, 0} β (Membership.Mem.{u1, u1} (Set.{u1} τ) (Filter.{u1} τ) (Filter.hasMem.{u1} τ) u f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} τ) (Filter.{u1} τ) (Filter.hasMem.{u1} τ) u f) => closure.{u3} β _inst_1 (Set.image2.{u1, u2, u3} τ α β ϕ u s))))
but is expected to have type
  forall {τ : Type.{u2}} {α : Type.{u1}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u2} τ) (ϕ : τ -> α -> β) (s : Set.{u1} α), Eq.{succ u3} (Set.{u3} β) (omegaLimit.{u2, u1, u3} τ α β _inst_1 f ϕ s) (Set.interᵢ.{u3, succ u2} β (Set.{u2} τ) (fun (u : Set.{u2} τ) => Set.interᵢ.{u3, 0} β (Membership.mem.{u2, u2} (Set.{u2} τ) (Filter.{u2} τ) (instMembershipSetFilter.{u2} τ) u f) (fun (H : Membership.mem.{u2, u2} (Set.{u2} τ) (Filter.{u2} τ) (instMembershipSetFilter.{u2} τ) u f) => closure.{u3} β _inst_1 (Set.image2.{u2, u1, u3} τ α β ϕ u s))))
Case conversion may be inaccurate. Consider using '#align omega_limit_def omegaLimit_defₓ'. -/
theorem omegaLimit_def : ω f ϕ s = ⋂ u ∈ f, closure (image2 ϕ u s) :=
  rfl
#align omega_limit_def omegaLimit_def

/- warning: omega_limit_subset_of_tendsto -> omegaLimit_subset_of_tendsto is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (ϕ : τ -> α -> β) (s : Set.{u2} α) {m : τ -> τ} {f₁ : Filter.{u1} τ} {f₂ : Filter.{u1} τ}, (Filter.Tendsto.{u1, u1} τ τ m f₁ f₂) -> (HasSubset.Subset.{u3} (Set.{u3} β) (Set.hasSubset.{u3} β) (omegaLimit.{u1, u2, u3} τ α β _inst_1 f₁ (fun (t : τ) (x : α) => ϕ (m t) x) s) (omegaLimit.{u1, u2, u3} τ α β _inst_1 f₂ ϕ s))
but is expected to have type
  forall {τ : Type.{u3}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} β] (ϕ : τ -> α -> β) (s : Set.{u1} α) {m : τ -> τ} {f₁ : Filter.{u3} τ} {f₂ : Filter.{u3} τ}, (Filter.Tendsto.{u3, u3} τ τ m f₁ f₂) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) (omegaLimit.{u3, u1, u2} τ α β _inst_1 f₁ (fun (t : τ) (x : α) => ϕ (m t) x) s) (omegaLimit.{u3, u1, u2} τ α β _inst_1 f₂ ϕ s))
Case conversion may be inaccurate. Consider using '#align omega_limit_subset_of_tendsto omegaLimit_subset_of_tendstoₓ'. -/
theorem omegaLimit_subset_of_tendsto {m : τ → τ} {f₁ f₂ : Filter τ} (hf : Tendsto m f₁ f₂) :
    ω f₁ (fun t x => ϕ (m t) x) s ⊆ ω f₂ ϕ s :=
  by
  refine' Inter₂_mono' fun u hu => ⟨m ⁻¹' u, tendsto_def.mp hf _ hu, _⟩
  rw [← image2_image_left]
  exact closure_mono (image2_subset (image_preimage_subset _ _) subset.rfl)
#align omega_limit_subset_of_tendsto omegaLimit_subset_of_tendsto

/- warning: omega_limit_mono_left -> omegaLimit_mono_left is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (ϕ : τ -> α -> β) (s : Set.{u2} α) {f₁ : Filter.{u1} τ} {f₂ : Filter.{u1} τ}, (LE.le.{u1} (Filter.{u1} τ) (Preorder.toLE.{u1} (Filter.{u1} τ) (PartialOrder.toPreorder.{u1} (Filter.{u1} τ) (Filter.partialOrder.{u1} τ))) f₁ f₂) -> (HasSubset.Subset.{u3} (Set.{u3} β) (Set.hasSubset.{u3} β) (omegaLimit.{u1, u2, u3} τ α β _inst_1 f₁ ϕ s) (omegaLimit.{u1, u2, u3} τ α β _inst_1 f₂ ϕ s))
but is expected to have type
  forall {τ : Type.{u3}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} β] (ϕ : τ -> α -> β) (s : Set.{u1} α) {f₁ : Filter.{u3} τ} {f₂ : Filter.{u3} τ}, (LE.le.{u3} (Filter.{u3} τ) (Preorder.toLE.{u3} (Filter.{u3} τ) (PartialOrder.toPreorder.{u3} (Filter.{u3} τ) (Filter.instPartialOrderFilter.{u3} τ))) f₁ f₂) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) (omegaLimit.{u3, u1, u2} τ α β _inst_1 f₁ ϕ s) (omegaLimit.{u3, u1, u2} τ α β _inst_1 f₂ ϕ s))
Case conversion may be inaccurate. Consider using '#align omega_limit_mono_left omegaLimit_mono_leftₓ'. -/
theorem omegaLimit_mono_left {f₁ f₂ : Filter τ} (hf : f₁ ≤ f₂) : ω f₁ ϕ s ⊆ ω f₂ ϕ s :=
  omegaLimit_subset_of_tendsto ϕ s (tendsto_id'.2 hf)
#align omega_limit_mono_left omegaLimit_mono_left

/- warning: omega_limit_mono_right -> omegaLimit_mono_right is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u1} τ) (ϕ : τ -> α -> β) {s₁ : Set.{u2} α} {s₂ : Set.{u2} α}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.hasSubset.{u2} α) s₁ s₂) -> (HasSubset.Subset.{u3} (Set.{u3} β) (Set.hasSubset.{u3} β) (omegaLimit.{u1, u2, u3} τ α β _inst_1 f ϕ s₁) (omegaLimit.{u1, u2, u3} τ α β _inst_1 f ϕ s₂))
but is expected to have type
  forall {τ : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} β] (f : Filter.{u1} τ) (ϕ : τ -> α -> β) {s₁ : Set.{u3} α} {s₂ : Set.{u3} α}, (HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) s₁ s₂) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) (omegaLimit.{u1, u3, u2} τ α β _inst_1 f ϕ s₁) (omegaLimit.{u1, u3, u2} τ α β _inst_1 f ϕ s₂))
Case conversion may be inaccurate. Consider using '#align omega_limit_mono_right omegaLimit_mono_rightₓ'. -/
theorem omegaLimit_mono_right {s₁ s₂ : Set α} (hs : s₁ ⊆ s₂) : ω f ϕ s₁ ⊆ ω f ϕ s₂ :=
  interᵢ₂_mono fun u hu => closure_mono (image2_subset Subset.rfl hs)
#align omega_limit_mono_right omegaLimit_mono_right

/- warning: is_closed_omega_limit -> isClosed_omegaLimit is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u1} τ) (ϕ : τ -> α -> β) (s : Set.{u2} α), IsClosed.{u3} β _inst_1 (omegaLimit.{u1, u2, u3} τ α β _inst_1 f ϕ s)
but is expected to have type
  forall {τ : Type.{u2}} {α : Type.{u1}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u2} τ) (ϕ : τ -> α -> β) (s : Set.{u1} α), IsClosed.{u3} β _inst_1 (omegaLimit.{u2, u1, u3} τ α β _inst_1 f ϕ s)
Case conversion may be inaccurate. Consider using '#align is_closed_omega_limit isClosed_omegaLimitₓ'. -/
theorem isClosed_omegaLimit : IsClosed (ω f ϕ s) :=
  isClosed_interᵢ fun u => isClosed_interᵢ fun hu => isClosed_closure
#align is_closed_omega_limit isClosed_omegaLimit

/- warning: maps_to_omega_limit' -> mapsTo_omega_limit' is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (s : Set.{u2} α) {α' : Type.{u4}} {β' : Type.{u5}} [_inst_2 : TopologicalSpace.{u5} β'] {f : Filter.{u1} τ} {ϕ : τ -> α -> β} {ϕ' : τ -> α' -> β'} {ga : α -> α'} {s' : Set.{u4} α'}, (Set.MapsTo.{u2, u4} α α' ga s s') -> (forall {gb : β -> β'}, (Filter.Eventually.{u1} τ (fun (t : τ) => Set.EqOn.{u2, u5} α β' (Function.comp.{succ u2, succ u3, succ u5} α β β' gb (ϕ t)) (Function.comp.{succ u2, succ u4, succ u5} α α' β' (ϕ' t) ga) s) f) -> (Continuous.{u3, u5} β β' _inst_1 _inst_2 gb) -> (Set.MapsTo.{u3, u5} β β' gb (omegaLimit.{u1, u2, u3} τ α β _inst_1 f ϕ s) (omegaLimit.{u1, u4, u5} τ α' β' _inst_2 f ϕ' s')))
but is expected to have type
  forall {τ : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} β] (s : Set.{u2} α) {α' : Type.{u5}} {β' : Type.{u4}} [_inst_2 : TopologicalSpace.{u4} β'] {f : Filter.{u3} τ} {ϕ : τ -> α -> β} {ϕ' : τ -> α' -> β'} {ga : α -> α'} {s' : Set.{u5} α'}, (Set.MapsTo.{u2, u5} α α' ga s s') -> (forall {gb : β -> β'}, (Filter.Eventually.{u3} τ (fun (t : τ) => Set.EqOn.{u2, u4} α β' (Function.comp.{succ u2, succ u1, succ u4} α β β' gb (ϕ t)) (Function.comp.{succ u2, succ u5, succ u4} α α' β' (ϕ' t) ga) s) f) -> (Continuous.{u1, u4} β β' _inst_1 _inst_2 gb) -> (Set.MapsTo.{u1, u4} β β' gb (omegaLimit.{u3, u2, u1} τ α β _inst_1 f ϕ s) (omegaLimit.{u3, u5, u4} τ α' β' _inst_2 f ϕ' s')))
Case conversion may be inaccurate. Consider using '#align maps_to_omega_limit' mapsTo_omega_limit'ₓ'. -/
theorem mapsTo_omega_limit' {α' β' : Type _} [TopologicalSpace β'] {f : Filter τ} {ϕ : τ → α → β}
    {ϕ' : τ → α' → β'} {ga : α → α'} {s' : Set α'} (hs : MapsTo ga s s') {gb : β → β'}
    (hg : ∀ᶠ t in f, EqOn (gb ∘ ϕ t) (ϕ' t ∘ ga) s) (hgc : Continuous gb) :
    MapsTo gb (ω f ϕ s) (ω f ϕ' s') :=
  by
  simp only [omegaLimit_def, mem_Inter, maps_to]
  intro y hy u hu
  refine' map_mem_closure hgc (hy _ (inter_mem hu hg)) (forall_image2_iff.2 fun t ht x hx => _)
  calc
    gb (ϕ t x) = ϕ' t (ga x) := ht.2 hx
    _ ∈ image2 ϕ' u s' := mem_image2_of_mem ht.1 (hs hx)
    
#align maps_to_omega_limit' mapsTo_omega_limit'

/- warning: maps_to_omega_limit -> mapsTo_omegaLimit is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (s : Set.{u2} α) {α' : Type.{u4}} {β' : Type.{u5}} [_inst_2 : TopologicalSpace.{u5} β'] {f : Filter.{u1} τ} {ϕ : τ -> α -> β} {ϕ' : τ -> α' -> β'} {ga : α -> α'} {s' : Set.{u4} α'}, (Set.MapsTo.{u2, u4} α α' ga s s') -> (forall {gb : β -> β'}, (forall (t : τ) (x : α), Eq.{succ u5} β' (gb (ϕ t x)) (ϕ' t (ga x))) -> (Continuous.{u3, u5} β β' _inst_1 _inst_2 gb) -> (Set.MapsTo.{u3, u5} β β' gb (omegaLimit.{u1, u2, u3} τ α β _inst_1 f ϕ s) (omegaLimit.{u1, u4, u5} τ α' β' _inst_2 f ϕ' s')))
but is expected to have type
  forall {τ : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} β] (s : Set.{u2} α) {α' : Type.{u5}} {β' : Type.{u4}} [_inst_2 : TopologicalSpace.{u4} β'] {f : Filter.{u3} τ} {ϕ : τ -> α -> β} {ϕ' : τ -> α' -> β'} {ga : α -> α'} {s' : Set.{u5} α'}, (Set.MapsTo.{u2, u5} α α' ga s s') -> (forall {gb : β -> β'}, (forall (t : τ) (x : α), Eq.{succ u4} β' (gb (ϕ t x)) (ϕ' t (ga x))) -> (Continuous.{u1, u4} β β' _inst_1 _inst_2 gb) -> (Set.MapsTo.{u1, u4} β β' gb (omegaLimit.{u3, u2, u1} τ α β _inst_1 f ϕ s) (omegaLimit.{u3, u5, u4} τ α' β' _inst_2 f ϕ' s')))
Case conversion may be inaccurate. Consider using '#align maps_to_omega_limit mapsTo_omegaLimitₓ'. -/
theorem mapsTo_omegaLimit {α' β' : Type _} [TopologicalSpace β'] {f : Filter τ} {ϕ : τ → α → β}
    {ϕ' : τ → α' → β'} {ga : α → α'} {s' : Set α'} (hs : MapsTo ga s s') {gb : β → β'}
    (hg : ∀ t x, gb (ϕ t x) = ϕ' t (ga x)) (hgc : Continuous gb) :
    MapsTo gb (ω f ϕ s) (ω f ϕ' s') :=
  mapsTo_omega_limit' _ hs (eventually_of_forall fun t x hx => hg t x) hgc
#align maps_to_omega_limit mapsTo_omegaLimit

/- warning: omega_limit_image_eq -> omegaLimit_image_eq is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (s : Set.{u2} α) {α' : Type.{u4}} (ϕ : τ -> α' -> β) (f : Filter.{u1} τ) (g : α -> α'), Eq.{succ u3} (Set.{u3} β) (omegaLimit.{u1, u4, u3} τ α' β _inst_1 f ϕ (Set.image.{u2, u4} α α' g s)) (omegaLimit.{u1, u2, u3} τ α β _inst_1 f (fun (t : τ) (x : α) => ϕ t (g x)) s)
but is expected to have type
  forall {τ : Type.{u3}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} β] (s : Set.{u1} α) {α' : Type.{u4}} (ϕ : τ -> α' -> β) (f : Filter.{u3} τ) (g : α -> α'), Eq.{succ u2} (Set.{u2} β) (omegaLimit.{u3, u4, u2} τ α' β _inst_1 f ϕ (Set.image.{u1, u4} α α' g s)) (omegaLimit.{u3, u1, u2} τ α β _inst_1 f (fun (t : τ) (x : α) => ϕ t (g x)) s)
Case conversion may be inaccurate. Consider using '#align omega_limit_image_eq omegaLimit_image_eqₓ'. -/
theorem omegaLimit_image_eq {α' : Type _} (ϕ : τ → α' → β) (f : Filter τ) (g : α → α') :
    ω f ϕ (g '' s) = ω f (fun t x => ϕ t (g x)) s := by simp only [omegaLimit, image2_image_right]
#align omega_limit_image_eq omegaLimit_image_eq

/- warning: omega_limit_preimage_subset -> omegaLimit_preimage_subset is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] {α' : Type.{u4}} (ϕ : τ -> α' -> β) (s : Set.{u4} α') (f : Filter.{u1} τ) (g : α -> α'), HasSubset.Subset.{u3} (Set.{u3} β) (Set.hasSubset.{u3} β) (omegaLimit.{u1, u2, u3} τ α β _inst_1 f (fun (t : τ) (x : α) => ϕ t (g x)) (Set.preimage.{u2, u4} α α' g s)) (omegaLimit.{u1, u4, u3} τ α' β _inst_1 f ϕ s)
but is expected to have type
  forall {τ : Type.{u3}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} β] {α' : Type.{u4}} (ϕ : τ -> α' -> β) (s : Set.{u4} α') (f : Filter.{u3} τ) (g : α -> α'), HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) (omegaLimit.{u3, u1, u2} τ α β _inst_1 f (fun (t : τ) (x : α) => ϕ t (g x)) (Set.preimage.{u1, u4} α α' g s)) (omegaLimit.{u3, u4, u2} τ α' β _inst_1 f ϕ s)
Case conversion may be inaccurate. Consider using '#align omega_limit_preimage_subset omegaLimit_preimage_subsetₓ'. -/
theorem omegaLimit_preimage_subset {α' : Type _} (ϕ : τ → α' → β) (s : Set α') (f : Filter τ)
    (g : α → α') : ω f (fun t x => ϕ t (g x)) (g ⁻¹' s) ⊆ ω f ϕ s :=
  mapsTo_omegaLimit _ (mapsTo_preimage _ _) (fun t x => rfl) continuous_id
#align omega_limit_preimage_subset omegaLimit_preimage_subset

/-!
### Equivalent definitions of the omega limit

The next few lemmas are various versions of the property
characterising ω-limits:
-/


/- warning: mem_omega_limit_iff_frequently -> mem_omegaLimit_iff_frequently is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u1} τ) (ϕ : τ -> α -> β) (s : Set.{u2} α) (y : β), Iff (Membership.Mem.{u3, u3} β (Set.{u3} β) (Set.hasMem.{u3} β) y (omegaLimit.{u1, u2, u3} τ α β _inst_1 f ϕ s)) (forall (n : Set.{u3} β), (Membership.Mem.{u3, u3} (Set.{u3} β) (Filter.{u3} β) (Filter.hasMem.{u3} β) n (nhds.{u3} β _inst_1 y)) -> (Filter.Frequently.{u1} τ (fun (t : τ) => Set.Nonempty.{u2} α (Inter.inter.{u2} (Set.{u2} α) (Set.hasInter.{u2} α) s (Set.preimage.{u2, u3} α β (ϕ t) n))) f))
but is expected to have type
  forall {τ : Type.{u2}} {α : Type.{u1}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u2} τ) (ϕ : τ -> α -> β) (s : Set.{u1} α) (y : β), Iff (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) y (omegaLimit.{u2, u1, u3} τ α β _inst_1 f ϕ s)) (forall (n : Set.{u3} β), (Membership.mem.{u3, u3} (Set.{u3} β) (Filter.{u3} β) (instMembershipSetFilter.{u3} β) n (nhds.{u3} β _inst_1 y)) -> (Filter.Frequently.{u2} τ (fun (t : τ) => Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (Set.preimage.{u1, u3} α β (ϕ t) n))) f))
Case conversion may be inaccurate. Consider using '#align mem_omega_limit_iff_frequently mem_omegaLimit_iff_frequentlyₓ'. -/
/-- An element `y` is in the ω-limit set of `s` w.r.t. `f` if the
    preimages of an arbitrary neighbourhood of `y` frequently
    (w.r.t. `f`) intersects of `s`. -/
theorem mem_omegaLimit_iff_frequently (y : β) :
    y ∈ ω f ϕ s ↔ ∀ n ∈ 𝓝 y, ∃ᶠ t in f, (s ∩ ϕ t ⁻¹' n).Nonempty :=
  by
  simp_rw [frequently_iff, omegaLimit_def, mem_Inter, mem_closure_iff_nhds]
  constructor
  · intro h _ hn _ hu
    rcases h _ hu _ hn with ⟨_, _, _, _, ht, hx, hϕtx⟩
    exact ⟨_, ht, _, hx, by rwa [mem_preimage, hϕtx]⟩
  · intro h _ hu _ hn
    rcases h _ hn hu with ⟨_, ht, _, hx, hϕtx⟩
    exact ⟨_, hϕtx, _, _, ht, hx, rfl⟩
#align mem_omega_limit_iff_frequently mem_omegaLimit_iff_frequently

/- warning: mem_omega_limit_iff_frequently₂ -> mem_omegaLimit_iff_frequently₂ is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u1} τ) (ϕ : τ -> α -> β) (s : Set.{u2} α) (y : β), Iff (Membership.Mem.{u3, u3} β (Set.{u3} β) (Set.hasMem.{u3} β) y (omegaLimit.{u1, u2, u3} τ α β _inst_1 f ϕ s)) (forall (n : Set.{u3} β), (Membership.Mem.{u3, u3} (Set.{u3} β) (Filter.{u3} β) (Filter.hasMem.{u3} β) n (nhds.{u3} β _inst_1 y)) -> (Filter.Frequently.{u1} τ (fun (t : τ) => Set.Nonempty.{u3} β (Inter.inter.{u3} (Set.{u3} β) (Set.hasInter.{u3} β) (Set.image.{u2, u3} α β (ϕ t) s) n)) f))
but is expected to have type
  forall {τ : Type.{u2}} {α : Type.{u1}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u2} τ) (ϕ : τ -> α -> β) (s : Set.{u1} α) (y : β), Iff (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) y (omegaLimit.{u2, u1, u3} τ α β _inst_1 f ϕ s)) (forall (n : Set.{u3} β), (Membership.mem.{u3, u3} (Set.{u3} β) (Filter.{u3} β) (instMembershipSetFilter.{u3} β) n (nhds.{u3} β _inst_1 y)) -> (Filter.Frequently.{u2} τ (fun (t : τ) => Set.Nonempty.{u3} β (Inter.inter.{u3} (Set.{u3} β) (Set.instInterSet.{u3} β) (Set.image.{u1, u3} α β (ϕ t) s) n)) f))
Case conversion may be inaccurate. Consider using '#align mem_omega_limit_iff_frequently₂ mem_omegaLimit_iff_frequently₂ₓ'. -/
/-- An element `y` is in the ω-limit set of `s` w.r.t. `f` if the
    forward images of `s` frequently (w.r.t. `f`) intersect arbitrary
    neighbourhoods of `y`. -/
theorem mem_omegaLimit_iff_frequently₂ (y : β) :
    y ∈ ω f ϕ s ↔ ∀ n ∈ 𝓝 y, ∃ᶠ t in f, (ϕ t '' s ∩ n).Nonempty := by
  simp_rw [mem_omegaLimit_iff_frequently, image_inter_nonempty_iff]
#align mem_omega_limit_iff_frequently₂ mem_omegaLimit_iff_frequently₂

/- warning: mem_omega_limit_singleton_iff_map_cluster_point -> mem_omegaLimit_singleton_iff_map_cluster_point is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u1} τ) (ϕ : τ -> α -> β) (x : α) (y : β), Iff (Membership.Mem.{u3, u3} β (Set.{u3} β) (Set.hasMem.{u3} β) y (omegaLimit.{u1, u2, u3} τ α β _inst_1 f ϕ (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.hasSingleton.{u2} α) x))) (MapClusterPt.{u3, u1} β _inst_1 τ y f (fun (t : τ) => ϕ t x))
but is expected to have type
  forall {τ : Type.{u2}} {α : Type.{u1}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u2} τ) (ϕ : τ -> α -> β) (x : α) (y : β), Iff (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) y (omegaLimit.{u2, u1, u3} τ α β _inst_1 f ϕ (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x))) (MapClusterPt.{u3, u2} β _inst_1 τ y f (fun (t : τ) => ϕ t x))
Case conversion may be inaccurate. Consider using '#align mem_omega_limit_singleton_iff_map_cluster_point mem_omegaLimit_singleton_iff_map_cluster_pointₓ'. -/
/-- An element `y` is in the ω-limit of `x` w.r.t. `f` if the forward
    images of `x` frequently (w.r.t. `f`) falls within an arbitrary
    neighbourhood of `y`. -/
theorem mem_omegaLimit_singleton_iff_map_cluster_point (x : α) (y : β) :
    y ∈ ω f ϕ {x} ↔ MapClusterPt y f fun t => ϕ t x := by
  simp_rw [mem_omegaLimit_iff_frequently, mapClusterPt_iff, singleton_inter_nonempty, mem_preimage]
#align mem_omega_limit_singleton_iff_map_cluster_point mem_omegaLimit_singleton_iff_map_cluster_point

/-!
### Set operations and omega limits
-/


/- warning: omega_limit_inter -> omegaLimit_inter is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u1} τ) (ϕ : τ -> α -> β) (s₁ : Set.{u2} α) (s₂ : Set.{u2} α), HasSubset.Subset.{u3} (Set.{u3} β) (Set.hasSubset.{u3} β) (omegaLimit.{u1, u2, u3} τ α β _inst_1 f ϕ (Inter.inter.{u2} (Set.{u2} α) (Set.hasInter.{u2} α) s₁ s₂)) (Inter.inter.{u3} (Set.{u3} β) (Set.hasInter.{u3} β) (omegaLimit.{u1, u2, u3} τ α β _inst_1 f ϕ s₁) (omegaLimit.{u1, u2, u3} τ α β _inst_1 f ϕ s₂))
but is expected to have type
  forall {τ : Type.{u2}} {α : Type.{u1}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u2} τ) (ϕ : τ -> α -> β) (s₁ : Set.{u1} α) (s₂ : Set.{u1} α), HasSubset.Subset.{u3} (Set.{u3} β) (Set.instHasSubsetSet.{u3} β) (omegaLimit.{u2, u1, u3} τ α β _inst_1 f ϕ (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s₁ s₂)) (Inter.inter.{u3} (Set.{u3} β) (Set.instInterSet.{u3} β) (omegaLimit.{u2, u1, u3} τ α β _inst_1 f ϕ s₁) (omegaLimit.{u2, u1, u3} τ α β _inst_1 f ϕ s₂))
Case conversion may be inaccurate. Consider using '#align omega_limit_inter omegaLimit_interₓ'. -/
theorem omegaLimit_inter : ω f ϕ (s₁ ∩ s₂) ⊆ ω f ϕ s₁ ∩ ω f ϕ s₂ :=
  subset_inter (omegaLimit_mono_right _ _ (inter_subset_left _ _))
    (omegaLimit_mono_right _ _ (inter_subset_right _ _))
#align omega_limit_inter omegaLimit_inter

/- warning: omega_limit_Inter -> omegaLimit_interᵢ is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {ι : Type.{u4}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u1} τ) (ϕ : τ -> α -> β) (p : ι -> (Set.{u2} α)), HasSubset.Subset.{u3} (Set.{u3} β) (Set.hasSubset.{u3} β) (omegaLimit.{u1, u2, u3} τ α β _inst_1 f ϕ (Set.interᵢ.{u2, succ u4} α ι (fun (i : ι) => p i))) (Set.interᵢ.{u3, succ u4} β ι (fun (i : ι) => omegaLimit.{u1, u2, u3} τ α β _inst_1 f ϕ (p i)))
but is expected to have type
  forall {τ : Type.{u2}} {α : Type.{u4}} {β : Type.{u3}} {ι : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u2} τ) (ϕ : τ -> α -> β) (p : ι -> (Set.{u4} α)), HasSubset.Subset.{u3} (Set.{u3} β) (Set.instHasSubsetSet.{u3} β) (omegaLimit.{u2, u4, u3} τ α β _inst_1 f ϕ (Set.interᵢ.{u4, succ u1} α ι (fun (i : ι) => p i))) (Set.interᵢ.{u3, succ u1} β ι (fun (i : ι) => omegaLimit.{u2, u4, u3} τ α β _inst_1 f ϕ (p i)))
Case conversion may be inaccurate. Consider using '#align omega_limit_Inter omegaLimit_interᵢₓ'. -/
theorem omegaLimit_interᵢ (p : ι → Set α) : ω f ϕ (⋂ i, p i) ⊆ ⋂ i, ω f ϕ (p i) :=
  subset_interᵢ fun i => omegaLimit_mono_right _ _ (interᵢ_subset _ _)
#align omega_limit_Inter omegaLimit_interᵢ

/- warning: omega_limit_union -> omegaLimit_union is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u1} τ) (ϕ : τ -> α -> β) (s₁ : Set.{u2} α) (s₂ : Set.{u2} α), Eq.{succ u3} (Set.{u3} β) (omegaLimit.{u1, u2, u3} τ α β _inst_1 f ϕ (Union.union.{u2} (Set.{u2} α) (Set.hasUnion.{u2} α) s₁ s₂)) (Union.union.{u3} (Set.{u3} β) (Set.hasUnion.{u3} β) (omegaLimit.{u1, u2, u3} τ α β _inst_1 f ϕ s₁) (omegaLimit.{u1, u2, u3} τ α β _inst_1 f ϕ s₂))
but is expected to have type
  forall {τ : Type.{u2}} {α : Type.{u1}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u2} τ) (ϕ : τ -> α -> β) (s₁ : Set.{u1} α) (s₂ : Set.{u1} α), Eq.{succ u3} (Set.{u3} β) (omegaLimit.{u2, u1, u3} τ α β _inst_1 f ϕ (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₁ s₂)) (Union.union.{u3} (Set.{u3} β) (Set.instUnionSet.{u3} β) (omegaLimit.{u2, u1, u3} τ α β _inst_1 f ϕ s₁) (omegaLimit.{u2, u1, u3} τ α β _inst_1 f ϕ s₂))
Case conversion may be inaccurate. Consider using '#align omega_limit_union omegaLimit_unionₓ'. -/
theorem omegaLimit_union : ω f ϕ (s₁ ∪ s₂) = ω f ϕ s₁ ∪ ω f ϕ s₂ :=
  by
  ext y; constructor
  · simp only [mem_union, mem_omegaLimit_iff_frequently, union_inter_distrib_right, union_nonempty,
      frequently_or_distrib]
    contrapose!
    simp only [not_frequently, not_nonempty_iff_eq_empty, ← subset_empty_iff]
    rintro ⟨⟨n₁, hn₁, h₁⟩, ⟨n₂, hn₂, h₂⟩⟩
    refine' ⟨n₁ ∩ n₂, inter_mem hn₁ hn₂, h₁.mono fun t => _, h₂.mono fun t => _⟩
    exacts[subset.trans <| inter_subset_inter_right _ <| preimage_mono <| inter_subset_left _ _,
      subset.trans <| inter_subset_inter_right _ <| preimage_mono <| inter_subset_right _ _]
  · rintro (hy | hy)
    exacts[omegaLimit_mono_right _ _ (subset_union_left _ _) hy,
      omegaLimit_mono_right _ _ (subset_union_right _ _) hy]
#align omega_limit_union omegaLimit_union

/- warning: omega_limit_Union -> omegaLimit_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {ι : Type.{u4}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u1} τ) (ϕ : τ -> α -> β) (p : ι -> (Set.{u2} α)), HasSubset.Subset.{u3} (Set.{u3} β) (Set.hasSubset.{u3} β) (Set.unionᵢ.{u3, succ u4} β ι (fun (i : ι) => omegaLimit.{u1, u2, u3} τ α β _inst_1 f ϕ (p i))) (omegaLimit.{u1, u2, u3} τ α β _inst_1 f ϕ (Set.unionᵢ.{u2, succ u4} α ι (fun (i : ι) => p i)))
but is expected to have type
  forall {τ : Type.{u1}} {α : Type.{u4}} {β : Type.{u3}} {ι : Type.{u2}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u1} τ) (ϕ : τ -> α -> β) (p : ι -> (Set.{u4} α)), HasSubset.Subset.{u3} (Set.{u3} β) (Set.instHasSubsetSet.{u3} β) (Set.unionᵢ.{u3, succ u2} β ι (fun (i : ι) => omegaLimit.{u1, u4, u3} τ α β _inst_1 f ϕ (p i))) (omegaLimit.{u1, u4, u3} τ α β _inst_1 f ϕ (Set.unionᵢ.{u4, succ u2} α ι (fun (i : ι) => p i)))
Case conversion may be inaccurate. Consider using '#align omega_limit_Union omegaLimit_unionᵢₓ'. -/
theorem omegaLimit_unionᵢ (p : ι → Set α) : (⋃ i, ω f ϕ (p i)) ⊆ ω f ϕ (⋃ i, p i) :=
  by
  rw [Union_subset_iff]
  exact fun i => omegaLimit_mono_right _ _ (subset_Union _ _)
#align omega_limit_Union omegaLimit_unionᵢ

/-!
Different expressions for omega limits, useful for rewrites. In
particular, one may restrict the intersection to sets in `f` which are
subsets of some set `v` also in `f`.
-/


/- warning: omega_limit_eq_Inter -> omegaLimit_eq_interᵢ is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u1} τ) (ϕ : τ -> α -> β) (s : Set.{u2} α), Eq.{succ u3} (Set.{u3} β) (omegaLimit.{u1, u2, u3} τ α β _inst_1 f ϕ s) (Set.interᵢ.{u3, succ u1} β (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} τ)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} τ)) (Filter.sets.{u1} τ f)) (fun (u : coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} τ)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} τ)) (Filter.sets.{u1} τ f)) => closure.{u3} β _inst_1 (Set.image2.{u1, u2, u3} τ α β ϕ ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} τ)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} τ)) (Filter.sets.{u1} τ f)) (Set.{u1} τ) (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} τ)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} τ)) (Filter.sets.{u1} τ f)) (Set.{u1} τ) (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} τ)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} τ)) (Filter.sets.{u1} τ f)) (Set.{u1} τ) (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} τ)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} τ)) (Filter.sets.{u1} τ f)) (Set.{u1} τ) (coeSubtype.{succ u1} (Set.{u1} τ) (fun (x : Set.{u1} τ) => Membership.Mem.{u1, u1} (Set.{u1} τ) (Set.{u1} (Set.{u1} τ)) (Set.hasMem.{u1} (Set.{u1} τ)) x (Filter.sets.{u1} τ f)))))) u) s)))
but is expected to have type
  forall {τ : Type.{u2}} {α : Type.{u1}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u2} τ) (ϕ : τ -> α -> β) (s : Set.{u1} α), Eq.{succ u3} (Set.{u3} β) (omegaLimit.{u2, u1, u3} τ α β _inst_1 f ϕ s) (Set.interᵢ.{u3, succ u2} β (Set.Elem.{u2} (Set.{u2} τ) (Filter.sets.{u2} τ f)) (fun (u : Set.Elem.{u2} (Set.{u2} τ) (Filter.sets.{u2} τ f)) => closure.{u3} β _inst_1 (Set.image2.{u2, u1, u3} τ α β ϕ (Subtype.val.{succ u2} (Set.{u2} τ) (fun (x : Set.{u2} τ) => Membership.mem.{u2, u2} (Set.{u2} τ) (Set.{u2} (Set.{u2} τ)) (Set.instMembershipSet.{u2} (Set.{u2} τ)) x (Filter.sets.{u2} τ f)) u) s)))
Case conversion may be inaccurate. Consider using '#align omega_limit_eq_Inter omegaLimit_eq_interᵢₓ'. -/
theorem omegaLimit_eq_interᵢ : ω f ϕ s = ⋂ u : ↥f.sets, closure (image2 ϕ u s) :=
  binterᵢ_eq_interᵢ _ _
#align omega_limit_eq_Inter omegaLimit_eq_interᵢ

/- warning: omega_limit_eq_bInter_inter -> omegaLimit_eq_bInter_inter is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u1} τ) (ϕ : τ -> α -> β) (s : Set.{u2} α) {v : Set.{u1} τ}, (Membership.Mem.{u1, u1} (Set.{u1} τ) (Filter.{u1} τ) (Filter.hasMem.{u1} τ) v f) -> (Eq.{succ u3} (Set.{u3} β) (omegaLimit.{u1, u2, u3} τ α β _inst_1 f ϕ s) (Set.interᵢ.{u3, succ u1} β (Set.{u1} τ) (fun (u : Set.{u1} τ) => Set.interᵢ.{u3, 0} β (Membership.Mem.{u1, u1} (Set.{u1} τ) (Filter.{u1} τ) (Filter.hasMem.{u1} τ) u f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} τ) (Filter.{u1} τ) (Filter.hasMem.{u1} τ) u f) => closure.{u3} β _inst_1 (Set.image2.{u1, u2, u3} τ α β ϕ (Inter.inter.{u1} (Set.{u1} τ) (Set.hasInter.{u1} τ) u v) s)))))
but is expected to have type
  forall {τ : Type.{u3}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} β] (f : Filter.{u3} τ) (ϕ : τ -> α -> β) (s : Set.{u1} α) {v : Set.{u3} τ}, (Membership.mem.{u3, u3} (Set.{u3} τ) (Filter.{u3} τ) (instMembershipSetFilter.{u3} τ) v f) -> (Eq.{succ u2} (Set.{u2} β) (omegaLimit.{u3, u1, u2} τ α β _inst_1 f ϕ s) (Set.interᵢ.{u2, succ u3} β (Set.{u3} τ) (fun (u : Set.{u3} τ) => Set.interᵢ.{u2, 0} β (Membership.mem.{u3, u3} (Set.{u3} τ) (Filter.{u3} τ) (instMembershipSetFilter.{u3} τ) u f) (fun (H : Membership.mem.{u3, u3} (Set.{u3} τ) (Filter.{u3} τ) (instMembershipSetFilter.{u3} τ) u f) => closure.{u2} β _inst_1 (Set.image2.{u3, u1, u2} τ α β ϕ (Inter.inter.{u3} (Set.{u3} τ) (Set.instInterSet.{u3} τ) u v) s)))))
Case conversion may be inaccurate. Consider using '#align omega_limit_eq_bInter_inter omegaLimit_eq_bInter_interₓ'. -/
theorem omegaLimit_eq_bInter_inter {v : Set τ} (hv : v ∈ f) :
    ω f ϕ s = ⋂ u ∈ f, closure (image2 ϕ (u ∩ v) s) :=
  Subset.antisymm (interᵢ₂_mono' fun u hu => ⟨u ∩ v, inter_mem hu hv, Subset.rfl⟩)
    (interᵢ₂_mono fun u hu => closure_mono <| image2_subset (inter_subset_left _ _) Subset.rfl)
#align omega_limit_eq_bInter_inter omegaLimit_eq_bInter_inter

/- warning: omega_limit_eq_Inter_inter -> omegaLimit_eq_interᵢ_inter is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u1} τ) (ϕ : τ -> α -> β) (s : Set.{u2} α) {v : Set.{u1} τ}, (Membership.Mem.{u1, u1} (Set.{u1} τ) (Filter.{u1} τ) (Filter.hasMem.{u1} τ) v f) -> (Eq.{succ u3} (Set.{u3} β) (omegaLimit.{u1, u2, u3} τ α β _inst_1 f ϕ s) (Set.interᵢ.{u3, succ u1} β (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} τ)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} τ)) (Filter.sets.{u1} τ f)) (fun (u : coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} τ)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} τ)) (Filter.sets.{u1} τ f)) => closure.{u3} β _inst_1 (Set.image2.{u1, u2, u3} τ α β ϕ (Inter.inter.{u1} (Set.{u1} τ) (Set.hasInter.{u1} τ) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} τ)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} τ)) (Filter.sets.{u1} τ f)) (Set.{u1} τ) (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} τ)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} τ)) (Filter.sets.{u1} τ f)) (Set.{u1} τ) (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} τ)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} τ)) (Filter.sets.{u1} τ f)) (Set.{u1} τ) (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Set.{u1} τ)) Type.{u1} (Set.hasCoeToSort.{u1} (Set.{u1} τ)) (Filter.sets.{u1} τ f)) (Set.{u1} τ) (coeSubtype.{succ u1} (Set.{u1} τ) (fun (x : Set.{u1} τ) => Membership.Mem.{u1, u1} (Set.{u1} τ) (Set.{u1} (Set.{u1} τ)) (Set.hasMem.{u1} (Set.{u1} τ)) x (Filter.sets.{u1} τ f)))))) u) v) s))))
but is expected to have type
  forall {τ : Type.{u3}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} β] (f : Filter.{u3} τ) (ϕ : τ -> α -> β) (s : Set.{u1} α) {v : Set.{u3} τ}, (Membership.mem.{u3, u3} (Set.{u3} τ) (Filter.{u3} τ) (instMembershipSetFilter.{u3} τ) v f) -> (Eq.{succ u2} (Set.{u2} β) (omegaLimit.{u3, u1, u2} τ α β _inst_1 f ϕ s) (Set.interᵢ.{u2, succ u3} β (Set.Elem.{u3} (Set.{u3} τ) (Filter.sets.{u3} τ f)) (fun (u : Set.Elem.{u3} (Set.{u3} τ) (Filter.sets.{u3} τ f)) => closure.{u2} β _inst_1 (Set.image2.{u3, u1, u2} τ α β ϕ (Inter.inter.{u3} (Set.{u3} τ) (Set.instInterSet.{u3} τ) (Subtype.val.{succ u3} (Set.{u3} τ) (fun (x : Set.{u3} τ) => Membership.mem.{u3, u3} (Set.{u3} τ) (Set.{u3} (Set.{u3} τ)) (Set.instMembershipSet.{u3} (Set.{u3} τ)) x (Filter.sets.{u3} τ f)) u) v) s))))
Case conversion may be inaccurate. Consider using '#align omega_limit_eq_Inter_inter omegaLimit_eq_interᵢ_interₓ'. -/
theorem omegaLimit_eq_interᵢ_inter {v : Set τ} (hv : v ∈ f) :
    ω f ϕ s = ⋂ u : ↥f.sets, closure (image2 ϕ (u ∩ v) s) :=
  by
  rw [omegaLimit_eq_bInter_inter _ _ _ hv]
  apply bInter_eq_Inter
#align omega_limit_eq_Inter_inter omegaLimit_eq_interᵢ_inter

/- warning: omega_limit_subset_closure_fw_image -> omegaLimit_subset_closure_fw_image is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u1} τ) (ϕ : τ -> α -> β) (s : Set.{u2} α) {u : Set.{u1} τ}, (Membership.Mem.{u1, u1} (Set.{u1} τ) (Filter.{u1} τ) (Filter.hasMem.{u1} τ) u f) -> (HasSubset.Subset.{u3} (Set.{u3} β) (Set.hasSubset.{u3} β) (omegaLimit.{u1, u2, u3} τ α β _inst_1 f ϕ s) (closure.{u3} β _inst_1 (Set.image2.{u1, u2, u3} τ α β ϕ u s)))
but is expected to have type
  forall {τ : Type.{u3}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} β] (f : Filter.{u3} τ) (ϕ : τ -> α -> β) (s : Set.{u1} α) {u : Set.{u3} τ}, (Membership.mem.{u3, u3} (Set.{u3} τ) (Filter.{u3} τ) (instMembershipSetFilter.{u3} τ) u f) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) (omegaLimit.{u3, u1, u2} τ α β _inst_1 f ϕ s) (closure.{u2} β _inst_1 (Set.image2.{u3, u1, u2} τ α β ϕ u s)))
Case conversion may be inaccurate. Consider using '#align omega_limit_subset_closure_fw_image omegaLimit_subset_closure_fw_imageₓ'. -/
theorem omegaLimit_subset_closure_fw_image {u : Set τ} (hu : u ∈ f) :
    ω f ϕ s ⊆ closure (image2 ϕ u s) :=
  by
  rw [omegaLimit_eq_interᵢ]
  intro _ hx
  rw [mem_Inter] at hx
  exact hx ⟨u, hu⟩
#align omega_limit_subset_closure_fw_image omegaLimit_subset_closure_fw_image

/-!
### `ω-limits and compactness
-/


/- warning: eventually_closure_subset_of_is_compact_absorbing_of_is_open_of_omega_limit_subset' -> eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset' is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u1} τ) (ϕ : τ -> α -> β) (s : Set.{u2} α) {c : Set.{u3} β}, (IsCompact.{u3} β _inst_1 c) -> (Exists.{succ u1} (Set.{u1} τ) (fun (v : Set.{u1} τ) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} τ) (Filter.{u1} τ) (Filter.hasMem.{u1} τ) v f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} τ) (Filter.{u1} τ) (Filter.hasMem.{u1} τ) v f) => HasSubset.Subset.{u3} (Set.{u3} β) (Set.hasSubset.{u3} β) (closure.{u3} β _inst_1 (Set.image2.{u1, u2, u3} τ α β ϕ v s)) c))) -> (forall {n : Set.{u3} β}, (IsOpen.{u3} β _inst_1 n) -> (HasSubset.Subset.{u3} (Set.{u3} β) (Set.hasSubset.{u3} β) (omegaLimit.{u1, u2, u3} τ α β _inst_1 f ϕ s) n) -> (Exists.{succ u1} (Set.{u1} τ) (fun (u : Set.{u1} τ) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} τ) (Filter.{u1} τ) (Filter.hasMem.{u1} τ) u f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} τ) (Filter.{u1} τ) (Filter.hasMem.{u1} τ) u f) => HasSubset.Subset.{u3} (Set.{u3} β) (Set.hasSubset.{u3} β) (closure.{u3} β _inst_1 (Set.image2.{u1, u2, u3} τ α β ϕ u s)) n))))
but is expected to have type
  forall {τ : Type.{u2}} {α : Type.{u1}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u2} τ) (ϕ : τ -> α -> β) (s : Set.{u1} α) {c : Set.{u3} β}, (IsCompact.{u3} β _inst_1 c) -> (Exists.{succ u2} (Set.{u2} τ) (fun (v : Set.{u2} τ) => And (Membership.mem.{u2, u2} (Set.{u2} τ) (Filter.{u2} τ) (instMembershipSetFilter.{u2} τ) v f) (HasSubset.Subset.{u3} (Set.{u3} β) (Set.instHasSubsetSet.{u3} β) (closure.{u3} β _inst_1 (Set.image2.{u2, u1, u3} τ α β ϕ v s)) c))) -> (forall {n : Set.{u3} β}, (IsOpen.{u3} β _inst_1 n) -> (HasSubset.Subset.{u3} (Set.{u3} β) (Set.instHasSubsetSet.{u3} β) (omegaLimit.{u2, u1, u3} τ α β _inst_1 f ϕ s) n) -> (Exists.{succ u2} (Set.{u2} τ) (fun (u : Set.{u2} τ) => And (Membership.mem.{u2, u2} (Set.{u2} τ) (Filter.{u2} τ) (instMembershipSetFilter.{u2} τ) u f) (HasSubset.Subset.{u3} (Set.{u3} β) (Set.instHasSubsetSet.{u3} β) (closure.{u3} β _inst_1 (Set.image2.{u2, u1, u3} τ α β ϕ u s)) n))))
Case conversion may be inaccurate. Consider using '#align eventually_closure_subset_of_is_compact_absorbing_of_is_open_of_omega_limit_subset' eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset'ₓ'. -/
/-- A set is eventually carried into any open neighbourhood of its ω-limit:
if `c` is a compact set such that `closure {ϕ t x | t ∈ v, x ∈ s} ⊆ c` for some `v ∈ f`
and `n` is an open neighbourhood of `ω f ϕ s`, then for some `u ∈ f` we have
`closure {ϕ t x | t ∈ u, x ∈ s} ⊆ n`. -/
theorem eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset' {c : Set β}
    (hc₁ : IsCompact c) (hc₂ : ∃ v ∈ f, closure (image2 ϕ v s) ⊆ c) {n : Set β} (hn₁ : IsOpen n)
    (hn₂ : ω f ϕ s ⊆ n) : ∃ u ∈ f, closure (image2 ϕ u s) ⊆ n :=
  by
  rcases hc₂ with ⟨v, hv₁, hv₂⟩
  let k := closure (image2 ϕ v s)
  have hk : IsCompact (k \ n) :=
    IsCompact.diff (isCompact_of_isClosed_subset hc₁ isClosed_closure hv₂) hn₁
  let j u := closure (image2 ϕ (u ∩ v) s)ᶜ
  have hj₁ : ∀ u ∈ f, IsOpen (j u) := fun _ _ => is_open_compl_iff.mpr isClosed_closure
  have hj₂ : k \ n ⊆ ⋃ u ∈ f, j u :=
    by
    have : (⋃ u ∈ f, j u) = ⋃ u : ↥f.sets, j u := bUnion_eq_Union _ _
    rw [this, diff_subset_comm, diff_Union]
    rw [omegaLimit_eq_interᵢ_inter _ _ _ hv₁] at hn₂
    simp_rw [diff_compl]
    rw [← inter_Inter]
    exact subset.trans (inter_subset_right _ _) hn₂
  rcases hk.elim_finite_subcover_image hj₁ hj₂ with ⟨g, hg₁ : ∀ u ∈ g, u ∈ f, hg₂, hg₃⟩
  let w := (⋂ u ∈ g, u) ∩ v
  have hw₂ : w ∈ f := by simpa [*]
  have hw₃ : k \ n ⊆ closure (image2 ϕ w s)ᶜ :=
    calc
      k \ n ⊆ ⋃ u ∈ g, j u := hg₃
      _ ⊆ closure (image2 ϕ w s)ᶜ :=
        by
        simp only [Union_subset_iff, compl_subset_compl]
        intro u hu
        mono* using w
        exact Inter_subset_of_subset u (Inter_subset_of_subset hu subset.rfl)
      
  have hw₄ : kᶜ ⊆ closure (image2 ϕ w s)ᶜ :=
    by
    rw [compl_subset_compl]
    calc
      closure (image2 ϕ w s) ⊆ _ := closure_mono (image2_subset (inter_subset_right _ _) subset.rfl)
      
  have hnc : nᶜ ⊆ k \ n ∪ kᶜ := by rw [union_comm, ← inter_subset, diff_eq, inter_comm]
  have hw : closure (image2 ϕ w s) ⊆ n :=
    compl_subset_compl.mp (subset.trans hnc (union_subset hw₃ hw₄))
  exact ⟨_, hw₂, hw⟩
#align eventually_closure_subset_of_is_compact_absorbing_of_is_open_of_omega_limit_subset' eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset'

/- warning: eventually_closure_subset_of_is_compact_absorbing_of_is_open_of_omega_limit_subset -> eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u1} τ) (ϕ : τ -> α -> β) (s : Set.{u2} α) [_inst_2 : T2Space.{u3} β _inst_1] {c : Set.{u3} β}, (IsCompact.{u3} β _inst_1 c) -> (Filter.Eventually.{u1} τ (fun (t : τ) => Set.MapsTo.{u2, u3} α β (ϕ t) s c) f) -> (forall {n : Set.{u3} β}, (IsOpen.{u3} β _inst_1 n) -> (HasSubset.Subset.{u3} (Set.{u3} β) (Set.hasSubset.{u3} β) (omegaLimit.{u1, u2, u3} τ α β _inst_1 f ϕ s) n) -> (Exists.{succ u1} (Set.{u1} τ) (fun (u : Set.{u1} τ) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} τ) (Filter.{u1} τ) (Filter.hasMem.{u1} τ) u f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} τ) (Filter.{u1} τ) (Filter.hasMem.{u1} τ) u f) => HasSubset.Subset.{u3} (Set.{u3} β) (Set.hasSubset.{u3} β) (closure.{u3} β _inst_1 (Set.image2.{u1, u2, u3} τ α β ϕ u s)) n))))
but is expected to have type
  forall {τ : Type.{u2}} {α : Type.{u1}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u2} τ) (ϕ : τ -> α -> β) (s : Set.{u1} α) [_inst_2 : T2Space.{u3} β _inst_1] {c : Set.{u3} β}, (IsCompact.{u3} β _inst_1 c) -> (Filter.Eventually.{u2} τ (fun (t : τ) => Set.MapsTo.{u1, u3} α β (ϕ t) s c) f) -> (forall {n : Set.{u3} β}, (IsOpen.{u3} β _inst_1 n) -> (HasSubset.Subset.{u3} (Set.{u3} β) (Set.instHasSubsetSet.{u3} β) (omegaLimit.{u2, u1, u3} τ α β _inst_1 f ϕ s) n) -> (Exists.{succ u2} (Set.{u2} τ) (fun (u : Set.{u2} τ) => And (Membership.mem.{u2, u2} (Set.{u2} τ) (Filter.{u2} τ) (instMembershipSetFilter.{u2} τ) u f) (HasSubset.Subset.{u3} (Set.{u3} β) (Set.instHasSubsetSet.{u3} β) (closure.{u3} β _inst_1 (Set.image2.{u2, u1, u3} τ α β ϕ u s)) n))))
Case conversion may be inaccurate. Consider using '#align eventually_closure_subset_of_is_compact_absorbing_of_is_open_of_omega_limit_subset eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subsetₓ'. -/
/-- A set is eventually carried into any open neighbourhood of its ω-limit:
if `c` is a compact set such that `closure {ϕ t x | t ∈ v, x ∈ s} ⊆ c` for some `v ∈ f`
and `n` is an open neighbourhood of `ω f ϕ s`, then for some `u ∈ f` we have
`closure {ϕ t x | t ∈ u, x ∈ s} ⊆ n`. -/
theorem eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset [T2Space β]
    {c : Set β} (hc₁ : IsCompact c) (hc₂ : ∀ᶠ t in f, MapsTo (ϕ t) s c) {n : Set β} (hn₁ : IsOpen n)
    (hn₂ : ω f ϕ s ⊆ n) : ∃ u ∈ f, closure (image2 ϕ u s) ⊆ n :=
  eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset' f ϕ _ hc₁
    ⟨_, hc₂, closure_minimal (image2_subset_iff.2 fun t => id) hc₁.IsClosed⟩ hn₁ hn₂
#align eventually_closure_subset_of_is_compact_absorbing_of_is_open_of_omega_limit_subset eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset

/- warning: eventually_maps_to_of_is_compact_absorbing_of_is_open_of_omega_limit_subset -> eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u1} τ) (ϕ : τ -> α -> β) (s : Set.{u2} α) [_inst_2 : T2Space.{u3} β _inst_1] {c : Set.{u3} β}, (IsCompact.{u3} β _inst_1 c) -> (Filter.Eventually.{u1} τ (fun (t : τ) => Set.MapsTo.{u2, u3} α β (ϕ t) s c) f) -> (forall {n : Set.{u3} β}, (IsOpen.{u3} β _inst_1 n) -> (HasSubset.Subset.{u3} (Set.{u3} β) (Set.hasSubset.{u3} β) (omegaLimit.{u1, u2, u3} τ α β _inst_1 f ϕ s) n) -> (Filter.Eventually.{u1} τ (fun (t : τ) => Set.MapsTo.{u2, u3} α β (ϕ t) s n) f))
but is expected to have type
  forall {τ : Type.{u2}} {α : Type.{u1}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u2} τ) (ϕ : τ -> α -> β) (s : Set.{u1} α) [_inst_2 : T2Space.{u3} β _inst_1] {c : Set.{u3} β}, (IsCompact.{u3} β _inst_1 c) -> (Filter.Eventually.{u2} τ (fun (t : τ) => Set.MapsTo.{u1, u3} α β (ϕ t) s c) f) -> (forall {n : Set.{u3} β}, (IsOpen.{u3} β _inst_1 n) -> (HasSubset.Subset.{u3} (Set.{u3} β) (Set.instHasSubsetSet.{u3} β) (omegaLimit.{u2, u1, u3} τ α β _inst_1 f ϕ s) n) -> (Filter.Eventually.{u2} τ (fun (t : τ) => Set.MapsTo.{u1, u3} α β (ϕ t) s n) f))
Case conversion may be inaccurate. Consider using '#align eventually_maps_to_of_is_compact_absorbing_of_is_open_of_omega_limit_subset eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subsetₓ'. -/
theorem eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset [T2Space β]
    {c : Set β} (hc₁ : IsCompact c) (hc₂ : ∀ᶠ t in f, MapsTo (ϕ t) s c) {n : Set β} (hn₁ : IsOpen n)
    (hn₂ : ω f ϕ s ⊆ n) : ∀ᶠ t in f, MapsTo (ϕ t) s n :=
  by
  rcases eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset f ϕ s hc₁
      hc₂ hn₁ hn₂ with
    ⟨u, hu_mem, hu⟩
  refine' mem_of_superset hu_mem fun t ht x hx => _
  exact hu (subset_closure <| mem_image2_of_mem ht hx)
#align eventually_maps_to_of_is_compact_absorbing_of_is_open_of_omega_limit_subset eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset

/- warning: eventually_closure_subset_of_is_open_of_omega_limit_subset -> eventually_closure_subset_of_isOpen_of_omegaLimit_subset is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u1} τ) (ϕ : τ -> α -> β) (s : Set.{u2} α) [_inst_2 : CompactSpace.{u3} β _inst_1] {v : Set.{u3} β}, (IsOpen.{u3} β _inst_1 v) -> (HasSubset.Subset.{u3} (Set.{u3} β) (Set.hasSubset.{u3} β) (omegaLimit.{u1, u2, u3} τ α β _inst_1 f ϕ s) v) -> (Exists.{succ u1} (Set.{u1} τ) (fun (u : Set.{u1} τ) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} τ) (Filter.{u1} τ) (Filter.hasMem.{u1} τ) u f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} τ) (Filter.{u1} τ) (Filter.hasMem.{u1} τ) u f) => HasSubset.Subset.{u3} (Set.{u3} β) (Set.hasSubset.{u3} β) (closure.{u3} β _inst_1 (Set.image2.{u1, u2, u3} τ α β ϕ u s)) v)))
but is expected to have type
  forall {τ : Type.{u2}} {α : Type.{u1}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u2} τ) (ϕ : τ -> α -> β) (s : Set.{u1} α) [_inst_2 : CompactSpace.{u3} β _inst_1] {v : Set.{u3} β}, (IsOpen.{u3} β _inst_1 v) -> (HasSubset.Subset.{u3} (Set.{u3} β) (Set.instHasSubsetSet.{u3} β) (omegaLimit.{u2, u1, u3} τ α β _inst_1 f ϕ s) v) -> (Exists.{succ u2} (Set.{u2} τ) (fun (u : Set.{u2} τ) => And (Membership.mem.{u2, u2} (Set.{u2} τ) (Filter.{u2} τ) (instMembershipSetFilter.{u2} τ) u f) (HasSubset.Subset.{u3} (Set.{u3} β) (Set.instHasSubsetSet.{u3} β) (closure.{u3} β _inst_1 (Set.image2.{u2, u1, u3} τ α β ϕ u s)) v)))
Case conversion may be inaccurate. Consider using '#align eventually_closure_subset_of_is_open_of_omega_limit_subset eventually_closure_subset_of_isOpen_of_omegaLimit_subsetₓ'. -/
theorem eventually_closure_subset_of_isOpen_of_omegaLimit_subset [CompactSpace β] {v : Set β}
    (hv₁ : IsOpen v) (hv₂ : ω f ϕ s ⊆ v) : ∃ u ∈ f, closure (image2 ϕ u s) ⊆ v :=
  eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset' _ _ _
    isCompact_univ ⟨univ, univ_mem, subset_univ _⟩ hv₁ hv₂
#align eventually_closure_subset_of_is_open_of_omega_limit_subset eventually_closure_subset_of_isOpen_of_omegaLimit_subset

/- warning: eventually_maps_to_of_is_open_of_omega_limit_subset -> eventually_mapsTo_of_isOpen_of_omegaLimit_subset is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u1} τ) (ϕ : τ -> α -> β) (s : Set.{u2} α) [_inst_2 : CompactSpace.{u3} β _inst_1] {v : Set.{u3} β}, (IsOpen.{u3} β _inst_1 v) -> (HasSubset.Subset.{u3} (Set.{u3} β) (Set.hasSubset.{u3} β) (omegaLimit.{u1, u2, u3} τ α β _inst_1 f ϕ s) v) -> (Filter.Eventually.{u1} τ (fun (t : τ) => Set.MapsTo.{u2, u3} α β (ϕ t) s v) f)
but is expected to have type
  forall {τ : Type.{u2}} {α : Type.{u1}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u2} τ) (ϕ : τ -> α -> β) (s : Set.{u1} α) [_inst_2 : CompactSpace.{u3} β _inst_1] {v : Set.{u3} β}, (IsOpen.{u3} β _inst_1 v) -> (HasSubset.Subset.{u3} (Set.{u3} β) (Set.instHasSubsetSet.{u3} β) (omegaLimit.{u2, u1, u3} τ α β _inst_1 f ϕ s) v) -> (Filter.Eventually.{u2} τ (fun (t : τ) => Set.MapsTo.{u1, u3} α β (ϕ t) s v) f)
Case conversion may be inaccurate. Consider using '#align eventually_maps_to_of_is_open_of_omega_limit_subset eventually_mapsTo_of_isOpen_of_omegaLimit_subsetₓ'. -/
theorem eventually_mapsTo_of_isOpen_of_omegaLimit_subset [CompactSpace β] {v : Set β}
    (hv₁ : IsOpen v) (hv₂ : ω f ϕ s ⊆ v) : ∀ᶠ t in f, MapsTo (ϕ t) s v :=
  by
  rcases eventually_closure_subset_of_isOpen_of_omegaLimit_subset f ϕ s hv₁ hv₂ with ⟨u, hu_mem, hu⟩
  refine' mem_of_superset hu_mem fun t ht x hx => _
  exact hu (subset_closure <| mem_image2_of_mem ht hx)
#align eventually_maps_to_of_is_open_of_omega_limit_subset eventually_mapsTo_of_isOpen_of_omegaLimit_subset

/- warning: nonempty_omega_limit_of_is_compact_absorbing -> nonempty_omegaLimit_of_isCompact_absorbing is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u1} τ) (ϕ : τ -> α -> β) (s : Set.{u2} α) [_inst_2 : Filter.NeBot.{u1} τ f] {c : Set.{u3} β}, (IsCompact.{u3} β _inst_1 c) -> (Exists.{succ u1} (Set.{u1} τ) (fun (v : Set.{u1} τ) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} τ) (Filter.{u1} τ) (Filter.hasMem.{u1} τ) v f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} τ) (Filter.{u1} τ) (Filter.hasMem.{u1} τ) v f) => HasSubset.Subset.{u3} (Set.{u3} β) (Set.hasSubset.{u3} β) (closure.{u3} β _inst_1 (Set.image2.{u1, u2, u3} τ α β ϕ v s)) c))) -> (Set.Nonempty.{u2} α s) -> (Set.Nonempty.{u3} β (omegaLimit.{u1, u2, u3} τ α β _inst_1 f ϕ s))
but is expected to have type
  forall {τ : Type.{u3}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} β] (f : Filter.{u3} τ) (ϕ : τ -> α -> β) (s : Set.{u1} α) [_inst_2 : Filter.NeBot.{u3} τ f] {c : Set.{u2} β}, (IsCompact.{u2} β _inst_1 c) -> (Exists.{succ u3} (Set.{u3} τ) (fun (v : Set.{u3} τ) => And (Membership.mem.{u3, u3} (Set.{u3} τ) (Filter.{u3} τ) (instMembershipSetFilter.{u3} τ) v f) (HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) (closure.{u2} β _inst_1 (Set.image2.{u3, u1, u2} τ α β ϕ v s)) c))) -> (Set.Nonempty.{u1} α s) -> (Set.Nonempty.{u2} β (omegaLimit.{u3, u1, u2} τ α β _inst_1 f ϕ s))
Case conversion may be inaccurate. Consider using '#align nonempty_omega_limit_of_is_compact_absorbing nonempty_omegaLimit_of_isCompact_absorbingₓ'. -/
/-- The ω-limit of a nonempty set w.r.t. a nontrivial filter is nonempty. -/
theorem nonempty_omegaLimit_of_isCompact_absorbing [NeBot f] {c : Set β} (hc₁ : IsCompact c)
    (hc₂ : ∃ v ∈ f, closure (image2 ϕ v s) ⊆ c) (hs : s.Nonempty) : (ω f ϕ s).Nonempty :=
  by
  rcases hc₂ with ⟨v, hv₁, hv₂⟩
  rw [omegaLimit_eq_interᵢ_inter _ _ _ hv₁]
  apply IsCompact.nonempty_interᵢ_of_directed_nonempty_compact_closed
  · rintro ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩
    use ⟨u₁ ∩ u₂, inter_mem hu₁ hu₂⟩
    constructor
    all_goals exact closure_mono (image2_subset (inter_subset_inter_left _ (by simp)) subset.rfl)
  · intro u
    have hn : (image2 ϕ (u ∩ v) s).Nonempty :=
      nonempty.image2 (nonempty_of_mem (inter_mem u.prop hv₁)) hs
    exact hn.mono subset_closure
  · intro
    apply isCompact_of_isClosed_subset hc₁ isClosed_closure
    calc
      _ ⊆ closure (image2 ϕ v s) := closure_mono (image2_subset (inter_subset_right _ _) subset.rfl)
      _ ⊆ c := hv₂
      
  · exact fun _ => isClosed_closure
#align nonempty_omega_limit_of_is_compact_absorbing nonempty_omegaLimit_of_isCompact_absorbing

/- warning: nonempty_omega_limit -> nonempty_omegaLimit is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u1} τ) (ϕ : τ -> α -> β) (s : Set.{u2} α) [_inst_2 : CompactSpace.{u3} β _inst_1] [_inst_3 : Filter.NeBot.{u1} τ f], (Set.Nonempty.{u2} α s) -> (Set.Nonempty.{u3} β (omegaLimit.{u1, u2, u3} τ α β _inst_1 f ϕ s))
but is expected to have type
  forall {τ : Type.{u2}} {α : Type.{u1}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} β] (f : Filter.{u2} τ) (ϕ : τ -> α -> β) (s : Set.{u1} α) [_inst_2 : CompactSpace.{u3} β _inst_1] [_inst_3 : Filter.NeBot.{u2} τ f], (Set.Nonempty.{u1} α s) -> (Set.Nonempty.{u3} β (omegaLimit.{u2, u1, u3} τ α β _inst_1 f ϕ s))
Case conversion may be inaccurate. Consider using '#align nonempty_omega_limit nonempty_omegaLimitₓ'. -/
theorem nonempty_omegaLimit [CompactSpace β] [NeBot f] (hs : s.Nonempty) : (ω f ϕ s).Nonempty :=
  nonempty_omegaLimit_of_isCompact_absorbing _ _ _ isCompact_univ ⟨univ, univ_mem, subset_univ _⟩ hs
#align nonempty_omega_limit nonempty_omegaLimit

end omegaLimit

/-!
### ω-limits of Flows by a Monoid
-/


namespace Flow

variable {τ : Type _} [TopologicalSpace τ] [AddMonoid τ] [ContinuousAdd τ] {α : Type _}
  [TopologicalSpace α] (f : Filter τ) (ϕ : Flow τ α) (s : Set α)

open omegaLimit

/- warning: flow.is_invariant_omega_limit -> Flow.isInvariant_omegaLimit is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} τ] [_inst_2 : AddMonoid.{u1} τ] [_inst_3 : ContinuousAdd.{u1} τ _inst_1 (AddZeroClass.toHasAdd.{u1} τ (AddMonoid.toAddZeroClass.{u1} τ _inst_2))] {α : Type.{u2}} [_inst_4 : TopologicalSpace.{u2} α] (f : Filter.{u1} τ) (ϕ : Flow.{u1, u2} τ _inst_1 _inst_2 _inst_3 α _inst_4) (s : Set.{u2} α), (forall (t : τ), Filter.Tendsto.{u1, u1} τ τ (HAdd.hAdd.{u1, u1, u1} τ τ τ (instHAdd.{u1} τ (AddZeroClass.toHasAdd.{u1} τ (AddMonoid.toAddZeroClass.{u1} τ _inst_2))) t) f f) -> (IsInvariant.{u1, u2} τ α (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Flow.{u1, u2} τ _inst_1 _inst_2 _inst_3 α _inst_4) (fun (_x : Flow.{u1, u2} τ _inst_1 _inst_2 _inst_3 α _inst_4) => τ -> α -> α) (Flow.hasCoeToFun.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) ϕ) (omegaLimit.{u1, u2, u2} τ α α _inst_4 f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Flow.{u1, u2} τ _inst_1 _inst_2 _inst_3 α _inst_4) (fun (_x : Flow.{u1, u2} τ _inst_1 _inst_2 _inst_3 α _inst_4) => τ -> α -> α) (Flow.hasCoeToFun.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) ϕ) s))
but is expected to have type
  forall {τ : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} τ] [_inst_2 : AddMonoid.{u2} τ] [_inst_3 : ContinuousAdd.{u2} τ _inst_1 (AddZeroClass.toAdd.{u2} τ (AddMonoid.toAddZeroClass.{u2} τ _inst_2))] {α : Type.{u1}} [_inst_4 : TopologicalSpace.{u1} α] (f : Filter.{u2} τ) (ϕ : Flow.{u2, u1} τ _inst_1 _inst_2 _inst_3 α _inst_4) (s : Set.{u1} α), (forall (t : τ), Filter.Tendsto.{u2, u2} τ τ ((fun (x._@.Mathlib.Dynamics.OmegaLimit._hyg.5367 : τ) (x._@.Mathlib.Dynamics.OmegaLimit._hyg.5369 : τ) => HAdd.hAdd.{u2, u2, u2} τ τ τ (instHAdd.{u2} τ (AddZeroClass.toAdd.{u2} τ (AddMonoid.toAddZeroClass.{u2} τ _inst_2))) x._@.Mathlib.Dynamics.OmegaLimit._hyg.5367 x._@.Mathlib.Dynamics.OmegaLimit._hyg.5369) t) f f) -> (IsInvariant.{u2, u1} τ α (Flow.toFun.{u2, u1} τ _inst_1 _inst_2 _inst_3 α _inst_4 ϕ) (omegaLimit.{u2, u1, u1} τ α α _inst_4 f (Flow.toFun.{u2, u1} τ _inst_1 _inst_2 _inst_3 α _inst_4 ϕ) s))
Case conversion may be inaccurate. Consider using '#align flow.is_invariant_omega_limit Flow.isInvariant_omegaLimitₓ'. -/
theorem isInvariant_omegaLimit (hf : ∀ t, Tendsto ((· + ·) t) f f) : IsInvariant ϕ (ω f ϕ s) :=
  by
  refine' fun t => maps_to.mono_right _ (omegaLimit_subset_of_tendsto ϕ s (hf t))
  exact
    mapsTo_omegaLimit _ (maps_to_id _) (fun t' x => (ϕ.map_add _ _ _).symm)
      (continuous_const.flow ϕ continuous_id)
#align flow.is_invariant_omega_limit Flow.isInvariant_omegaLimit

/- warning: flow.omega_limit_image_subset -> Flow.omegaLimit_image_subset is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} τ] [_inst_2 : AddMonoid.{u1} τ] [_inst_3 : ContinuousAdd.{u1} τ _inst_1 (AddZeroClass.toHasAdd.{u1} τ (AddMonoid.toAddZeroClass.{u1} τ _inst_2))] {α : Type.{u2}} [_inst_4 : TopologicalSpace.{u2} α] (f : Filter.{u1} τ) (ϕ : Flow.{u1, u2} τ _inst_1 _inst_2 _inst_3 α _inst_4) (s : Set.{u2} α) (t : τ), (Filter.Tendsto.{u1, u1} τ τ (fun (_x : τ) => HAdd.hAdd.{u1, u1, u1} τ τ τ (instHAdd.{u1} τ (AddZeroClass.toHasAdd.{u1} τ (AddMonoid.toAddZeroClass.{u1} τ _inst_2))) _x t) f f) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.hasSubset.{u2} α) (omegaLimit.{u1, u2, u2} τ α α _inst_4 f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Flow.{u1, u2} τ _inst_1 _inst_2 _inst_3 α _inst_4) (fun (_x : Flow.{u1, u2} τ _inst_1 _inst_2 _inst_3 α _inst_4) => τ -> α -> α) (Flow.hasCoeToFun.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) ϕ) (Set.image.{u2, u2} α α (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Flow.{u1, u2} τ _inst_1 _inst_2 _inst_3 α _inst_4) (fun (_x : Flow.{u1, u2} τ _inst_1 _inst_2 _inst_3 α _inst_4) => τ -> α -> α) (Flow.hasCoeToFun.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) ϕ t) s)) (omegaLimit.{u1, u2, u2} τ α α _inst_4 f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Flow.{u1, u2} τ _inst_1 _inst_2 _inst_3 α _inst_4) (fun (_x : Flow.{u1, u2} τ _inst_1 _inst_2 _inst_3 α _inst_4) => τ -> α -> α) (Flow.hasCoeToFun.{u1, u2} τ _inst_2 _inst_1 _inst_3 α _inst_4) ϕ) s))
but is expected to have type
  forall {τ : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} τ] [_inst_2 : AddMonoid.{u2} τ] [_inst_3 : ContinuousAdd.{u2} τ _inst_1 (AddZeroClass.toAdd.{u2} τ (AddMonoid.toAddZeroClass.{u2} τ _inst_2))] {α : Type.{u1}} [_inst_4 : TopologicalSpace.{u1} α] (f : Filter.{u2} τ) (ϕ : Flow.{u2, u1} τ _inst_1 _inst_2 _inst_3 α _inst_4) (s : Set.{u1} α) (t : τ), (Filter.Tendsto.{u2, u2} τ τ (fun (_x : τ) => HAdd.hAdd.{u2, u2, u2} τ τ τ (instHAdd.{u2} τ (AddZeroClass.toAdd.{u2} τ (AddMonoid.toAddZeroClass.{u2} τ _inst_2))) _x t) f f) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (omegaLimit.{u2, u1, u1} τ α α _inst_4 f (Flow.toFun.{u2, u1} τ _inst_1 _inst_2 _inst_3 α _inst_4 ϕ) (Set.image.{u1, u1} α α (Flow.toFun.{u2, u1} τ _inst_1 _inst_2 _inst_3 α _inst_4 ϕ t) s)) (omegaLimit.{u2, u1, u1} τ α α _inst_4 f (Flow.toFun.{u2, u1} τ _inst_1 _inst_2 _inst_3 α _inst_4 ϕ) s))
Case conversion may be inaccurate. Consider using '#align flow.omega_limit_image_subset Flow.omegaLimit_image_subsetₓ'. -/
theorem omegaLimit_image_subset (t : τ) (ht : Tendsto (· + t) f f) : ω f ϕ (ϕ t '' s) ⊆ ω f ϕ s :=
  by
  simp only [omegaLimit_image_eq, ← map_add]
  exact omegaLimit_subset_of_tendsto ϕ s ht
#align flow.omega_limit_image_subset Flow.omegaLimit_image_subset

end Flow

/-!
### ω-limits of Flows by a Group
-/


namespace Flow

variable {τ : Type _} [TopologicalSpace τ] [AddCommGroup τ] [TopologicalAddGroup τ] {α : Type _}
  [TopologicalSpace α] (f : Filter τ) (ϕ : Flow τ α) (s : Set α)

open omegaLimit

/- warning: flow.omega_limit_image_eq -> Flow.omegaLimit_image_eq is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} τ] [_inst_2 : AddCommGroup.{u1} τ] [_inst_3 : TopologicalAddGroup.{u1} τ _inst_1 (AddCommGroup.toAddGroup.{u1} τ _inst_2)] {α : Type.{u2}} [_inst_4 : TopologicalSpace.{u2} α] (f : Filter.{u1} τ) (ϕ : Flow.{u1, u2} τ _inst_1 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_2))) (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_1 (AddCommGroup.toAddGroup.{u1} τ _inst_2) _inst_3) α _inst_4) (s : Set.{u2} α), (forall (t : τ), Filter.Tendsto.{u1, u1} τ τ (fun (_x : τ) => HAdd.hAdd.{u1, u1, u1} τ τ τ (instHAdd.{u1} τ (AddZeroClass.toHasAdd.{u1} τ (AddMonoid.toAddZeroClass.{u1} τ (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_2)))))) _x t) f f) -> (forall (t : τ), Eq.{succ u2} (Set.{u2} α) (omegaLimit.{u1, u2, u2} τ α α _inst_4 f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Flow.{u1, u2} τ _inst_1 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_2))) (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_1 (AddCommGroup.toAddGroup.{u1} τ _inst_2) _inst_3) α _inst_4) (fun (_x : Flow.{u1, u2} τ _inst_1 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_2))) (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_1 (AddCommGroup.toAddGroup.{u1} τ _inst_2) _inst_3) α _inst_4) => τ -> α -> α) (Flow.hasCoeToFun.{u1, u2} τ (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_2))) _inst_1 (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_1 (AddCommGroup.toAddGroup.{u1} τ _inst_2) _inst_3) α _inst_4) ϕ) (Set.image.{u2, u2} α α (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Flow.{u1, u2} τ _inst_1 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_2))) (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_1 (AddCommGroup.toAddGroup.{u1} τ _inst_2) _inst_3) α _inst_4) (fun (_x : Flow.{u1, u2} τ _inst_1 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_2))) (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_1 (AddCommGroup.toAddGroup.{u1} τ _inst_2) _inst_3) α _inst_4) => τ -> α -> α) (Flow.hasCoeToFun.{u1, u2} τ (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_2))) _inst_1 (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_1 (AddCommGroup.toAddGroup.{u1} τ _inst_2) _inst_3) α _inst_4) ϕ t) s)) (omegaLimit.{u1, u2, u2} τ α α _inst_4 f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Flow.{u1, u2} τ _inst_1 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_2))) (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_1 (AddCommGroup.toAddGroup.{u1} τ _inst_2) _inst_3) α _inst_4) (fun (_x : Flow.{u1, u2} τ _inst_1 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_2))) (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_1 (AddCommGroup.toAddGroup.{u1} τ _inst_2) _inst_3) α _inst_4) => τ -> α -> α) (Flow.hasCoeToFun.{u1, u2} τ (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_2))) _inst_1 (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_1 (AddCommGroup.toAddGroup.{u1} τ _inst_2) _inst_3) α _inst_4) ϕ) s))
but is expected to have type
  forall {τ : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} τ] [_inst_2 : AddCommGroup.{u2} τ] [_inst_3 : TopologicalAddGroup.{u2} τ _inst_1 (AddCommGroup.toAddGroup.{u2} τ _inst_2)] {α : Type.{u1}} [_inst_4 : TopologicalSpace.{u1} α] (f : Filter.{u2} τ) (ϕ : Flow.{u2, u1} τ _inst_1 (SubNegMonoid.toAddMonoid.{u2} τ (AddGroup.toSubNegMonoid.{u2} τ (AddCommGroup.toAddGroup.{u2} τ _inst_2))) (TopologicalAddGroup.toContinuousAdd.{u2} τ _inst_1 (AddCommGroup.toAddGroup.{u2} τ _inst_2) _inst_3) α _inst_4) (s : Set.{u1} α), (forall (t : τ), Filter.Tendsto.{u2, u2} τ τ (fun (_x : τ) => HAdd.hAdd.{u2, u2, u2} τ τ τ (instHAdd.{u2} τ (AddZeroClass.toAdd.{u2} τ (AddMonoid.toAddZeroClass.{u2} τ (SubNegMonoid.toAddMonoid.{u2} τ (AddGroup.toSubNegMonoid.{u2} τ (AddCommGroup.toAddGroup.{u2} τ _inst_2)))))) _x t) f f) -> (forall (t : τ), Eq.{succ u1} (Set.{u1} α) (omegaLimit.{u2, u1, u1} τ α α _inst_4 f (Flow.toFun.{u2, u1} τ _inst_1 (SubNegMonoid.toAddMonoid.{u2} τ (AddGroup.toSubNegMonoid.{u2} τ (AddCommGroup.toAddGroup.{u2} τ _inst_2))) (TopologicalAddGroup.toContinuousAdd.{u2} τ _inst_1 (AddCommGroup.toAddGroup.{u2} τ _inst_2) _inst_3) α _inst_4 ϕ) (Set.image.{u1, u1} α α (Flow.toFun.{u2, u1} τ _inst_1 (SubNegMonoid.toAddMonoid.{u2} τ (AddGroup.toSubNegMonoid.{u2} τ (AddCommGroup.toAddGroup.{u2} τ _inst_2))) (TopologicalAddGroup.toContinuousAdd.{u2} τ _inst_1 (AddCommGroup.toAddGroup.{u2} τ _inst_2) _inst_3) α _inst_4 ϕ t) s)) (omegaLimit.{u2, u1, u1} τ α α _inst_4 f (Flow.toFun.{u2, u1} τ _inst_1 (SubNegMonoid.toAddMonoid.{u2} τ (AddGroup.toSubNegMonoid.{u2} τ (AddCommGroup.toAddGroup.{u2} τ _inst_2))) (TopologicalAddGroup.toContinuousAdd.{u2} τ _inst_1 (AddCommGroup.toAddGroup.{u2} τ _inst_2) _inst_3) α _inst_4 ϕ) s))
Case conversion may be inaccurate. Consider using '#align flow.omega_limit_image_eq Flow.omegaLimit_image_eqₓ'. -/
/-- the ω-limit of a forward image of `s` is the same as the ω-limit of `s`. -/
@[simp]
theorem omegaLimit_image_eq (hf : ∀ t, Tendsto (· + t) f f) (t : τ) : ω f ϕ (ϕ t '' s) = ω f ϕ s :=
  Subset.antisymm (omegaLimit_image_subset _ _ _ _ (hf t)) <|
    calc
      ω f ϕ s = ω f ϕ (ϕ (-t) '' (ϕ t '' s)) := by simp [image_image, ← map_add]
      _ ⊆ ω f ϕ (ϕ t '' s) := omegaLimit_image_subset _ _ _ _ (hf _)
      
#align flow.omega_limit_image_eq Flow.omegaLimit_image_eq

/- warning: flow.omega_limit_omega_limit -> Flow.omegaLimit_omegaLimit is a dubious translation:
lean 3 declaration is
  forall {τ : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} τ] [_inst_2 : AddCommGroup.{u1} τ] [_inst_3 : TopologicalAddGroup.{u1} τ _inst_1 (AddCommGroup.toAddGroup.{u1} τ _inst_2)] {α : Type.{u2}} [_inst_4 : TopologicalSpace.{u2} α] (f : Filter.{u1} τ) (ϕ : Flow.{u1, u2} τ _inst_1 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_2))) (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_1 (AddCommGroup.toAddGroup.{u1} τ _inst_2) _inst_3) α _inst_4) (s : Set.{u2} α), (forall (t : τ), Filter.Tendsto.{u1, u1} τ τ (HAdd.hAdd.{u1, u1, u1} τ τ τ (instHAdd.{u1} τ (AddZeroClass.toHasAdd.{u1} τ (AddMonoid.toAddZeroClass.{u1} τ (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_2)))))) t) f f) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.hasSubset.{u2} α) (omegaLimit.{u1, u2, u2} τ α α _inst_4 f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Flow.{u1, u2} τ _inst_1 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_2))) (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_1 (AddCommGroup.toAddGroup.{u1} τ _inst_2) _inst_3) α _inst_4) (fun (_x : Flow.{u1, u2} τ _inst_1 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_2))) (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_1 (AddCommGroup.toAddGroup.{u1} τ _inst_2) _inst_3) α _inst_4) => τ -> α -> α) (Flow.hasCoeToFun.{u1, u2} τ (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_2))) _inst_1 (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_1 (AddCommGroup.toAddGroup.{u1} τ _inst_2) _inst_3) α _inst_4) ϕ) (omegaLimit.{u1, u2, u2} τ α α _inst_4 f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Flow.{u1, u2} τ _inst_1 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_2))) (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_1 (AddCommGroup.toAddGroup.{u1} τ _inst_2) _inst_3) α _inst_4) (fun (_x : Flow.{u1, u2} τ _inst_1 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_2))) (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_1 (AddCommGroup.toAddGroup.{u1} τ _inst_2) _inst_3) α _inst_4) => τ -> α -> α) (Flow.hasCoeToFun.{u1, u2} τ (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_2))) _inst_1 (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_1 (AddCommGroup.toAddGroup.{u1} τ _inst_2) _inst_3) α _inst_4) ϕ) s)) (omegaLimit.{u1, u2, u2} τ α α _inst_4 f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Flow.{u1, u2} τ _inst_1 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_2))) (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_1 (AddCommGroup.toAddGroup.{u1} τ _inst_2) _inst_3) α _inst_4) (fun (_x : Flow.{u1, u2} τ _inst_1 (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_2))) (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_1 (AddCommGroup.toAddGroup.{u1} τ _inst_2) _inst_3) α _inst_4) => τ -> α -> α) (Flow.hasCoeToFun.{u1, u2} τ (SubNegMonoid.toAddMonoid.{u1} τ (AddGroup.toSubNegMonoid.{u1} τ (AddCommGroup.toAddGroup.{u1} τ _inst_2))) _inst_1 (TopologicalAddGroup.to_continuousAdd.{u1} τ _inst_1 (AddCommGroup.toAddGroup.{u1} τ _inst_2) _inst_3) α _inst_4) ϕ) s))
but is expected to have type
  forall {τ : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} τ] [_inst_2 : AddCommGroup.{u2} τ] [_inst_3 : TopologicalAddGroup.{u2} τ _inst_1 (AddCommGroup.toAddGroup.{u2} τ _inst_2)] {α : Type.{u1}} [_inst_4 : TopologicalSpace.{u1} α] (f : Filter.{u2} τ) (ϕ : Flow.{u2, u1} τ _inst_1 (SubNegMonoid.toAddMonoid.{u2} τ (AddGroup.toSubNegMonoid.{u2} τ (AddCommGroup.toAddGroup.{u2} τ _inst_2))) (TopologicalAddGroup.toContinuousAdd.{u2} τ _inst_1 (AddCommGroup.toAddGroup.{u2} τ _inst_2) _inst_3) α _inst_4) (s : Set.{u1} α), (forall (t : τ), Filter.Tendsto.{u2, u2} τ τ ((fun (x._@.Mathlib.Dynamics.OmegaLimit._hyg.5733 : τ) (x._@.Mathlib.Dynamics.OmegaLimit._hyg.5735 : τ) => HAdd.hAdd.{u2, u2, u2} τ τ τ (instHAdd.{u2} τ (AddZeroClass.toAdd.{u2} τ (AddMonoid.toAddZeroClass.{u2} τ (SubNegMonoid.toAddMonoid.{u2} τ (AddGroup.toSubNegMonoid.{u2} τ (AddCommGroup.toAddGroup.{u2} τ _inst_2)))))) x._@.Mathlib.Dynamics.OmegaLimit._hyg.5733 x._@.Mathlib.Dynamics.OmegaLimit._hyg.5735) t) f f) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (omegaLimit.{u2, u1, u1} τ α α _inst_4 f (Flow.toFun.{u2, u1} τ _inst_1 (SubNegMonoid.toAddMonoid.{u2} τ (AddGroup.toSubNegMonoid.{u2} τ (AddCommGroup.toAddGroup.{u2} τ _inst_2))) (TopologicalAddGroup.toContinuousAdd.{u2} τ _inst_1 (AddCommGroup.toAddGroup.{u2} τ _inst_2) _inst_3) α _inst_4 ϕ) (omegaLimit.{u2, u1, u1} τ α α _inst_4 f (Flow.toFun.{u2, u1} τ _inst_1 (SubNegMonoid.toAddMonoid.{u2} τ (AddGroup.toSubNegMonoid.{u2} τ (AddCommGroup.toAddGroup.{u2} τ _inst_2))) (TopologicalAddGroup.toContinuousAdd.{u2} τ _inst_1 (AddCommGroup.toAddGroup.{u2} τ _inst_2) _inst_3) α _inst_4 ϕ) s)) (omegaLimit.{u2, u1, u1} τ α α _inst_4 f (Flow.toFun.{u2, u1} τ _inst_1 (SubNegMonoid.toAddMonoid.{u2} τ (AddGroup.toSubNegMonoid.{u2} τ (AddCommGroup.toAddGroup.{u2} τ _inst_2))) (TopologicalAddGroup.toContinuousAdd.{u2} τ _inst_1 (AddCommGroup.toAddGroup.{u2} τ _inst_2) _inst_3) α _inst_4 ϕ) s))
Case conversion may be inaccurate. Consider using '#align flow.omega_limit_omega_limit Flow.omegaLimit_omegaLimitₓ'. -/
theorem omegaLimit_omegaLimit (hf : ∀ t, Tendsto ((· + ·) t) f f) : ω f ϕ (ω f ϕ s) ⊆ ω f ϕ s :=
  by
  simp only [subset_def, mem_omegaLimit_iff_frequently₂, frequently_iff]
  intro _ h
  rintro n hn u hu
  rcases mem_nhds_iff.mp hn with ⟨o, ho₁, ho₂, ho₃⟩
  rcases h o (IsOpen.mem_nhds ho₂ ho₃) hu with ⟨t, ht₁, ht₂⟩
  have l₁ : (ω f ϕ s ∩ o).Nonempty :=
    ht₂.mono
      (inter_subset_inter_left _
        ((isInvariant_iff_image _ _).mp (is_invariant_omega_limit _ _ _ hf) _))
  have l₂ : (closure (image2 ϕ u s) ∩ o).Nonempty :=
    l₁.mono fun b hb => ⟨omegaLimit_subset_closure_fw_image _ _ _ hu hb.1, hb.2⟩
  have l₃ : (o ∩ image2 ϕ u s).Nonempty :=
    by
    rcases l₂ with ⟨b, hb₁, hb₂⟩
    exact mem_closure_iff_nhds.mp hb₁ o (IsOpen.mem_nhds ho₂ hb₂)
  rcases l₃ with ⟨ϕra, ho, ⟨_, _, hr, ha, hϕra⟩⟩
  exact ⟨_, hr, ϕra, ⟨_, ha, hϕra⟩, ho₁ ho⟩
#align flow.omega_limit_omega_limit Flow.omegaLimit_omegaLimit

end Flow

