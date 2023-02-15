/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton

! This file was ported from Lean 3 source module topology.compact_open
! leanprover-community/mathlib commit 369525b73f229ccd76a6ec0e0e0bf2be57599768
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Tidy
import Mathbin.Topology.ContinuousFunction.Basic
import Mathbin.Topology.Homeomorph
import Mathbin.Topology.SubsetProperties
import Mathbin.Topology.Maps

/-!
# The compact-open topology

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we define the compact-open topology on the set of continuous maps between two
topological spaces.

## Main definitions

* `compact_open` is the compact-open topology on `C(α, β)`. It is declared as an instance.
* `continuous_map.coev` is the coevaluation map `β → C(α, β × α)`. It is always continuous.
* `continuous_map.curry` is the currying map `C(α × β, γ) → C(α, C(β, γ))`. This map always exists
  and it is continuous as long as `α × β` is locally compact.
* `continuous_map.uncurry` is the uncurrying map `C(α, C(β, γ)) → C(α × β, γ)`. For this map to
  exist, we need `β` to be locally compact. If `α` is also locally compact, then this map is
  continuous.
* `homeomorph.curry` combines the currying and uncurrying operations into a homeomorphism
  `C(α × β, γ) ≃ₜ C(α, C(β, γ))`. This homeomorphism exists if `α` and `β` are locally compact.


## Tags

compact-open, curry, function space
-/


open Set

open Topology

namespace ContinuousMap

section CompactOpen

variable {α : Type _} {β : Type _} {γ : Type _}

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

#print ContinuousMap.CompactOpen.gen /-
/-- A generating set for the compact-open topology (when `s` is compact and `u` is open). -/
def CompactOpen.gen (s : Set α) (u : Set β) : Set C(α, β) :=
  { f | f '' s ⊆ u }
#align continuous_map.compact_open.gen ContinuousMap.CompactOpen.gen
-/

#print ContinuousMap.gen_empty /-
@[simp]
theorem gen_empty (u : Set β) : CompactOpen.gen (∅ : Set α) u = Set.univ :=
  Set.ext fun f => iff_true_intro ((congr_arg (· ⊆ u) (image_empty f)).mpr u.empty_subset)
#align continuous_map.gen_empty ContinuousMap.gen_empty
-/

/- warning: continuous_map.gen_univ -> ContinuousMap.gen_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (s : Set.{u1} α), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (ContinuousMap.CompactOpen.gen.{u1, u2} α β _inst_1 _inst_2 s (Set.univ.{u2} β)) (Set.univ.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (s : Set.{u2} α), Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (ContinuousMap.CompactOpen.gen.{u2, u1} α β _inst_1 _inst_2 s (Set.univ.{u1} β)) (Set.univ.{max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2))
Case conversion may be inaccurate. Consider using '#align continuous_map.gen_univ ContinuousMap.gen_univₓ'. -/
@[simp]
theorem gen_univ (s : Set α) : CompactOpen.gen s (Set.univ : Set β) = Set.univ :=
  Set.ext fun f => iff_true_intro (f '' s).subset_univ
#align continuous_map.gen_univ ContinuousMap.gen_univ

/- warning: continuous_map.gen_inter -> ContinuousMap.gen_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (s : Set.{u1} α) (u : Set.{u2} β) (v : Set.{u2} β), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (ContinuousMap.CompactOpen.gen.{u1, u2} α β _inst_1 _inst_2 s (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) u v)) (Inter.inter.{max u1 u2} (Set.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (Set.hasInter.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (ContinuousMap.CompactOpen.gen.{u1, u2} α β _inst_1 _inst_2 s u) (ContinuousMap.CompactOpen.gen.{u1, u2} α β _inst_1 _inst_2 s v))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (s : Set.{u2} α) (u : Set.{u1} β) (v : Set.{u1} β), Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (ContinuousMap.CompactOpen.gen.{u2, u1} α β _inst_1 _inst_2 s (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) u v)) (Inter.inter.{max u1 u2} (Set.{max u1 u2} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (Set.instInterSet.{max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (ContinuousMap.CompactOpen.gen.{u2, u1} α β _inst_1 _inst_2 s u) (ContinuousMap.CompactOpen.gen.{u2, u1} α β _inst_1 _inst_2 s v))
Case conversion may be inaccurate. Consider using '#align continuous_map.gen_inter ContinuousMap.gen_interₓ'. -/
@[simp]
theorem gen_inter (s : Set α) (u v : Set β) :
    CompactOpen.gen s (u ∩ v) = CompactOpen.gen s u ∩ CompactOpen.gen s v :=
  Set.ext fun f => subset_inter_iff
#align continuous_map.gen_inter ContinuousMap.gen_inter

/- warning: continuous_map.gen_union -> ContinuousMap.gen_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (s : Set.{u1} α) (t : Set.{u1} α) (u : Set.{u2} β), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (ContinuousMap.CompactOpen.gen.{u1, u2} α β _inst_1 _inst_2 (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) u) (Inter.inter.{max u1 u2} (Set.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (Set.hasInter.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (ContinuousMap.CompactOpen.gen.{u1, u2} α β _inst_1 _inst_2 s u) (ContinuousMap.CompactOpen.gen.{u1, u2} α β _inst_1 _inst_2 t u))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (s : Set.{u2} α) (t : Set.{u2} α) (u : Set.{u1} β), Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (ContinuousMap.CompactOpen.gen.{u2, u1} α β _inst_1 _inst_2 (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s t) u) (Inter.inter.{max u1 u2} (Set.{max u1 u2} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (Set.instInterSet.{max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (ContinuousMap.CompactOpen.gen.{u2, u1} α β _inst_1 _inst_2 s u) (ContinuousMap.CompactOpen.gen.{u2, u1} α β _inst_1 _inst_2 t u))
Case conversion may be inaccurate. Consider using '#align continuous_map.gen_union ContinuousMap.gen_unionₓ'. -/
@[simp]
theorem gen_union (s t : Set α) (u : Set β) :
    CompactOpen.gen (s ∪ t) u = CompactOpen.gen s u ∩ CompactOpen.gen t u :=
  Set.ext fun f => (iff_of_eq (congr_arg (· ⊆ u) (image_union f s t))).trans union_subset_iff
#align continuous_map.gen_union ContinuousMap.gen_union

/- warning: continuous_map.gen_empty_right -> ContinuousMap.gen_empty_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Eq.{succ (max u1 u2)} (Set.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (ContinuousMap.CompactOpen.gen.{u1, u2} α β _inst_1 _inst_2 s (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.hasEmptyc.{u2} β))) (EmptyCollection.emptyCollection.{max u1 u2} (Set.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (Set.hasEmptyc.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {s : Set.{u2} α}, (Set.Nonempty.{u2} α s) -> (Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (ContinuousMap.CompactOpen.gen.{u2, u1} α β _inst_1 _inst_2 s (EmptyCollection.emptyCollection.{u1} (Set.{u1} β) (Set.instEmptyCollectionSet.{u1} β))) (EmptyCollection.emptyCollection.{max u2 u1} (Set.{max u1 u2} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (Set.instEmptyCollectionSet.{max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2))))
Case conversion may be inaccurate. Consider using '#align continuous_map.gen_empty_right ContinuousMap.gen_empty_rightₓ'. -/
theorem gen_empty_right {s : Set α} (h : s.Nonempty) : CompactOpen.gen s (∅ : Set β) = ∅ :=
  eq_empty_of_forall_not_mem fun f => (h.image _).not_subset_empty
#align continuous_map.gen_empty_right ContinuousMap.gen_empty_right

#print ContinuousMap.compactOpen /-
-- The compact-open topology on the space of continuous maps α → β.
instance compactOpen : TopologicalSpace C(α, β) :=
  TopologicalSpace.generateFrom
    { m | ∃ (s : Set α)(hs : IsCompact s)(u : Set β)(hu : IsOpen u), m = CompactOpen.gen s u }
#align continuous_map.compact_open ContinuousMap.compactOpen
-/

/- warning: continuous_map.is_open_gen -> ContinuousMap.isOpen_gen is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{u1} α}, (IsCompact.{u1} α _inst_1 s) -> (forall {u : Set.{u2} β}, (IsOpen.{u2} β _inst_2 u) -> (IsOpen.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.compactOpen.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.CompactOpen.gen.{u1, u2} α β _inst_1 _inst_2 s u)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {s : Set.{u2} α}, (IsCompact.{u2} α _inst_1 s) -> (forall {u : Set.{u1} β}, (IsOpen.{u1} β _inst_2 u) -> (IsOpen.{max u1 u2} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) (ContinuousMap.compactOpen.{u2, u1} α β _inst_1 _inst_2) (ContinuousMap.CompactOpen.gen.{u2, u1} α β _inst_1 _inst_2 s u)))
Case conversion may be inaccurate. Consider using '#align continuous_map.is_open_gen ContinuousMap.isOpen_genₓ'. -/
protected theorem isOpen_gen {s : Set α} (hs : IsCompact s) {u : Set β} (hu : IsOpen u) :
    IsOpen (CompactOpen.gen s u) :=
  TopologicalSpace.GenerateOpen.basic _ (by dsimp [mem_set_of_eq] <;> tauto)
#align continuous_map.is_open_gen ContinuousMap.isOpen_gen

section Functorial

variable (g : C(β, γ))

private theorem preimage_gen {s : Set α} (hs : IsCompact s) {u : Set γ} (hu : IsOpen u) :
    ContinuousMap.comp g ⁻¹' CompactOpen.gen s u = CompactOpen.gen s (g ⁻¹' u) :=
  by
  ext ⟨f, _⟩
  change g ∘ f '' s ⊆ u ↔ f '' s ⊆ g ⁻¹' u
  rw [image_comp, image_subset_iff]
#align continuous_map.preimage_gen continuous_map.preimage_gen

/- warning: continuous_map.continuous_comp -> ContinuousMap.continuous_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (g : ContinuousMap.{u2, u3} β γ _inst_2 _inst_3), Continuous.{max u1 u2, max u1 u3} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.compactOpen.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.compactOpen.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] (g : ContinuousMap.{u2, u1} β γ _inst_2 _inst_3), Continuous.{max u3 u2, max u3 u1} (ContinuousMap.{u3, u2} α β _inst_1 _inst_2) (ContinuousMap.{u3, u1} α γ _inst_1 _inst_3) (ContinuousMap.compactOpen.{u3, u2} α β _inst_1 _inst_2) (ContinuousMap.compactOpen.{u3, u1} α γ _inst_1 _inst_3) (ContinuousMap.comp.{u3, u2, u1} α β γ _inst_1 _inst_2 _inst_3 g)
Case conversion may be inaccurate. Consider using '#align continuous_map.continuous_comp ContinuousMap.continuous_compₓ'. -/
/-- C(α, -) is a functor. -/
theorem continuous_comp : Continuous (ContinuousMap.comp g : C(α, β) → C(α, γ)) :=
  continuous_generateFrom fun m ⟨s, hs, u, hu, hm⟩ => by
    rw [hm, preimage_gen g hs hu] <;> exact ContinuousMap.isOpen_gen hs (hu.preimage g.2)
#align continuous_map.continuous_comp ContinuousMap.continuous_comp

variable (f : C(α, β))

private theorem image_gen {s : Set α} (hs : IsCompact s) {u : Set γ} (hu : IsOpen u) :
    (fun g : C(β, γ) => g.comp f) ⁻¹' CompactOpen.gen s u = CompactOpen.gen (f '' s) u :=
  by
  ext ⟨g, _⟩
  change g ∘ f '' s ⊆ u ↔ g '' (f '' s) ⊆ u
  rw [Set.image_comp]
#align continuous_map.image_gen continuous_map.image_gen

/- warning: continuous_map.continuous_comp_left -> ContinuousMap.continuous_comp_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2), Continuous.{max u2 u3, max u1 u3} (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.compactOpen.{u2, u3} β γ _inst_2 _inst_3) (ContinuousMap.compactOpen.{u1, u3} α γ _inst_1 _inst_3) (fun (g : ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) => ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] (f : ContinuousMap.{u1, u3} α β _inst_1 _inst_2), Continuous.{max u3 u2, max u1 u2} (ContinuousMap.{u3, u2} β γ _inst_2 _inst_3) (ContinuousMap.{u1, u2} α γ _inst_1 _inst_3) (ContinuousMap.compactOpen.{u3, u2} β γ _inst_2 _inst_3) (ContinuousMap.compactOpen.{u1, u2} α γ _inst_1 _inst_3) (fun (g : ContinuousMap.{u3, u2} β γ _inst_2 _inst_3) => ContinuousMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f)
Case conversion may be inaccurate. Consider using '#align continuous_map.continuous_comp_left ContinuousMap.continuous_comp_leftₓ'. -/
/-- C(-, γ) is a functor. -/
theorem continuous_comp_left : Continuous (fun g => g.comp f : C(β, γ) → C(α, γ)) :=
  continuous_generateFrom fun m ⟨s, hs, u, hu, hm⟩ =>
    by
    rw [hm, image_gen f hs hu]
    exact ContinuousMap.isOpen_gen (hs.image f.2) hu
#align continuous_map.continuous_comp_left ContinuousMap.continuous_comp_left

/- warning: continuous_map.continuous_comp' -> ContinuousMap.continuous_comp' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : LocallyCompactSpace.{u2} β _inst_2], Continuous.{max (max u1 u2) u2 u3, max u1 u3} (Prod.{max u1 u2, max u2 u3} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3)) (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (Prod.topologicalSpace.{max u1 u2, max u2 u3} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (ContinuousMap.compactOpen.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.compactOpen.{u2, u3} β γ _inst_2 _inst_3)) (ContinuousMap.compactOpen.{u1, u3} α γ _inst_1 _inst_3) (fun (x : Prod.{max u1 u2, max u2 u3} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3)) => ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 (Prod.snd.{max u1 u2, max u2 u3} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) x) (Prod.fst.{max u1 u2, max u2 u3} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] [_inst_4 : LocallyCompactSpace.{u3} β _inst_2], Continuous.{max (max u2 u3) u1, max u1 u2} (Prod.{max u3 u2, max u1 u3} (ContinuousMap.{u2, u3} α β _inst_1 _inst_2) (ContinuousMap.{u3, u1} β γ _inst_2 _inst_3)) (ContinuousMap.{u2, u1} α γ _inst_1 _inst_3) (instTopologicalSpaceProd.{max u2 u3, max u3 u1} (ContinuousMap.{u2, u3} α β _inst_1 _inst_2) (ContinuousMap.{u3, u1} β γ _inst_2 _inst_3) (ContinuousMap.compactOpen.{u2, u3} α β _inst_1 _inst_2) (ContinuousMap.compactOpen.{u3, u1} β γ _inst_2 _inst_3)) (ContinuousMap.compactOpen.{u2, u1} α γ _inst_1 _inst_3) (fun (x : Prod.{max u3 u2, max u1 u3} (ContinuousMap.{u2, u3} α β _inst_1 _inst_2) (ContinuousMap.{u3, u1} β γ _inst_2 _inst_3)) => ContinuousMap.comp.{u2, u3, u1} α β γ _inst_1 _inst_2 _inst_3 (Prod.snd.{max u2 u3, max u3 u1} (ContinuousMap.{u2, u3} α β _inst_1 _inst_2) (ContinuousMap.{u3, u1} β γ _inst_2 _inst_3) x) (Prod.fst.{max u2 u3, max u3 u1} (ContinuousMap.{u2, u3} α β _inst_1 _inst_2) (ContinuousMap.{u3, u1} β γ _inst_2 _inst_3) x))
Case conversion may be inaccurate. Consider using '#align continuous_map.continuous_comp' ContinuousMap.continuous_comp'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Composition is a continuous map from `C(α, β) × C(β, γ)` to `C(α, γ)`, provided that `β` is
  locally compact. This is Prop. 9 of Chap. X, §3, №. 4 of Bourbaki's *Topologie Générale*. -/
theorem continuous_comp' [LocallyCompactSpace β] :
    Continuous fun x : C(α, β) × C(β, γ) => x.2.comp x.1 :=
  continuous_generateFrom
    (by
      rintro M ⟨K, hK, U, hU, rfl⟩
      conv =>
        congr
        rw [compact_open.gen, preimage_set_of_eq]
        congr
        ext
        rw [coe_comp, image_comp, image_subset_iff]
      rw [isOpen_iff_forall_mem_open]
      rintro ⟨φ₀, ψ₀⟩ H
      obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between (hK.image φ₀.2) (hU.preimage ψ₀.2) H
      use { φ : C(α, β) | φ '' K ⊆ interior L } ×ˢ { ψ : C(β, γ) | ψ '' L ⊆ U }
      use fun ⟨φ, ψ⟩ ⟨hφ, hψ⟩ => subset_trans hφ (interior_subset.trans <| image_subset_iff.mp hψ)
      use (ContinuousMap.isOpen_gen hK isOpen_interior).Prod (ContinuousMap.isOpen_gen hL hU)
      exact mem_prod.mpr ⟨hKL, image_subset_iff.mpr hLU⟩)
#align continuous_map.continuous_comp' ContinuousMap.continuous_comp'

/- warning: continuous_map.continuous.comp' -> ContinuousMap.continuous.comp' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {X : Type.{u4}} [_inst_4 : TopologicalSpace.{u4} X] [_inst_5 : LocallyCompactSpace.{u2} β _inst_2] {f : X -> (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)} {g : X -> (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3)}, (Continuous.{u4, max u1 u2} X (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) _inst_4 (ContinuousMap.compactOpen.{u1, u2} α β _inst_1 _inst_2) f) -> (Continuous.{u4, max u2 u3} X (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) _inst_4 (ContinuousMap.compactOpen.{u2, u3} β γ _inst_2 _inst_3) g) -> (Continuous.{u4, max u1 u3} X (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) _inst_4 (ContinuousMap.compactOpen.{u1, u3} α γ _inst_1 _inst_3) (fun (x : X) => ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 (g x) (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] {X : Type.{u4}} [_inst_4 : TopologicalSpace.{u4} X] [_inst_5 : LocallyCompactSpace.{u3} β _inst_2] {f : X -> (ContinuousMap.{u2, u3} α β _inst_1 _inst_2)} {g : X -> (ContinuousMap.{u3, u1} β γ _inst_2 _inst_3)}, (Continuous.{u4, max u2 u3} X (ContinuousMap.{u2, u3} α β _inst_1 _inst_2) _inst_4 (ContinuousMap.compactOpen.{u2, u3} α β _inst_1 _inst_2) f) -> (Continuous.{u4, max u3 u1} X (ContinuousMap.{u3, u1} β γ _inst_2 _inst_3) _inst_4 (ContinuousMap.compactOpen.{u3, u1} β γ _inst_2 _inst_3) g) -> (Continuous.{u4, max u1 u2} X (ContinuousMap.{u2, u1} α γ _inst_1 _inst_3) _inst_4 (ContinuousMap.compactOpen.{u2, u1} α γ _inst_1 _inst_3) (fun (x : X) => ContinuousMap.comp.{u2, u3, u1} α β γ _inst_1 _inst_2 _inst_3 (g x) (f x)))
Case conversion may be inaccurate. Consider using '#align continuous_map.continuous.comp' ContinuousMap.continuous.comp'ₓ'. -/
theorem continuous.comp' {X : Type _} [TopologicalSpace X] [LocallyCompactSpace β] {f : X → C(α, β)}
    {g : X → C(β, γ)} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => (g x).comp (f x) :=
  continuous_comp'.comp (hf.prod_mk hg : Continuous fun x => (f x, g x))
#align continuous_map.continuous.comp' ContinuousMap.continuous.comp'

end Functorial

section Ev

variable {α β}

/- warning: continuous_map.continuous_eval' -> ContinuousMap.continuous_eval' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : LocallyCompactSpace.{u1} α _inst_1], Continuous.{max u1 u2, u2} (Prod.{max u1 u2, u1} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α) β (Prod.topologicalSpace.{max u1 u2, u1} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (ContinuousMap.compactOpen.{u1, u2} α β _inst_1 _inst_2) _inst_1) _inst_2 (fun (p : Prod.{max u1 u2, u1} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (Prod.fst.{max u1 u2, u1} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α p) (Prod.snd.{max u1 u2, u1} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α p))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_4 : LocallyCompactSpace.{u2} α _inst_1], Continuous.{max u2 u1, u1} (Prod.{max u1 u2, u2} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α) β (instTopologicalSpaceProd.{max u2 u1, u2} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (ContinuousMap.compactOpen.{u2, u1} α β _inst_1 _inst_2) _inst_1) _inst_2 (fun (p : Prod.{max u1 u2, u2} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α) => FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (Prod.fst.{max u2 u1, u2} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α p) (Prod.snd.{max u2 u1, u2} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α p))
Case conversion may be inaccurate. Consider using '#align continuous_map.continuous_eval' ContinuousMap.continuous_eval'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The evaluation map `C(α, β) × α → β` is continuous if `α` is locally compact.

See also `continuous_map.continuous_eval` -/
theorem continuous_eval' [LocallyCompactSpace α] : Continuous fun p : C(α, β) × α => p.1 p.2 :=
  continuous_iff_continuousAt.mpr fun ⟨f, x⟩ n hn =>
    let ⟨v, vn, vo, fxv⟩ := mem_nhds_iff.mp hn
    have : v ∈ 𝓝 (f x) := IsOpen.mem_nhds vo fxv
    let ⟨s, hs, sv, sc⟩ :=
      LocallyCompactSpace.local_compact_nhds x (f ⁻¹' v) (f.Continuous.Tendsto x this)
    let ⟨u, us, uo, xu⟩ := mem_nhds_iff.mp hs
    show (fun p : C(α, β) × α => p.1 p.2) ⁻¹' n ∈ 𝓝 (f, x) from
      let w := CompactOpen.gen s v ×ˢ u
      have : w ⊆ (fun p : C(α, β) × α => p.1 p.2) ⁻¹' n := fun ⟨f', x'⟩ ⟨hf', hx'⟩ =>
        calc
          f' x' ∈ f' '' s := mem_image_of_mem f' (us hx')
          _ ⊆ v := hf'
          _ ⊆ n := vn
          
      have : IsOpen w := (ContinuousMap.isOpen_gen sc vo).Prod uo
      have : (f, x) ∈ w := ⟨image_subset_iff.mpr sv, xu⟩
      mem_nhds_iff.mpr ⟨w, by assumption, by assumption, by assumption⟩
#align continuous_map.continuous_eval' ContinuousMap.continuous_eval'

/- warning: continuous_map.continuous_eval_const' -> ContinuousMap.continuous_eval_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : LocallyCompactSpace.{u1} α _inst_1] (a : α), Continuous.{max u1 u2, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) β (ContinuousMap.compactOpen.{u1, u2} α β _inst_1 _inst_2) _inst_2 (fun (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_4 : LocallyCompactSpace.{u2} α _inst_1] (a : α), Continuous.{max u2 u1, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) a) (ContinuousMap.compactOpen.{u2, u1} α β _inst_1 _inst_2) _inst_2 (fun (f : ContinuousMap.{u2, u1} α β _inst_1 _inst_2) => FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) f a)
Case conversion may be inaccurate. Consider using '#align continuous_map.continuous_eval_const' ContinuousMap.continuous_eval_const'ₓ'. -/
/-- See also `continuous_map.continuous_eval_const` -/
theorem continuous_eval_const' [LocallyCompactSpace α] (a : α) :
    Continuous fun f : C(α, β) => f a :=
  continuous_eval'.comp (continuous_id.prod_mk continuous_const)
#align continuous_map.continuous_eval_const' ContinuousMap.continuous_eval_const'

/- warning: continuous_map.continuous_coe' -> ContinuousMap.continuous_coe' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : LocallyCompactSpace.{u1} α _inst_1], Continuous.{max u1 u2, max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (α -> β) (ContinuousMap.compactOpen.{u1, u2} α β _inst_1 _inst_2) (Pi.topologicalSpace.{u1, u2} α (fun (ᾰ : α) => β) (fun (a : α) => _inst_2)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (ᾰ : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_4 : LocallyCompactSpace.{u2} α _inst_1], Continuous.{max u1 u2, max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) (α -> β) (ContinuousMap.compactOpen.{u2, u1} α β _inst_1 _inst_2) (Pi.topologicalSpace.{u2, u1} α (fun (ᾰ : α) => β) (fun (a : α) => _inst_2)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (ᾰ : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)))
Case conversion may be inaccurate. Consider using '#align continuous_map.continuous_coe' ContinuousMap.continuous_coe'ₓ'. -/
/-- See also `continuous_map.continuous_coe` -/
theorem continuous_coe' [LocallyCompactSpace α] : @Continuous C(α, β) (α → β) _ _ coeFn :=
  continuous_pi continuous_eval_const'
#align continuous_map.continuous_coe' ContinuousMap.continuous_coe'

instance [T2Space β] : T2Space C(α, β) :=
  ⟨by
    intro f₁ f₂ h
    obtain ⟨x, hx⟩ := not_forall.mp (mt (FunLike.ext f₁ f₂) h)
    obtain ⟨u, v, hu, hv, hxu, hxv, huv⟩ := t2_separation hx
    refine'
      ⟨compact_open.gen {x} u, compact_open.gen {x} v,
        ContinuousMap.isOpen_gen isCompact_singleton hu,
        ContinuousMap.isOpen_gen isCompact_singleton hv, _, _, _⟩
    · rwa [compact_open.gen, mem_set_of_eq, image_singleton, singleton_subset_iff]
    · rwa [compact_open.gen, mem_set_of_eq, image_singleton, singleton_subset_iff]
    ·
      rw [disjoint_iff_inter_eq_empty, ← gen_inter, huv.inter_eq,
        gen_empty_right (singleton_nonempty _)]⟩

end Ev

section InfInduced

/- warning: continuous_map.compact_open_le_induced -> ContinuousMap.compactOpen_le_induced is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (s : Set.{u1} α), LE.le.{max u1 u2} (TopologicalSpace.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (Preorder.toLE.{max u1 u2} (TopologicalSpace.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (PartialOrder.toPreorder.{max u1 u2} (TopologicalSpace.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (TopologicalSpace.partialOrder.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)))) (ContinuousMap.compactOpen.{u1, u2} α β _inst_1 _inst_2) (TopologicalSpace.induced.{max u1 u2, max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) (ContinuousMap.restrict.{u1, u2} α β _inst_1 _inst_2 s) (ContinuousMap.compactOpen.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (s : Set.{u2} α), LE.le.{max u2 u1} (TopologicalSpace.{max u1 u2} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (Preorder.toLE.{max u2 u1} (TopologicalSpace.{max u1 u2} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (PartialOrder.toPreorder.{max u2 u1} (TopologicalSpace.{max u1 u2} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (TopologicalSpace.instPartialOrderTopologicalSpace.{max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)))) (ContinuousMap.compactOpen.{u2, u1} α β _inst_1 _inst_2) (TopologicalSpace.induced.{max u2 u1, max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) (ContinuousMap.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2) (ContinuousMap.restrict.{u2, u1} α β _inst_1 _inst_2 s) (ContinuousMap.compactOpen.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2))
Case conversion may be inaccurate. Consider using '#align continuous_map.compact_open_le_induced ContinuousMap.compactOpen_le_inducedₓ'. -/
theorem compactOpen_le_induced (s : Set α) :
    (ContinuousMap.compactOpen : TopologicalSpace C(α, β)) ≤
      TopologicalSpace.induced (ContinuousMap.restrict s) ContinuousMap.compactOpen :=
  by
  simp only [induced_generateFrom_eq, ContinuousMap.compactOpen]
  apply TopologicalSpace.generateFrom_anti
  rintro b ⟨a, ⟨c, hc, u, hu, rfl⟩, rfl⟩
  refine' ⟨coe '' c, hc.image continuous_subtype_val, u, hu, _⟩
  ext f
  simp only [compact_open.gen, mem_set_of_eq, mem_preimage, ContinuousMap.coe_restrict]
  rw [image_comp f (coe : s → α)]
#align continuous_map.compact_open_le_induced ContinuousMap.compactOpen_le_induced

/- warning: continuous_map.compact_open_eq_Inf_induced -> ContinuousMap.compactOpen_eq_infₛ_induced is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], Eq.{succ (max u1 u2)} (TopologicalSpace.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (ContinuousMap.compactOpen.{u1, u2} α β _inst_1 _inst_2) (infᵢ.{max u1 u2, succ u1} (TopologicalSpace.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (ConditionallyCompleteLattice.toHasInf.{max u1 u2} (TopologicalSpace.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (CompleteLattice.toConditionallyCompleteLattice.{max u1 u2} (TopologicalSpace.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (TopologicalSpace.completeLattice.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)))) (Set.{u1} α) (fun (s : Set.{u1} α) => infᵢ.{max u1 u2, 0} (TopologicalSpace.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (ConditionallyCompleteLattice.toHasInf.{max u1 u2} (TopologicalSpace.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (CompleteLattice.toConditionallyCompleteLattice.{max u1 u2} (TopologicalSpace.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (TopologicalSpace.completeLattice.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)))) (IsCompact.{u1} α _inst_1 s) (fun (hs : IsCompact.{u1} α _inst_1 s) => TopologicalSpace.induced.{max u1 u2, max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) (ContinuousMap.restrict.{u1, u2} α β _inst_1 _inst_2 s) (ContinuousMap.compactOpen.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β], Eq.{max (succ u2) (succ u1)} (TopologicalSpace.{max u1 u2} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (ContinuousMap.compactOpen.{u2, u1} α β _inst_1 _inst_2) (infᵢ.{max u2 u1, succ u2} (TopologicalSpace.{max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (ConditionallyCompleteLattice.toInfSet.{max u2 u1} (TopologicalSpace.{max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (CompleteLattice.toConditionallyCompleteLattice.{max u2 u1} (TopologicalSpace.{max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)))) (Set.{u2} α) (fun (s : Set.{u2} α) => infᵢ.{max u2 u1, 0} (TopologicalSpace.{max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (ConditionallyCompleteLattice.toInfSet.{max u2 u1} (TopologicalSpace.{max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (CompleteLattice.toConditionallyCompleteLattice.{max u2 u1} (TopologicalSpace.{max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)))) (IsCompact.{u2} α _inst_1 s) (fun (hs : IsCompact.{u2} α _inst_1 s) => TopologicalSpace.induced.{max u2 u1, max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) (ContinuousMap.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2) (ContinuousMap.restrict.{u2, u1} α β _inst_1 _inst_2 s) (ContinuousMap.compactOpen.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2))))
Case conversion may be inaccurate. Consider using '#align continuous_map.compact_open_eq_Inf_induced ContinuousMap.compactOpen_eq_infₛ_inducedₓ'. -/
/-- The compact-open topology on `C(α, β)` is equal to the infimum of the compact-open topologies
on `C(s, β)` for `s` a compact subset of `α`.  The key point of the proof is that the union of the
compact subsets of `α` is equal to the union of compact subsets of the compact subsets of `α`. -/
theorem compactOpen_eq_infₛ_induced :
    (ContinuousMap.compactOpen : TopologicalSpace C(α, β)) =
      ⨅ (s : Set α) (hs : IsCompact s),
        TopologicalSpace.induced (ContinuousMap.restrict s) ContinuousMap.compactOpen :=
  by
  refine' le_antisymm _ _
  · refine' le_infᵢ₂ _
    exact fun s hs => compact_open_le_induced s
  simp only [← generateFrom_unionᵢ, induced_generateFrom_eq, ContinuousMap.compactOpen]
  apply TopologicalSpace.generateFrom_anti
  rintro _ ⟨s, hs, u, hu, rfl⟩
  rw [mem_Union₂]
  refine' ⟨s, hs, _, ⟨univ, is_compact_iff_is_compact_univ.mp hs, u, hu, rfl⟩, _⟩
  ext f
  simp only [compact_open.gen, mem_set_of_eq, mem_preimage, ContinuousMap.coe_restrict]
  rw [image_comp f (coe : s → α)]
  simp
#align continuous_map.compact_open_eq_Inf_induced ContinuousMap.compactOpen_eq_infₛ_induced

/- warning: continuous_map.continuous_restrict -> ContinuousMap.continuous_restrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (s : Set.{u1} α), Continuous.{max u1 u2, max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) (ContinuousMap.compactOpen.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.compactOpen.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) (fun (F : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => ContinuousMap.restrict.{u1, u2} α β _inst_1 _inst_2 s F)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (s : Set.{u2} α), Continuous.{max u2 u1, max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) (ContinuousMap.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2) (ContinuousMap.compactOpen.{u2, u1} α β _inst_1 _inst_2) (ContinuousMap.compactOpen.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2) (fun (F : ContinuousMap.{u2, u1} α β _inst_1 _inst_2) => ContinuousMap.restrict.{u2, u1} α β _inst_1 _inst_2 s F)
Case conversion may be inaccurate. Consider using '#align continuous_map.continuous_restrict ContinuousMap.continuous_restrictₓ'. -/
/-- For any subset `s` of `α`, the restriction of continuous functions to `s` is continuous as a
function from `C(α, β)` to `C(s, β)` with their respective compact-open topologies. -/
theorem continuous_restrict (s : Set α) : Continuous fun F : C(α, β) => F.restrict s :=
  by
  rw [continuous_iff_le_induced]
  exact compact_open_le_induced s
#align continuous_map.continuous_restrict ContinuousMap.continuous_restrict

/- warning: continuous_map.nhds_compact_open_eq_Inf_nhds_induced -> ContinuousMap.nhds_compactOpen_eq_infₛ_nhds_induced is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2), Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (nhds.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.compactOpen.{u1, u2} α β _inst_1 _inst_2) f) (infᵢ.{max u1 u2, succ u1} (Filter.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (ConditionallyCompleteLattice.toHasInf.{max u1 u2} (Filter.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (CompleteLattice.toConditionallyCompleteLattice.{max u1 u2} (Filter.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (Filter.completeLattice.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)))) (Set.{u1} α) (fun (s : Set.{u1} α) => infᵢ.{max u1 u2, 0} (Filter.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (ConditionallyCompleteLattice.toHasInf.{max u1 u2} (Filter.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (CompleteLattice.toConditionallyCompleteLattice.{max u1 u2} (Filter.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (Filter.completeLattice.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)))) (IsCompact.{u1} α _inst_1 s) (fun (hs : IsCompact.{u1} α _inst_1 s) => Filter.comap.{max u1 u2, max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) (ContinuousMap.restrict.{u1, u2} α β _inst_1 _inst_2 s) (nhds.{max u1 u2} (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) (ContinuousMap.compactOpen.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) (ContinuousMap.restrict.{u1, u2} α β _inst_1 _inst_2 s f)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : ContinuousMap.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (Filter.{max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (nhds.{max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) (ContinuousMap.compactOpen.{u2, u1} α β _inst_1 _inst_2) f) (infᵢ.{max u2 u1, succ u2} (Filter.{max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (ConditionallyCompleteLattice.toInfSet.{max u2 u1} (Filter.{max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (CompleteLattice.toConditionallyCompleteLattice.{max u2 u1} (Filter.{max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (Filter.instCompleteLatticeFilter.{max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)))) (Set.{u2} α) (fun (s : Set.{u2} α) => infᵢ.{max u2 u1, 0} (Filter.{max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (ConditionallyCompleteLattice.toInfSet.{max u2 u1} (Filter.{max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (CompleteLattice.toConditionallyCompleteLattice.{max u2 u1} (Filter.{max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (Filter.instCompleteLatticeFilter.{max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)))) (IsCompact.{u2} α _inst_1 s) (fun (hs : IsCompact.{u2} α _inst_1 s) => Filter.comap.{max u2 u1, max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) (ContinuousMap.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2) (ContinuousMap.restrict.{u2, u1} α β _inst_1 _inst_2 s) (nhds.{max u2 u1} (ContinuousMap.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2) (ContinuousMap.compactOpen.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2) (ContinuousMap.restrict.{u2, u1} α β _inst_1 _inst_2 s f)))))
Case conversion may be inaccurate. Consider using '#align continuous_map.nhds_compact_open_eq_Inf_nhds_induced ContinuousMap.nhds_compactOpen_eq_infₛ_nhds_inducedₓ'. -/
theorem nhds_compactOpen_eq_infₛ_nhds_induced (f : C(α, β)) :
    𝓝 f = ⨅ (s) (hs : IsCompact s), (𝓝 (f.restrict s)).comap (ContinuousMap.restrict s) :=
  by
  rw [compact_open_eq_Inf_induced]
  simp [nhds_infᵢ, nhds_induced]
#align continuous_map.nhds_compact_open_eq_Inf_nhds_induced ContinuousMap.nhds_compactOpen_eq_infₛ_nhds_induced

/- warning: continuous_map.tendsto_compact_open_restrict -> ContinuousMap.tendsto_compactOpen_restrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {ι : Type.{u3}} {l : Filter.{u3} ι} {F : ι -> (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)} {f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2}, (Filter.Tendsto.{u3, max u1 u2} ι (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) F l (nhds.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.compactOpen.{u1, u2} α β _inst_1 _inst_2) f)) -> (forall (s : Set.{u1} α), Filter.Tendsto.{u3, max u1 u2} ι (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) (fun (i : ι) => ContinuousMap.restrict.{u1, u2} α β _inst_1 _inst_2 s (F i)) l (nhds.{max u1 u2} (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) (ContinuousMap.compactOpen.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) (ContinuousMap.restrict.{u1, u2} α β _inst_1 _inst_2 s f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {ι : Type.{u3}} {l : Filter.{u3} ι} {F : ι -> (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)} {f : ContinuousMap.{u2, u1} α β _inst_1 _inst_2}, (Filter.Tendsto.{u3, max u2 u1} ι (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) F l (nhds.{max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) (ContinuousMap.compactOpen.{u2, u1} α β _inst_1 _inst_2) f)) -> (forall (s : Set.{u2} α), Filter.Tendsto.{u3, max u2 u1} ι (ContinuousMap.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2) (fun (i : ι) => ContinuousMap.restrict.{u2, u1} α β _inst_1 _inst_2 s (F i)) l (nhds.{max u2 u1} (ContinuousMap.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2) (ContinuousMap.compactOpen.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2) (ContinuousMap.restrict.{u2, u1} α β _inst_1 _inst_2 s f)))
Case conversion may be inaccurate. Consider using '#align continuous_map.tendsto_compact_open_restrict ContinuousMap.tendsto_compactOpen_restrictₓ'. -/
theorem tendsto_compactOpen_restrict {ι : Type _} {l : Filter ι} {F : ι → C(α, β)} {f : C(α, β)}
    (hFf : Filter.Tendsto F l (𝓝 f)) (s : Set α) :
    Filter.Tendsto (fun i => (F i).restrict s) l (𝓝 (f.restrict s)) :=
  (continuous_restrict s).ContinuousAt.Tendsto.comp hFf
#align continuous_map.tendsto_compact_open_restrict ContinuousMap.tendsto_compactOpen_restrict

/- warning: continuous_map.tendsto_compact_open_iff_forall -> ContinuousMap.tendsto_compactOpen_iff_forall is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {ι : Type.{u3}} {l : Filter.{u3} ι} (F : ι -> (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2), Iff (Filter.Tendsto.{u3, max u1 u2} ι (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) F l (nhds.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.compactOpen.{u1, u2} α β _inst_1 _inst_2) f)) (forall (s : Set.{u1} α), (IsCompact.{u1} α _inst_1 s) -> (Filter.Tendsto.{u3, max u1 u2} ι (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) (fun (i : ι) => ContinuousMap.restrict.{u1, u2} α β _inst_1 _inst_2 s (F i)) l (nhds.{max u1 u2} (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) (ContinuousMap.compactOpen.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) (ContinuousMap.restrict.{u1, u2} α β _inst_1 _inst_2 s f))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {ι : Type.{u3}} {l : Filter.{u3} ι} (F : ι -> (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (f : ContinuousMap.{u2, u1} α β _inst_1 _inst_2), Iff (Filter.Tendsto.{u3, max u2 u1} ι (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) F l (nhds.{max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) (ContinuousMap.compactOpen.{u2, u1} α β _inst_1 _inst_2) f)) (forall (s : Set.{u2} α), (IsCompact.{u2} α _inst_1 s) -> (Filter.Tendsto.{u3, max u2 u1} ι (ContinuousMap.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2) (fun (i : ι) => ContinuousMap.restrict.{u2, u1} α β _inst_1 _inst_2 s (F i)) l (nhds.{max u2 u1} (ContinuousMap.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2) (ContinuousMap.compactOpen.{u2, u1} (Set.Elem.{u2} α s) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) _inst_1) _inst_2) (ContinuousMap.restrict.{u2, u1} α β _inst_1 _inst_2 s f))))
Case conversion may be inaccurate. Consider using '#align continuous_map.tendsto_compact_open_iff_forall ContinuousMap.tendsto_compactOpen_iff_forallₓ'. -/
theorem tendsto_compactOpen_iff_forall {ι : Type _} {l : Filter ι} (F : ι → C(α, β)) (f : C(α, β)) :
    Filter.Tendsto F l (𝓝 f) ↔
      ∀ (s) (hs : IsCompact s), Filter.Tendsto (fun i => (F i).restrict s) l (𝓝 (f.restrict s)) :=
  by
  rw [compact_open_eq_Inf_induced]
  simp [nhds_infᵢ, nhds_induced, Filter.tendsto_comap_iff]
#align continuous_map.tendsto_compact_open_iff_forall ContinuousMap.tendsto_compactOpen_iff_forall

/- warning: continuous_map.exists_tendsto_compact_open_iff_forall -> ContinuousMap.exists_tendsto_compactOpen_iff_forall is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : LocallyCompactSpace.{u1} α _inst_1] [_inst_5 : T2Space.{u1} α _inst_1] [_inst_6 : T2Space.{u2} β _inst_2] {ι : Type.{u3}} {l : Filter.{u3} ι} [_inst_7 : Filter.NeBot.{u3} ι l] (F : ι -> (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)), Iff (Exists.{max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => Filter.Tendsto.{u3, max u1 u2} ι (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) F l (nhds.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.compactOpen.{u1, u2} α β _inst_1 _inst_2) f))) (forall (s : Set.{u1} α), (IsCompact.{u1} α _inst_1 s) -> (Exists.{max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) (fun (f : ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) => Filter.Tendsto.{u3, max u1 u2} ι (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) (fun (i : ι) => ContinuousMap.restrict.{u1, u2} α β _inst_1 _inst_2 s (F i)) l (nhds.{max u1 u2} (ContinuousMap.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) (ContinuousMap.compactOpen.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) _inst_2) f))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : LocallyCompactSpace.{u3} α _inst_1] [_inst_5 : T2Space.{u3} α _inst_1] [_inst_6 : T2Space.{u2} β _inst_2] {ι : Type.{u1}} {l : Filter.{u1} ι} [_inst_7 : Filter.NeBot.{u1} ι l] (F : ι -> (ContinuousMap.{u3, u2} α β _inst_1 _inst_2)), Iff (Exists.{max (succ u3) (succ u2)} (ContinuousMap.{u3, u2} α β _inst_1 _inst_2) (fun (f : ContinuousMap.{u3, u2} α β _inst_1 _inst_2) => Filter.Tendsto.{u1, max u3 u2} ι (ContinuousMap.{u3, u2} α β _inst_1 _inst_2) F l (nhds.{max u3 u2} (ContinuousMap.{u3, u2} α β _inst_1 _inst_2) (ContinuousMap.compactOpen.{u3, u2} α β _inst_1 _inst_2) f))) (forall (s : Set.{u3} α), (IsCompact.{u3} α _inst_1 s) -> (Exists.{max (succ u3) (succ u2)} (ContinuousMap.{u3, u2} (Set.Elem.{u3} α s) β (instTopologicalSpaceSubtype.{u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x s) _inst_1) _inst_2) (fun (f : ContinuousMap.{u3, u2} (Set.Elem.{u3} α s) β (instTopologicalSpaceSubtype.{u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x s) _inst_1) _inst_2) => Filter.Tendsto.{u1, max u3 u2} ι (ContinuousMap.{u3, u2} (Set.Elem.{u3} α s) β (instTopologicalSpaceSubtype.{u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x s) _inst_1) _inst_2) (fun (i : ι) => ContinuousMap.restrict.{u3, u2} α β _inst_1 _inst_2 s (F i)) l (nhds.{max u3 u2} (ContinuousMap.{u3, u2} (Set.Elem.{u3} α s) β (instTopologicalSpaceSubtype.{u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x s) _inst_1) _inst_2) (ContinuousMap.compactOpen.{u3, u2} (Set.Elem.{u3} α s) β (instTopologicalSpaceSubtype.{u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x s) _inst_1) _inst_2) f))))
Case conversion may be inaccurate. Consider using '#align continuous_map.exists_tendsto_compact_open_iff_forall ContinuousMap.exists_tendsto_compactOpen_iff_forallₓ'. -/
/-- A family `F` of functions in `C(α, β)` converges in the compact-open topology, if and only if
it converges in the compact-open topology on each compact subset of `α`. -/
theorem exists_tendsto_compactOpen_iff_forall [LocallyCompactSpace α] [T2Space α] [T2Space β]
    {ι : Type _} {l : Filter ι} [Filter.NeBot l] (F : ι → C(α, β)) :
    (∃ f, Filter.Tendsto F l (𝓝 f)) ↔
      ∀ (s : Set α) (hs : IsCompact s), ∃ f, Filter.Tendsto (fun i => (F i).restrict s) l (𝓝 f) :=
  by
  constructor
  · rintro ⟨f, hf⟩ s hs
    exact ⟨f.restrict s, tendsto_compact_open_restrict hf s⟩
  · intro h
    choose f hf using h
    -- By uniqueness of limits in a `t2_space`, since `λ i, F i x` tends to both `f s₁ hs₁ x` and
    -- `f s₂ hs₂ x`, we have `f s₁ hs₁ x = f s₂ hs₂ x`
    have h :
      ∀ (s₁) (hs₁ : IsCompact s₁) (s₂) (hs₂ : IsCompact s₂) (x : α) (hxs₁ : x ∈ s₁) (hxs₂ : x ∈ s₂),
        f s₁ hs₁ ⟨x, hxs₁⟩ = f s₂ hs₂ ⟨x, hxs₂⟩ :=
      by
      rintro s₁ hs₁ s₂ hs₂ x hxs₁ hxs₂
      haveI := is_compact_iff_compact_space.mp hs₁
      haveI := is_compact_iff_compact_space.mp hs₂
      have h₁ := (continuous_eval_const' (⟨x, hxs₁⟩ : s₁)).ContinuousAt.Tendsto.comp (hf s₁ hs₁)
      have h₂ := (continuous_eval_const' (⟨x, hxs₂⟩ : s₂)).ContinuousAt.Tendsto.comp (hf s₂ hs₂)
      exact tendsto_nhds_unique h₁ h₂
    -- So glue the `f s hs` together and prove that this glued function `f₀` is a limit on each
    -- compact set `s`
    have hs : ∀ x : α, ∃ (s : _)(hs : IsCompact s), s ∈ 𝓝 x :=
      by
      intro x
      obtain ⟨s, hs, hs'⟩ := exists_compact_mem_nhds x
      exact ⟨s, hs, hs'⟩
    refine' ⟨lift_cover' _ _ h hs, _⟩
    rw [tendsto_compact_open_iff_forall]
    intro s hs
    rw [lift_cover_restrict']
    exact hf s hs
#align continuous_map.exists_tendsto_compact_open_iff_forall ContinuousMap.exists_tendsto_compactOpen_iff_forall

end InfInduced

section Coev

variable (α β)

/- warning: continuous_map.coev -> ContinuousMap.coev is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}) [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], β -> (ContinuousMap.{u1, max u2 u1} α (Prod.{u2, u1} β α) _inst_1 (Prod.topologicalSpace.{u2, u1} β α _inst_2 _inst_1))
but is expected to have type
  forall (α : Type.{u1}) (β : Type.{u2}) [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], β -> (ContinuousMap.{u1, max u1 u2} α (Prod.{u2, u1} β α) _inst_1 (instTopologicalSpaceProd.{u2, u1} β α _inst_2 _inst_1))
Case conversion may be inaccurate. Consider using '#align continuous_map.coev ContinuousMap.coevₓ'. -/
/-- The coevaluation map `β → C(α, β × α)` sending a point `x : β` to the continuous function
on `α` sending `y` to `(x, y)`. -/
def coev (b : β) : C(α, β × α) :=
  ⟨Prod.mk b, continuous_const.prod_mk continuous_id⟩
#align continuous_map.coev ContinuousMap.coev

variable {α β}

/- warning: continuous_map.image_coev -> ContinuousMap.image_coev is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {y : β} (s : Set.{u1} α), Eq.{succ (max u2 u1)} (Set.{max u2 u1} (Prod.{u2, u1} β α)) (Set.image.{u1, max u2 u1} α (Prod.{u2, u1} β α) (coeFn.{max (succ u1) (succ (max u2 u1)), max (succ u1) (succ (max u2 u1))} (ContinuousMap.{u1, max u2 u1} α (Prod.{u2, u1} β α) _inst_1 (Prod.topologicalSpace.{u2, u1} β α _inst_2 _inst_1)) (fun (_x : ContinuousMap.{u1, max u2 u1} α (Prod.{u2, u1} β α) _inst_1 (Prod.topologicalSpace.{u2, u1} β α _inst_2 _inst_1)) => α -> (Prod.{u2, u1} β α)) (ContinuousMap.hasCoeToFun.{u1, max u2 u1} α (Prod.{u2, u1} β α) _inst_1 (Prod.topologicalSpace.{u2, u1} β α _inst_2 _inst_1)) (ContinuousMap.coev.{u1, u2} α β _inst_1 _inst_2 y)) s) (Set.prod.{u2, u1} β α (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) y) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {y : β} (s : Set.{u2} α), Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (Prod.{u1, u2} β α)) (Set.image.{u2, max u2 u1} α (Prod.{u1, u2} β α) (FunLike.coe.{max (succ u2) (succ u1), succ u2, max (succ u2) (succ u1)} (ContinuousMap.{u2, max u2 u1} α (Prod.{u1, u2} β α) _inst_1 (instTopologicalSpaceProd.{u1, u2} β α _inst_2 _inst_1)) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => Prod.{u1, u2} β α) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, max u2 u1} (ContinuousMap.{u2, max u2 u1} α (Prod.{u1, u2} β α) _inst_1 (instTopologicalSpaceProd.{u1, u2} β α _inst_2 _inst_1)) α (Prod.{u1, u2} β α) _inst_1 (instTopologicalSpaceProd.{u1, u2} β α _inst_2 _inst_1) (ContinuousMap.instContinuousMapClassContinuousMap.{u2, max u2 u1} α (Prod.{u1, u2} β α) _inst_1 (instTopologicalSpaceProd.{u1, u2} β α _inst_2 _inst_1))) (ContinuousMap.coev.{u2, u1} α β _inst_1 _inst_2 y)) s) (Set.prod.{u1, u2} β α (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) y) s)
Case conversion may be inaccurate. Consider using '#align continuous_map.image_coev ContinuousMap.image_coevₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem image_coev {y : β} (s : Set α) : coev α β y '' s = ({y} : Set β) ×ˢ s := by tidy
#align continuous_map.image_coev ContinuousMap.image_coev

/- warning: continuous_map.continuous_coev -> ContinuousMap.continuous_coev is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], Continuous.{u2, max u2 u1} β (ContinuousMap.{u1, max u2 u1} α (Prod.{u2, u1} β α) _inst_1 (Prod.topologicalSpace.{u2, u1} β α _inst_2 _inst_1)) _inst_2 (ContinuousMap.compactOpen.{u1, max u2 u1} α (Prod.{u2, u1} β α) _inst_1 (Prod.topologicalSpace.{u2, u1} β α _inst_2 _inst_1)) (ContinuousMap.coev.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], Continuous.{u2, max u1 u2} β (ContinuousMap.{u1, max u1 u2} α (Prod.{u2, u1} β α) _inst_1 (instTopologicalSpaceProd.{u2, u1} β α _inst_2 _inst_1)) _inst_2 (ContinuousMap.compactOpen.{u1, max u1 u2} α (Prod.{u2, u1} β α) _inst_1 (instTopologicalSpaceProd.{u2, u1} β α _inst_2 _inst_1)) (ContinuousMap.coev.{u1, u2} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align continuous_map.continuous_coev ContinuousMap.continuous_coevₓ'. -/
-- The coevaluation map β → C(α, β × α) is continuous (always).
theorem continuous_coev : Continuous (coev α β) :=
  continuous_generateFrom <| by
    rintro _ ⟨s, sc, u, uo, rfl⟩
    rw [isOpen_iff_forall_mem_open]
    intro y hy
    change coev α β y '' s ⊆ u at hy
    rw [image_coev s] at hy
    rcases generalized_tube_lemma isCompact_singleton sc uo hy with ⟨v, w, vo, wo, yv, sw, vwu⟩
    refine' ⟨v, _, vo, singleton_subset_iff.mp yv⟩
    intro y' hy'
    change coev α β y' '' s ⊆ u
    rw [image_coev s]
    exact subset.trans (prod_mono (singleton_subset_iff.mpr hy') sw) vwu
#align continuous_map.continuous_coev ContinuousMap.continuous_coev

end Coev

section Curry

/- warning: continuous_map.curry' -> ContinuousMap.curry' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ], (ContinuousMap.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3) -> α -> (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ], (ContinuousMap.{max u2 u1, u3} (Prod.{u1, u2} α β) γ (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) _inst_3) -> α -> (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3)
Case conversion may be inaccurate. Consider using '#align continuous_map.curry' ContinuousMap.curry'ₓ'. -/
/-- Auxiliary definition, see `continuous_map.curry` and `homeomorph.curry`. -/
def curry' (f : C(α × β, γ)) (a : α) : C(β, γ) :=
  ⟨Function.curry f a⟩
#align continuous_map.curry' ContinuousMap.curry'

/- warning: continuous_map.continuous_curry' -> ContinuousMap.continuous_curry' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (f : ContinuousMap.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3), Continuous.{u1, max u2 u3} α (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u2, u3} β γ _inst_2 _inst_3) (ContinuousMap.curry'.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] (f : ContinuousMap.{max u3 u2, u1} (Prod.{u2, u3} α β) γ (instTopologicalSpaceProd.{u2, u3} α β _inst_1 _inst_2) _inst_3), Continuous.{u2, max u1 u3} α (ContinuousMap.{u3, u1} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u3, u1} β γ _inst_2 _inst_3) (ContinuousMap.curry'.{u2, u3, u1} α β γ _inst_1 _inst_2 _inst_3 f)
Case conversion may be inaccurate. Consider using '#align continuous_map.continuous_curry' ContinuousMap.continuous_curry'ₓ'. -/
/-- If a map `α × β → γ` is continuous, then its curried form `α → C(β, γ)` is continuous. -/
theorem continuous_curry' (f : C(α × β, γ)) : Continuous (curry' f) :=
  have hf : curry' f = ContinuousMap.comp f ∘ coev _ _ :=
    by
    ext
    rfl
  hf ▸ Continuous.comp (continuous_comp f) continuous_coev
#align continuous_map.continuous_curry' ContinuousMap.continuous_curry'

/- warning: continuous_map.continuous_of_continuous_uncurry -> ContinuousMap.continuous_of_continuous_uncurry is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (f : α -> (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3)), (Continuous.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3 (Function.uncurry.{u1, u2, u3} α β γ (fun (x : α) (y : β) => coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (ContinuousMap.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) (f x) y))) -> (Continuous.{u1, max u2 u3} α (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u2, u3} β γ _inst_2 _inst_3) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] (f : α -> (ContinuousMap.{u3, u2} β γ _inst_2 _inst_3)), (Continuous.{max u3 u1, u2} (Prod.{u1, u3} α β) γ (instTopologicalSpaceProd.{u1, u3} α β _inst_1 _inst_2) _inst_3 (Function.uncurry.{u1, u3, u2} α β γ (fun (x : α) (y : β) => FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (ContinuousMap.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : β) => γ) _x) (ContinuousMapClass.toFunLike.{max u3 u2, u3, u2} (ContinuousMap.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (ContinuousMap.instContinuousMapClassContinuousMap.{u3, u2} β γ _inst_2 _inst_3)) (f x) y))) -> (Continuous.{u1, max u3 u2} α (ContinuousMap.{u3, u2} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u3, u2} β γ _inst_2 _inst_3) f)
Case conversion may be inaccurate. Consider using '#align continuous_map.continuous_of_continuous_uncurry ContinuousMap.continuous_of_continuous_uncurryₓ'. -/
/-- To show continuity of a map `α → C(β, γ)`, it suffices to show that its uncurried form
    `α × β → γ` is continuous. -/
theorem continuous_of_continuous_uncurry (f : α → C(β, γ))
    (h : Continuous (Function.uncurry fun x y => f x y)) : Continuous f :=
  by
  convert continuous_curry' ⟨_, h⟩
  ext
  rfl
#align continuous_map.continuous_of_continuous_uncurry ContinuousMap.continuous_of_continuous_uncurry

/- warning: continuous_map.curry -> ContinuousMap.curry is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ], (ContinuousMap.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3) -> (ContinuousMap.{u1, max u2 u3} α (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u2, u3} β γ _inst_2 _inst_3))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ], (ContinuousMap.{max u2 u1, u3} (Prod.{u1, u2} α β) γ (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) _inst_3) -> (ContinuousMap.{u1, max u3 u2} α (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u2, u3} β γ _inst_2 _inst_3))
Case conversion may be inaccurate. Consider using '#align continuous_map.curry ContinuousMap.curryₓ'. -/
/-- The curried form of a continuous map `α × β → γ` as a continuous map `α → C(β, γ)`.
    If `a × β` is locally compact, this is continuous. If `α` and `β` are both locally
    compact, then this is a homeomorphism, see `homeomorph.curry`. -/
def curry (f : C(α × β, γ)) : C(α, C(β, γ)) :=
  ⟨_, continuous_curry' f⟩
#align continuous_map.curry ContinuousMap.curry

/- warning: continuous_map.continuous_curry -> ContinuousMap.continuous_curry is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : LocallyCompactSpace.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2)], Continuous.{max (max u1 u2) u3, max u1 u2 u3} (ContinuousMap.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3) (ContinuousMap.{u1, max u2 u3} α (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u2, u3} β γ _inst_2 _inst_3)) (ContinuousMap.compactOpen.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3) (ContinuousMap.compactOpen.{u1, max u2 u3} α (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u2, u3} β γ _inst_2 _inst_3)) (ContinuousMap.curry.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] [_inst_4 : LocallyCompactSpace.{max u3 u2} (Prod.{u2, u3} α β) (instTopologicalSpaceProd.{u2, u3} α β _inst_1 _inst_2)], Continuous.{max (max u2 u3) u1, max (max u2 u3) u1} (ContinuousMap.{max u3 u2, u1} (Prod.{u2, u3} α β) γ (instTopologicalSpaceProd.{u2, u3} α β _inst_1 _inst_2) _inst_3) (ContinuousMap.{u2, max u1 u3} α (ContinuousMap.{u3, u1} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u3, u1} β γ _inst_2 _inst_3)) (ContinuousMap.compactOpen.{max u2 u3, u1} (Prod.{u2, u3} α β) γ (instTopologicalSpaceProd.{u2, u3} α β _inst_1 _inst_2) _inst_3) (ContinuousMap.compactOpen.{u2, max u3 u1} α (ContinuousMap.{u3, u1} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u3, u1} β γ _inst_2 _inst_3)) (ContinuousMap.curry.{u2, u3, u1} α β γ _inst_1 _inst_2 _inst_3)
Case conversion may be inaccurate. Consider using '#align continuous_map.continuous_curry ContinuousMap.continuous_curryₓ'. -/
/-- The currying process is a continuous map between function spaces. -/
theorem continuous_curry [LocallyCompactSpace (α × β)] :
    Continuous (curry : C(α × β, γ) → C(α, C(β, γ))) :=
  by
  apply continuous_of_continuous_uncurry
  apply continuous_of_continuous_uncurry
  rw [← Homeomorph.comp_continuous_iff' (Homeomorph.prodAssoc _ _ _).symm]
  convert continuous_eval' <;> tidy
#align continuous_map.continuous_curry ContinuousMap.continuous_curry

/- warning: continuous_map.curry_apply -> ContinuousMap.curry_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (f : ContinuousMap.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3) (a : α) (b : β), Eq.{succ u3} γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (ContinuousMap.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) (coeFn.{max (succ u1) (succ (max u2 u3)), max (succ u1) (succ (max u2 u3))} (ContinuousMap.{u1, max u2 u3} α (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u2, u3} β γ _inst_2 _inst_3)) (fun (_x : ContinuousMap.{u1, max u2 u3} α (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u2, u3} β γ _inst_2 _inst_3)) => α -> (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3)) (ContinuousMap.hasCoeToFun.{u1, max u2 u3} α (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u2, u3} β γ _inst_2 _inst_3)) (ContinuousMap.curry.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f) a) b) (coeFn.{max (succ (max u1 u2)) (succ u3), max (succ (max u1 u2)) (succ u3)} (ContinuousMap.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3) (fun (_x : ContinuousMap.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3) => (Prod.{u1, u2} α β) -> γ) (ContinuousMap.hasCoeToFun.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3) f (Prod.mk.{u1, u2} α β a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] (f : ContinuousMap.{max u3 u2, u1} (Prod.{u2, u3} α β) γ (instTopologicalSpaceProd.{u2, u3} α β _inst_1 _inst_2) _inst_3) (a : α) (b : β), Eq.{succ u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : β) => γ) b) (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => ContinuousMap.{u3, u1} β γ _inst_2 _inst_3) a) β (fun (_x : β) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : β) => γ) _x) (ContinuousMapClass.toFunLike.{max u3 u1, u3, u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => ContinuousMap.{u3, u1} β γ _inst_2 _inst_3) a) β γ _inst_2 _inst_3 (ContinuousMap.instContinuousMapClassContinuousMap.{u3, u1} β γ _inst_2 _inst_3)) (FunLike.coe.{max (max (succ u2) (succ u3)) (succ u1), succ u2, max (succ u3) (succ u1)} (ContinuousMap.{u2, max u1 u3} α (ContinuousMap.{u3, u1} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u3, u1} β γ _inst_2 _inst_3)) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => ContinuousMap.{u3, u1} β γ _inst_2 _inst_3) _x) (ContinuousMapClass.toFunLike.{max (max u2 u3) u1, u2, max u3 u1} (ContinuousMap.{u2, max u1 u3} α (ContinuousMap.{u3, u1} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u3, u1} β γ _inst_2 _inst_3)) α (ContinuousMap.{u3, u1} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u3, u1} β γ _inst_2 _inst_3) (ContinuousMap.instContinuousMapClassContinuousMap.{u2, max u3 u1} α (ContinuousMap.{u3, u1} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u3, u1} β γ _inst_2 _inst_3))) (ContinuousMap.curry.{u2, u3, u1} α β γ _inst_1 _inst_2 _inst_3 f) a) b) (FunLike.coe.{max (max (succ u2) (succ u3)) (succ u1), max (succ u2) (succ u3), succ u1} (ContinuousMap.{max u3 u2, u1} (Prod.{u2, u3} α β) γ (instTopologicalSpaceProd.{u2, u3} α β _inst_1 _inst_2) _inst_3) (Prod.{u2, u3} α β) (fun (_x : Prod.{u2, u3} α β) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Prod.{u2, u3} α β) => γ) _x) (ContinuousMapClass.toFunLike.{max (max u2 u3) u1, max u2 u3, u1} (ContinuousMap.{max u3 u2, u1} (Prod.{u2, u3} α β) γ (instTopologicalSpaceProd.{u2, u3} α β _inst_1 _inst_2) _inst_3) (Prod.{u2, u3} α β) γ (instTopologicalSpaceProd.{u2, u3} α β _inst_1 _inst_2) _inst_3 (ContinuousMap.instContinuousMapClassContinuousMap.{max u2 u3, u1} (Prod.{u2, u3} α β) γ (instTopologicalSpaceProd.{u2, u3} α β _inst_1 _inst_2) _inst_3)) f (Prod.mk.{u2, u3} α β a b))
Case conversion may be inaccurate. Consider using '#align continuous_map.curry_apply ContinuousMap.curry_applyₓ'. -/
@[simp]
theorem curry_apply (f : C(α × β, γ)) (a : α) (b : β) : f.curry a b = f (a, b) :=
  rfl
#align continuous_map.curry_apply ContinuousMap.curry_apply

/- warning: continuous_map.continuous_uncurry_of_continuous -> ContinuousMap.continuous_uncurry_of_continuous is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : LocallyCompactSpace.{u2} β _inst_2] (f : ContinuousMap.{u1, max u2 u3} α (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u2, u3} β γ _inst_2 _inst_3)), Continuous.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3 (Function.uncurry.{u1, u2, u3} α β γ (fun (x : α) (y : β) => coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (ContinuousMap.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) (coeFn.{max (succ u1) (succ (max u2 u3)), max (succ u1) (succ (max u2 u3))} (ContinuousMap.{u1, max u2 u3} α (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u2, u3} β γ _inst_2 _inst_3)) (fun (_x : ContinuousMap.{u1, max u2 u3} α (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u2, u3} β γ _inst_2 _inst_3)) => α -> (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3)) (ContinuousMap.hasCoeToFun.{u1, max u2 u3} α (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u2, u3} β γ _inst_2 _inst_3)) f x) y))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] [_inst_4 : LocallyCompactSpace.{u3} β _inst_2] (f : ContinuousMap.{u2, max u1 u3} α (ContinuousMap.{u3, u1} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u3, u1} β γ _inst_2 _inst_3)), Continuous.{max u3 u2, u1} (Prod.{u2, u3} α β) γ (instTopologicalSpaceProd.{u2, u3} α β _inst_1 _inst_2) _inst_3 (Function.uncurry.{u2, u3, u1} α β γ (fun (x : α) (y : β) => FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => ContinuousMap.{u3, u1} β γ _inst_2 _inst_3) x) β (fun (_x : β) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : β) => γ) _x) (ContinuousMapClass.toFunLike.{max u3 u1, u3, u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => ContinuousMap.{u3, u1} β γ _inst_2 _inst_3) x) β γ _inst_2 _inst_3 (ContinuousMap.instContinuousMapClassContinuousMap.{u3, u1} β γ _inst_2 _inst_3)) (FunLike.coe.{max (max (succ u2) (succ u3)) (succ u1), succ u2, max (succ u3) (succ u1)} (ContinuousMap.{u2, max u1 u3} α (ContinuousMap.{u3, u1} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u3, u1} β γ _inst_2 _inst_3)) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => ContinuousMap.{u3, u1} β γ _inst_2 _inst_3) _x) (ContinuousMapClass.toFunLike.{max (max u2 u3) u1, u2, max u3 u1} (ContinuousMap.{u2, max u1 u3} α (ContinuousMap.{u3, u1} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u3, u1} β γ _inst_2 _inst_3)) α (ContinuousMap.{u3, u1} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u3, u1} β γ _inst_2 _inst_3) (ContinuousMap.instContinuousMapClassContinuousMap.{u2, max u3 u1} α (ContinuousMap.{u3, u1} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u3, u1} β γ _inst_2 _inst_3))) f x) y))
Case conversion may be inaccurate. Consider using '#align continuous_map.continuous_uncurry_of_continuous ContinuousMap.continuous_uncurry_of_continuousₓ'. -/
/-- The uncurried form of a continuous map `α → C(β, γ)` is a continuous map `α × β → γ`. -/
theorem continuous_uncurry_of_continuous [LocallyCompactSpace β] (f : C(α, C(β, γ))) :
    Continuous (Function.uncurry fun x y => f x y) :=
  continuous_eval'.comp <| f.Continuous.Prod_map continuous_id
#align continuous_map.continuous_uncurry_of_continuous ContinuousMap.continuous_uncurry_of_continuous

/- warning: continuous_map.uncurry -> ContinuousMap.uncurry is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : LocallyCompactSpace.{u2} β _inst_2], (ContinuousMap.{u1, max u2 u3} α (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u2, u3} β γ _inst_2 _inst_3)) -> (ContinuousMap.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : LocallyCompactSpace.{u2} β _inst_2], (ContinuousMap.{u1, max u3 u2} α (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u2, u3} β γ _inst_2 _inst_3)) -> (ContinuousMap.{max u2 u1, u3} (Prod.{u1, u2} α β) γ (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) _inst_3)
Case conversion may be inaccurate. Consider using '#align continuous_map.uncurry ContinuousMap.uncurryₓ'. -/
/-- The uncurried form of a continuous map `α → C(β, γ)` as a continuous map `α × β → γ` (if `β` is
    locally compact). If `α` is also locally compact, then this is a homeomorphism between the two
    function spaces, see `homeomorph.curry`. -/
@[simps]
def uncurry [LocallyCompactSpace β] (f : C(α, C(β, γ))) : C(α × β, γ) :=
  ⟨_, continuous_uncurry_of_continuous f⟩
#align continuous_map.uncurry ContinuousMap.uncurry

/- warning: continuous_map.continuous_uncurry -> ContinuousMap.continuous_uncurry is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : LocallyCompactSpace.{u1} α _inst_1] [_inst_5 : LocallyCompactSpace.{u2} β _inst_2], Continuous.{max u1 u2 u3, max (max u1 u2) u3} (ContinuousMap.{u1, max u2 u3} α (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u2, u3} β γ _inst_2 _inst_3)) (ContinuousMap.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3) (ContinuousMap.compactOpen.{u1, max u2 u3} α (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u2, u3} β γ _inst_2 _inst_3)) (ContinuousMap.compactOpen.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3) (ContinuousMap.uncurry.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 _inst_5)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] [_inst_4 : LocallyCompactSpace.{u3} α _inst_1] [_inst_5 : LocallyCompactSpace.{u2} β _inst_2], Continuous.{max (max u3 u2) u1, max (max u3 u2) u1} (ContinuousMap.{u3, max u1 u2} α (ContinuousMap.{u2, u1} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u2, u1} β γ _inst_2 _inst_3)) (ContinuousMap.{max u2 u3, u1} (Prod.{u3, u2} α β) γ (instTopologicalSpaceProd.{u3, u2} α β _inst_1 _inst_2) _inst_3) (ContinuousMap.compactOpen.{u3, max u2 u1} α (ContinuousMap.{u2, u1} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u2, u1} β γ _inst_2 _inst_3)) (ContinuousMap.compactOpen.{max u3 u2, u1} (Prod.{u3, u2} α β) γ (instTopologicalSpaceProd.{u3, u2} α β _inst_1 _inst_2) _inst_3) (ContinuousMap.uncurry.{u3, u2, u1} α β γ _inst_1 _inst_2 _inst_3 _inst_5)
Case conversion may be inaccurate. Consider using '#align continuous_map.continuous_uncurry ContinuousMap.continuous_uncurryₓ'. -/
/-- The uncurrying process is a continuous map between function spaces. -/
theorem continuous_uncurry [LocallyCompactSpace α] [LocallyCompactSpace β] :
    Continuous (uncurry : C(α, C(β, γ)) → C(α × β, γ)) :=
  by
  apply continuous_of_continuous_uncurry
  rw [← Homeomorph.comp_continuous_iff' (Homeomorph.prodAssoc _ _ _)]
  apply Continuous.comp continuous_eval' (Continuous.prod_map continuous_eval' continuous_id) <;>
    infer_instance
#align continuous_map.continuous_uncurry ContinuousMap.continuous_uncurry

#print ContinuousMap.const' /-
/-- The family of constant maps: `β → C(α, β)` as a continuous map. -/
def const' : C(β, C(α, β)) :=
  curry ⟨Prod.fst, continuous_fst⟩
#align continuous_map.const' ContinuousMap.const'
-/

/- warning: continuous_map.coe_const' -> ContinuousMap.coe_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], Eq.{max (succ u1) (succ u2)} ((fun (_x : ContinuousMap.{u2, max u1 u2} β (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) _inst_2 (ContinuousMap.compactOpen.{u1, u2} α β _inst_1 _inst_2)) => β -> (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (ContinuousMap.const'.{u1, u2} α β _inst_1 _inst_2)) (coeFn.{max (succ u2) (succ (max u1 u2)), max (succ u2) (succ (max u1 u2))} (ContinuousMap.{u2, max u1 u2} β (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) _inst_2 (ContinuousMap.compactOpen.{u1, u2} α β _inst_1 _inst_2)) (fun (_x : ContinuousMap.{u2, max u1 u2} β (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) _inst_2 (ContinuousMap.compactOpen.{u1, u2} α β _inst_1 _inst_2)) => β -> (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (ContinuousMap.hasCoeToFun.{u2, max u1 u2} β (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) _inst_2 (ContinuousMap.compactOpen.{u1, u2} α β _inst_1 _inst_2)) (ContinuousMap.const'.{u1, u2} α β _inst_1 _inst_2)) (ContinuousMap.const.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β], Eq.{max (succ u2) (succ u1)} (forall (a : β), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : β) => ContinuousMap.{u2, u1} α β _inst_1 _inst_2) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, max (succ u1) (succ u2)} (ContinuousMap.{u1, max u1 u2} β (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) _inst_2 (ContinuousMap.compactOpen.{u2, u1} α β _inst_1 _inst_2)) β (fun (_x : β) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : β) => ContinuousMap.{u2, u1} α β _inst_1 _inst_2) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, max u1 u2} (ContinuousMap.{u1, max u1 u2} β (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) _inst_2 (ContinuousMap.compactOpen.{u2, u1} α β _inst_1 _inst_2)) β (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) _inst_2 (ContinuousMap.compactOpen.{u2, u1} α β _inst_1 _inst_2) (ContinuousMap.instContinuousMapClassContinuousMap.{u1, max u1 u2} β (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) _inst_2 (ContinuousMap.compactOpen.{u2, u1} α β _inst_1 _inst_2))) (ContinuousMap.const'.{u2, u1} α β _inst_1 _inst_2)) (ContinuousMap.const.{u2, u1} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align continuous_map.coe_const' ContinuousMap.coe_const'ₓ'. -/
@[simp]
theorem coe_const' : (const' : β → C(α, β)) = const α :=
  rfl
#align continuous_map.coe_const' ContinuousMap.coe_const'

#print ContinuousMap.continuous_const' /-
theorem continuous_const' : Continuous (const α : β → C(α, β)) :=
  const'.Continuous
#align continuous_map.continuous_const' ContinuousMap.continuous_const'
-/

end Curry

end CompactOpen

end ContinuousMap

open ContinuousMap

namespace Homeomorph

variable {α : Type _} {β : Type _} {γ : Type _}

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

/- warning: homeomorph.curry -> Homeomorph.curry is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : LocallyCompactSpace.{u1} α _inst_1] [_inst_5 : LocallyCompactSpace.{u2} β _inst_2], Homeomorph.{max (max u1 u2) u3, max u1 u2 u3} (ContinuousMap.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3) (ContinuousMap.{u1, max u2 u3} α (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u2, u3} β γ _inst_2 _inst_3)) (ContinuousMap.compactOpen.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3) (ContinuousMap.compactOpen.{u1, max u2 u3} α (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u2, u3} β γ _inst_2 _inst_3))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : LocallyCompactSpace.{u1} α _inst_1] [_inst_5 : LocallyCompactSpace.{u2} β _inst_2], Homeomorph.{max u3 u2 u1, max (max u3 u2) u1} (ContinuousMap.{max u2 u1, u3} (Prod.{u1, u2} α β) γ (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) _inst_3) (ContinuousMap.{u1, max u3 u2} α (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u2, u3} β γ _inst_2 _inst_3)) (ContinuousMap.compactOpen.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) _inst_3) (ContinuousMap.compactOpen.{u1, max u2 u3} α (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) _inst_1 (ContinuousMap.compactOpen.{u2, u3} β γ _inst_2 _inst_3))
Case conversion may be inaccurate. Consider using '#align homeomorph.curry Homeomorph.curryₓ'. -/
/-- Currying as a homeomorphism between the function spaces `C(α × β, γ)` and `C(α, C(β, γ))`. -/
def curry [LocallyCompactSpace α] [LocallyCompactSpace β] : C(α × β, γ) ≃ₜ C(α, C(β, γ)) :=
  ⟨⟨curry, uncurry, by tidy, by tidy⟩, continuous_curry, continuous_uncurry⟩
#align homeomorph.curry Homeomorph.curry

#print Homeomorph.continuousMapOfUnique /-
/-- If `α` has a single element, then `β` is homeomorphic to `C(α, β)`. -/
def continuousMapOfUnique [Unique α] : β ≃ₜ C(α, β)
    where
  toFun := const α
  invFun f := f default
  left_inv a := rfl
  right_inv f := by
    ext
    rw [Unique.eq_default a]
    rfl
  continuous_toFun := continuous_const'
  continuous_invFun := continuous_eval'.comp (continuous_id.prod_mk continuous_const)
#align homeomorph.continuous_map_of_unique Homeomorph.continuousMapOfUnique
-/

/- warning: homeomorph.continuous_map_of_unique_apply -> Homeomorph.continuousMapOfUnique_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : Unique.{succ u1} α] (b : β) (a : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (coeFn.{max (succ u2) (succ (max u1 u2)), max (succ u2) (succ (max u1 u2))} (Homeomorph.{u2, max u1 u2} β (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) _inst_2 (ContinuousMap.compactOpen.{u1, u2} α β _inst_1 _inst_2)) (fun (_x : Homeomorph.{u2, max u1 u2} β (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) _inst_2 (ContinuousMap.compactOpen.{u1, u2} α β _inst_1 _inst_2)) => β -> (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (Homeomorph.hasCoeToFun.{u2, max u1 u2} β (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) _inst_2 (ContinuousMap.compactOpen.{u1, u2} α β _inst_1 _inst_2)) (Homeomorph.continuousMapOfUnique.{u1, u2} α β _inst_1 _inst_2 _inst_4) b) a) b
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_4 : Unique.{succ u2} α] (b : β) (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) a) (FunLike.coe.{max (succ u1) (succ u2), succ u2, succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => ContinuousMap.{u2, u1} α β _inst_1 _inst_2) b) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u2, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => ContinuousMap.{u2, u1} α β _inst_1 _inst_2) b) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, max (succ u1) (succ u2)} (Homeomorph.{u1, max u1 u2} β (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) _inst_2 (ContinuousMap.compactOpen.{u2, u1} α β _inst_1 _inst_2)) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => ContinuousMap.{u2, u1} α β _inst_1 _inst_2) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, max (succ u1) (succ u2)} (Homeomorph.{u1, max u1 u2} β (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) _inst_2 (ContinuousMap.compactOpen.{u2, u1} α β _inst_1 _inst_2)) β (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u1, max (succ u1) (succ u2)} (Homeomorph.{u1, max u1 u2} β (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) _inst_2 (ContinuousMap.compactOpen.{u2, u1} α β _inst_1 _inst_2)) β (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) (Homeomorph.instEquivLikeHomeomorph.{u1, max u1 u2} β (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) _inst_2 (ContinuousMap.compactOpen.{u2, u1} α β _inst_1 _inst_2)))) (Homeomorph.continuousMapOfUnique.{u2, u1} α β _inst_1 _inst_2 _inst_4) b) a) b
Case conversion may be inaccurate. Consider using '#align homeomorph.continuous_map_of_unique_apply Homeomorph.continuousMapOfUnique_applyₓ'. -/
@[simp]
theorem continuousMapOfUnique_apply [Unique α] (b : β) (a : α) : continuousMapOfUnique b a = b :=
  rfl
#align homeomorph.continuous_map_of_unique_apply Homeomorph.continuousMapOfUnique_apply

/- warning: homeomorph.continuous_map_of_unique_symm_apply -> Homeomorph.continuousMapOfUnique_symm_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : Unique.{succ u1} α] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2), Eq.{succ u2} β (coeFn.{max (succ (max u1 u2)) (succ u2), max (succ (max u1 u2)) (succ u2)} (Homeomorph.{max u1 u2, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) β (ContinuousMap.compactOpen.{u1, u2} α β _inst_1 _inst_2) _inst_2) (fun (_x : Homeomorph.{max u1 u2, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) β (ContinuousMap.compactOpen.{u1, u2} α β _inst_1 _inst_2) _inst_2) => (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) -> β) (Homeomorph.hasCoeToFun.{max u1 u2, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) β (ContinuousMap.compactOpen.{u1, u2} α β _inst_1 _inst_2) _inst_2) (Homeomorph.symm.{u2, max u1 u2} β (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) _inst_2 (ContinuousMap.compactOpen.{u1, u2} α β _inst_1 _inst_2) (Homeomorph.continuousMapOfUnique.{u1, u2} α β _inst_1 _inst_2 _inst_4)) f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f (Inhabited.default.{succ u1} α (Unique.inhabited.{succ u1} α _inst_4)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_4 : Unique.{succ u2} α] (f : ContinuousMap.{u2, u1} α β _inst_1 _inst_2), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : ContinuousMap.{u2, u1} α β _inst_1 _inst_2) => β) f) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), succ u1} (Homeomorph.{max u2 u1, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) β (ContinuousMap.compactOpen.{u2, u1} α β _inst_1 _inst_2) _inst_2) (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u2, u1} α β _inst_1 _inst_2) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : ContinuousMap.{u2, u1} α β _inst_1 _inst_2) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), succ u1} (Homeomorph.{max u2 u1, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) β (ContinuousMap.compactOpen.{u2, u1} α β _inst_1 _inst_2) _inst_2) (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), succ u1} (Homeomorph.{max u2 u1, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) β (ContinuousMap.compactOpen.{u2, u1} α β _inst_1 _inst_2) _inst_2) (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) β (Homeomorph.instEquivLikeHomeomorph.{max u2 u1, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) β (ContinuousMap.compactOpen.{u2, u1} α β _inst_1 _inst_2) _inst_2))) (Homeomorph.symm.{u1, max u2 u1} β (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) _inst_2 (ContinuousMap.compactOpen.{u2, u1} α β _inst_1 _inst_2) (Homeomorph.continuousMapOfUnique.{u2, u1} α β _inst_1 _inst_2 _inst_4)) f) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) f (Inhabited.default.{succ u2} α (Unique.instInhabited.{succ u2} α _inst_4)))
Case conversion may be inaccurate. Consider using '#align homeomorph.continuous_map_of_unique_symm_apply Homeomorph.continuousMapOfUnique_symm_applyₓ'. -/
@[simp]
theorem continuousMapOfUnique_symm_apply [Unique α] (f : C(α, β)) :
    continuousMapOfUnique.symm f = f default :=
  rfl
#align homeomorph.continuous_map_of_unique_symm_apply Homeomorph.continuousMapOfUnique_symm_apply

end Homeomorph

section QuotientMap

variable {X₀ X Y Z : Type _} [TopologicalSpace X₀] [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [LocallyCompactSpace Y] {f : X₀ → X}

/- warning: quotient_map.continuous_lift_prod_left -> QuotientMap.continuous_lift_prod_left is a dubious translation:
lean 3 declaration is
  forall {X₀ : Type.{u1}} {X : Type.{u2}} {Y : Type.{u3}} {Z : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} X₀] [_inst_2 : TopologicalSpace.{u2} X] [_inst_3 : TopologicalSpace.{u3} Y] [_inst_4 : TopologicalSpace.{u4} Z] [_inst_5 : LocallyCompactSpace.{u3} Y _inst_3] {f : X₀ -> X}, (QuotientMap.{u1, u2} X₀ X _inst_1 _inst_2 f) -> (forall {g : (Prod.{u2, u3} X Y) -> Z}, (Continuous.{max u1 u3, u4} (Prod.{u1, u3} X₀ Y) Z (Prod.topologicalSpace.{u1, u3} X₀ Y _inst_1 _inst_3) _inst_4 (fun (p : Prod.{u1, u3} X₀ Y) => g (Prod.mk.{u2, u3} X Y (f (Prod.fst.{u1, u3} X₀ Y p)) (Prod.snd.{u1, u3} X₀ Y p)))) -> (Continuous.{max u2 u3, u4} (Prod.{u2, u3} X Y) Z (Prod.topologicalSpace.{u2, u3} X Y _inst_2 _inst_3) _inst_4 g))
but is expected to have type
  forall {X₀ : Type.{u4}} {X : Type.{u3}} {Y : Type.{u2}} {Z : Type.{u1}} [_inst_1 : TopologicalSpace.{u4} X₀] [_inst_2 : TopologicalSpace.{u3} X] [_inst_3 : TopologicalSpace.{u2} Y] [_inst_4 : TopologicalSpace.{u1} Z] [_inst_5 : LocallyCompactSpace.{u2} Y _inst_3] {f : X₀ -> X}, (QuotientMap.{u4, u3} X₀ X _inst_1 _inst_2 f) -> (forall {g : (Prod.{u3, u2} X Y) -> Z}, (Continuous.{max u4 u2, u1} (Prod.{u4, u2} X₀ Y) Z (instTopologicalSpaceProd.{u4, u2} X₀ Y _inst_1 _inst_3) _inst_4 (fun (p : Prod.{u4, u2} X₀ Y) => g (Prod.mk.{u3, u2} X Y (f (Prod.fst.{u4, u2} X₀ Y p)) (Prod.snd.{u4, u2} X₀ Y p)))) -> (Continuous.{max u3 u2, u1} (Prod.{u3, u2} X Y) Z (instTopologicalSpaceProd.{u3, u2} X Y _inst_2 _inst_3) _inst_4 g))
Case conversion may be inaccurate. Consider using '#align quotient_map.continuous_lift_prod_left QuotientMap.continuous_lift_prod_leftₓ'. -/
theorem QuotientMap.continuous_lift_prod_left (hf : QuotientMap f) {g : X × Y → Z}
    (hg : Continuous fun p : X₀ × Y => g (f p.1, p.2)) : Continuous g :=
  by
  let Gf : C(X₀, C(Y, Z)) := ContinuousMap.curry ⟨_, hg⟩
  have h : ∀ x : X, Continuous fun y => g (x, y) :=
    by
    intro x
    obtain ⟨x₀, rfl⟩ := hf.surjective x
    exact (Gf x₀).Continuous
  let G : X → C(Y, Z) := fun x => ⟨_, h x⟩
  have : Continuous G := by
    rw [hf.continuous_iff]
    exact Gf.continuous
  convert ContinuousMap.continuous_uncurry_of_continuous ⟨G, this⟩
  ext x
  cases x
  rfl
#align quotient_map.continuous_lift_prod_left QuotientMap.continuous_lift_prod_left

/- warning: quotient_map.continuous_lift_prod_right -> QuotientMap.continuous_lift_prod_right is a dubious translation:
lean 3 declaration is
  forall {X₀ : Type.{u1}} {X : Type.{u2}} {Y : Type.{u3}} {Z : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} X₀] [_inst_2 : TopologicalSpace.{u2} X] [_inst_3 : TopologicalSpace.{u3} Y] [_inst_4 : TopologicalSpace.{u4} Z] [_inst_5 : LocallyCompactSpace.{u3} Y _inst_3] {f : X₀ -> X}, (QuotientMap.{u1, u2} X₀ X _inst_1 _inst_2 f) -> (forall {g : (Prod.{u3, u2} Y X) -> Z}, (Continuous.{max u3 u1, u4} (Prod.{u3, u1} Y X₀) Z (Prod.topologicalSpace.{u3, u1} Y X₀ _inst_3 _inst_1) _inst_4 (fun (p : Prod.{u3, u1} Y X₀) => g (Prod.mk.{u3, u2} Y X (Prod.fst.{u3, u1} Y X₀ p) (f (Prod.snd.{u3, u1} Y X₀ p))))) -> (Continuous.{max u3 u2, u4} (Prod.{u3, u2} Y X) Z (Prod.topologicalSpace.{u3, u2} Y X _inst_3 _inst_2) _inst_4 g))
but is expected to have type
  forall {X₀ : Type.{u4}} {X : Type.{u3}} {Y : Type.{u2}} {Z : Type.{u1}} [_inst_1 : TopologicalSpace.{u4} X₀] [_inst_2 : TopologicalSpace.{u3} X] [_inst_3 : TopologicalSpace.{u2} Y] [_inst_4 : TopologicalSpace.{u1} Z] [_inst_5 : LocallyCompactSpace.{u2} Y _inst_3] {f : X₀ -> X}, (QuotientMap.{u4, u3} X₀ X _inst_1 _inst_2 f) -> (forall {g : (Prod.{u2, u3} Y X) -> Z}, (Continuous.{max u4 u2, u1} (Prod.{u2, u4} Y X₀) Z (instTopologicalSpaceProd.{u2, u4} Y X₀ _inst_3 _inst_1) _inst_4 (fun (p : Prod.{u2, u4} Y X₀) => g (Prod.mk.{u2, u3} Y X (Prod.fst.{u2, u4} Y X₀ p) (f (Prod.snd.{u2, u4} Y X₀ p))))) -> (Continuous.{max u3 u2, u1} (Prod.{u2, u3} Y X) Z (instTopologicalSpaceProd.{u2, u3} Y X _inst_3 _inst_2) _inst_4 g))
Case conversion may be inaccurate. Consider using '#align quotient_map.continuous_lift_prod_right QuotientMap.continuous_lift_prod_rightₓ'. -/
theorem QuotientMap.continuous_lift_prod_right (hf : QuotientMap f) {g : Y × X → Z}
    (hg : Continuous fun p : Y × X₀ => g (p.1, f p.2)) : Continuous g :=
  by
  have : Continuous fun p : X₀ × Y => g ((Prod.swap p).1, f (Prod.swap p).2) :=
    hg.comp continuous_swap
  have : Continuous fun p : X₀ × Y => (g ∘ Prod.swap) (f p.1, p.2) := this
  convert (hf.continuous_lift_prod_left this).comp continuous_swap
  ext x
  simp
#align quotient_map.continuous_lift_prod_right QuotientMap.continuous_lift_prod_right

end QuotientMap

