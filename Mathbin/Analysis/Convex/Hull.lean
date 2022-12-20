/-
Copyright (c) 2020 Yury Kudriashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudriashov, Yaël Dillies

! This file was ported from Lean 3 source module analysis.convex.hull
! leanprover-community/mathlib commit 550b58538991c8977703fdeb7c9d51a5aa27df11
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Convex.Basic
import Mathbin.Order.Closure

/-!
# Convex hull

This file defines the convex hull of a set `s` in a module. `convex_hull 𝕜 s` is the smallest convex
set containing `s`. In order theory speak, this is a closure operator.

## Implementation notes

`convex_hull` is defined as a closure operator. This gives access to the `closure_operator` API
while the impact on writing code is minimal as `convex_hull 𝕜 s` is automatically elaborated as
`⇑(convex_hull 𝕜) s`.
-/


open Set

open Pointwise

variable {𝕜 E F : Type _}

section convexHull

section OrderedSemiring

variable [OrderedSemiring 𝕜]

section AddCommMonoid

variable (𝕜) [AddCommMonoid E] [AddCommMonoid F] [Module 𝕜 E] [Module 𝕜 F]

/-- The convex hull of a set `s` is the minimal convex set that includes `s`. -/
def convexHull : ClosureOperator (Set E) :=
  ClosureOperator.mk₃ (fun s => ⋂ (t : Set E) (hst : s ⊆ t) (ht : Convex 𝕜 t), t) (Convex 𝕜)
    (fun s => Set.subset_Inter fun t => Set.subset_Inter fun hst => Set.subset_Inter fun ht => hst)
    (fun s => convex_Inter fun t => convex_Inter fun ht => convex_Inter id) fun s t hst ht =>
    Set.Inter_subset_of_subset t <| Set.Inter_subset_of_subset hst <| Set.Inter_subset _ ht
#align convex_hull convexHull

variable (s : Set E)

theorem subset_convex_hull : s ⊆ convexHull 𝕜 s :=
  (convexHull 𝕜).le_closure s
#align subset_convex_hull subset_convex_hull

theorem convex_convex_hull : Convex 𝕜 (convexHull 𝕜 s) :=
  ClosureOperator.closure_mem_mk₃ s
#align convex_convex_hull convex_convex_hull

theorem convex_hull_eq_Inter : convexHull 𝕜 s = ⋂ (t : Set E) (hst : s ⊆ t) (ht : Convex 𝕜 t), t :=
  rfl
#align convex_hull_eq_Inter convex_hull_eq_Inter

variable {𝕜 s} {t : Set E} {x y : E}

theorem mem_convex_hull_iff : x ∈ convexHull 𝕜 s ↔ ∀ t, s ⊆ t → Convex 𝕜 t → x ∈ t := by
  simp_rw [convex_hull_eq_Inter, mem_Inter]
#align mem_convex_hull_iff mem_convex_hull_iff

theorem convex_hull_min (hst : s ⊆ t) (ht : Convex 𝕜 t) : convexHull 𝕜 s ⊆ t :=
  ClosureOperator.closure_le_mk₃_iff (show s ≤ t from hst) ht
#align convex_hull_min convex_hull_min

theorem Convex.convex_hull_subset_iff (ht : Convex 𝕜 t) : convexHull 𝕜 s ⊆ t ↔ s ⊆ t :=
  ⟨(subset_convex_hull _ _).trans, fun h => convex_hull_min h ht⟩
#align convex.convex_hull_subset_iff Convex.convex_hull_subset_iff

@[mono]
theorem convex_hull_mono (hst : s ⊆ t) : convexHull 𝕜 s ⊆ convexHull 𝕜 t :=
  (convexHull 𝕜).Monotone hst
#align convex_hull_mono convex_hull_mono

theorem Convex.convex_hull_eq (hs : Convex 𝕜 s) : convexHull 𝕜 s = s :=
  ClosureOperator.mem_mk₃_closed hs
#align convex.convex_hull_eq Convex.convex_hull_eq

@[simp]
theorem convex_hull_univ : convexHull 𝕜 (univ : Set E) = univ :=
  ClosureOperator.closure_top (convexHull 𝕜)
#align convex_hull_univ convex_hull_univ

@[simp]
theorem convex_hull_empty : convexHull 𝕜 (∅ : Set E) = ∅ :=
  convex_empty.convex_hull_eq
#align convex_hull_empty convex_hull_empty

@[simp]
theorem convex_hull_empty_iff : convexHull 𝕜 s = ∅ ↔ s = ∅ := by
  constructor
  · intro h
    rw [← Set.subset_empty_iff, ← h]
    exact subset_convex_hull 𝕜 _
  · rintro rfl
    exact convex_hull_empty
#align convex_hull_empty_iff convex_hull_empty_iff

@[simp]
theorem convex_hull_nonempty_iff : (convexHull 𝕜 s).Nonempty ↔ s.Nonempty := by
  rw [nonempty_iff_ne_empty, nonempty_iff_ne_empty, Ne.def, Ne.def]
  exact not_congr convex_hull_empty_iff
#align convex_hull_nonempty_iff convex_hull_nonempty_iff

alias convex_hull_nonempty_iff ↔ _ Set.Nonempty.convex_hull

attribute [protected] Set.Nonempty.convex_hull

theorem segment_subset_convex_hull (hx : x ∈ s) (hy : y ∈ s) : segment 𝕜 x y ⊆ convexHull 𝕜 s :=
  (convex_convex_hull _ _).segment_subset (subset_convex_hull _ _ hx) (subset_convex_hull _ _ hy)
#align segment_subset_convex_hull segment_subset_convex_hull

@[simp]
theorem convex_hull_singleton (x : E) : convexHull 𝕜 ({x} : Set E) = {x} :=
  (convex_singleton x).convex_hull_eq
#align convex_hull_singleton convex_hull_singleton

@[simp]
theorem convex_hull_pair (x y : E) : convexHull 𝕜 {x, y} = segment 𝕜 x y := by
  refine'
    (convex_hull_min _ <| convex_segment _ _).antisymm
      (segment_subset_convex_hull (mem_insert _ _) <| mem_insert_of_mem _ <| mem_singleton _)
  rw [insert_subset, singleton_subset_iff]
  exact ⟨left_mem_segment _ _ _, right_mem_segment _ _ _⟩
#align convex_hull_pair convex_hull_pair

theorem convex_hull_convex_hull_union_left (s t : Set E) :
    convexHull 𝕜 (convexHull 𝕜 s ∪ t) = convexHull 𝕜 (s ∪ t) :=
  ClosureOperator.closure_sup_closure_left _ _ _
#align convex_hull_convex_hull_union_left convex_hull_convex_hull_union_left

theorem convex_hull_convex_hull_union_right (s t : Set E) :
    convexHull 𝕜 (s ∪ convexHull 𝕜 t) = convexHull 𝕜 (s ∪ t) :=
  ClosureOperator.closure_sup_closure_right _ _ _
#align convex_hull_convex_hull_union_right convex_hull_convex_hull_union_right

theorem Convex.convex_remove_iff_not_mem_convex_hull_remove {s : Set E} (hs : Convex 𝕜 s) (x : E) :
    Convex 𝕜 (s \ {x}) ↔ x ∉ convexHull 𝕜 (s \ {x}) := by
  constructor
  · rintro hsx hx
    rw [hsx.convex_hull_eq] at hx
    exact hx.2 (mem_singleton _)
  rintro hx
  suffices h : s \ {x} = convexHull 𝕜 (s \ {x}); · convert convex_convex_hull 𝕜 _
  exact
    subset.antisymm (subset_convex_hull 𝕜 _) fun y hy =>
      ⟨convex_hull_min (diff_subset _ _) hs hy, by
        rintro (rfl : y = x)
        exact hx hy⟩
#align
  convex.convex_remove_iff_not_mem_convex_hull_remove Convex.convex_remove_iff_not_mem_convex_hull_remove

theorem IsLinearMap.convex_hull_image {f : E → F} (hf : IsLinearMap 𝕜 f) (s : Set E) :
    convexHull 𝕜 (f '' s) = f '' convexHull 𝕜 s :=
  Set.Subset.antisymm
    (convex_hull_min (image_subset _ (subset_convex_hull 𝕜 s)) <|
      (convex_convex_hull 𝕜 s).is_linear_image hf)
    (image_subset_iff.2 <|
      convex_hull_min (image_subset_iff.1 <| subset_convex_hull 𝕜 _)
        ((convex_convex_hull 𝕜 _).is_linear_preimage hf))
#align is_linear_map.convex_hull_image IsLinearMap.convex_hull_image

theorem LinearMap.convex_hull_image (f : E →ₗ[𝕜] F) (s : Set E) :
    convexHull 𝕜 (f '' s) = f '' convexHull 𝕜 s :=
  f.is_linear.convex_hull_image s
#align linear_map.convex_hull_image LinearMap.convex_hull_image

end AddCommMonoid

end OrderedSemiring

section OrderedCommSemiring

variable [OrderedCommSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]

theorem convex_hull_smul (a : 𝕜) (s : Set E) : convexHull 𝕜 (a • s) = a • convexHull 𝕜 s :=
  (LinearMap.lsmul _ _ a).convex_hull_image _
#align convex_hull_smul convex_hull_smul

end OrderedCommSemiring

section OrderedRing

variable [OrderedRing 𝕜]

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F] (s : Set E)

theorem AffineMap.image_convex_hull (f : E →ᵃ[𝕜] F) : f '' convexHull 𝕜 s = convexHull 𝕜 (f '' s) :=
  by 
  apply Set.Subset.antisymm
  · rw [Set.image_subset_iff]
    refine' convex_hull_min _ ((convex_convex_hull 𝕜 (⇑f '' s)).affine_preimage f)
    rw [← Set.image_subset_iff]
    exact subset_convex_hull 𝕜 (f '' s)
  ·
    exact
      convex_hull_min (Set.image_subset _ (subset_convex_hull 𝕜 s))
        ((convex_convex_hull 𝕜 s).affine_image f)
#align affine_map.image_convex_hull AffineMap.image_convex_hull

theorem convex_hull_subset_affine_span : convexHull 𝕜 s ⊆ (affineSpan 𝕜 s : Set E) :=
  convex_hull_min (subset_affine_span 𝕜 s) (affineSpan 𝕜 s).Convex
#align convex_hull_subset_affine_span convex_hull_subset_affine_span

@[simp]
theorem affine_span_convex_hull : affineSpan 𝕜 (convexHull 𝕜 s) = affineSpan 𝕜 s := by
  refine' le_antisymm _ (affine_span_mono 𝕜 (subset_convex_hull 𝕜 s))
  rw [affine_span_le]
  exact convex_hull_subset_affine_span s
#align affine_span_convex_hull affine_span_convex_hull

theorem convex_hull_neg (s : Set E) : convexHull 𝕜 (-s) = -convexHull 𝕜 s := by
  simp_rw [← image_neg]
  exact (AffineMap.image_convex_hull _ <| -1).symm
#align convex_hull_neg convex_hull_neg

end AddCommGroup

end OrderedRing

end convexHull

