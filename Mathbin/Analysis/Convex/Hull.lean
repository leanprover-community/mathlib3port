/-
Copyright (c) 2020 Yury Kudriashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudriashov, Yaël Dillies
-/
import Analysis.Convex.Basic
import Order.Closure

#align_import analysis.convex.hull from "leanprover-community/mathlib"@"92bd7b1ffeb306a89f450bee126ddd8a284c259d"

/-!
# Convex hull

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the convex hull of a set `s` in a module. `convex_hull 𝕜 s` is the smallest convex
set containing `s`. In order theory speak, this is a closure operator.

## Implementation notes

`convex_hull` is defined as a closure operator. This gives access to the `closure_operator` API
while the impact on writing code is minimal as `convex_hull 𝕜 s` is automatically elaborated as
`⇑(convex_hull 𝕜) s`.
-/


open Set

open scoped Pointwise

variable {𝕜 E F : Type _}

section convexHull

section OrderedSemiring

variable [OrderedSemiring 𝕜]

section AddCommMonoid

variable (𝕜) [AddCommMonoid E] [AddCommMonoid F] [Module 𝕜 E] [Module 𝕜 F]

#print convexHull /-
/-- The convex hull of a set `s` is the minimal convex set that includes `s`. -/
def convexHull : ClosureOperator (Set E) :=
  ClosureOperator.ofPred (fun s => ⋂ (t : Set E) (hst : s ⊆ t) (ht : Convex 𝕜 t), t) (Convex 𝕜)
    (fun s =>
      Set.subset_iInter fun t => Set.subset_iInter fun hst => Set.subset_iInter fun ht => hst)
    (fun s => convex_iInter fun t => convex_iInter fun ht => convex_iInter id) fun s t hst ht =>
    Set.iInter_subset_of_subset t <| Set.iInter_subset_of_subset hst <| Set.iInter_subset _ ht
#align convex_hull convexHull
-/

variable (s : Set E)

#print subset_convexHull /-
theorem subset_convexHull : s ⊆ convexHull 𝕜 s :=
  (convexHull 𝕜).le_closure s
#align subset_convex_hull subset_convexHull
-/

#print convex_convexHull /-
theorem convex_convexHull : Convex 𝕜 (convexHull 𝕜 s) :=
  ClosureOperator.closure_mem_ofPred s
#align convex_convex_hull convex_convexHull
-/

#print convexHull_eq_iInter /-
theorem convexHull_eq_iInter : convexHull 𝕜 s = ⋂ (t : Set E) (hst : s ⊆ t) (ht : Convex 𝕜 t), t :=
  rfl
#align convex_hull_eq_Inter convexHull_eq_iInter
-/

variable {𝕜 s} {t : Set E} {x y : E}

#print mem_convexHull_iff /-
theorem mem_convexHull_iff : x ∈ convexHull 𝕜 s ↔ ∀ t, s ⊆ t → Convex 𝕜 t → x ∈ t := by
  simp_rw [convexHull_eq_iInter, mem_Inter]
#align mem_convex_hull_iff mem_convexHull_iff
-/

#print convexHull_min /-
theorem convexHull_min (hst : s ⊆ t) (ht : Convex 𝕜 t) : convexHull 𝕜 s ⊆ t :=
  ClosureOperator.closure_le_ofPred_iff (show s ≤ t from hst) ht
#align convex_hull_min convexHull_min
-/

#print Convex.convexHull_subset_iff /-
theorem Convex.convexHull_subset_iff (ht : Convex 𝕜 t) : convexHull 𝕜 s ⊆ t ↔ s ⊆ t :=
  ⟨(subset_convexHull _ _).trans, fun h => convexHull_min h ht⟩
#align convex.convex_hull_subset_iff Convex.convexHull_subset_iff
-/

#print convexHull_mono /-
@[mono]
theorem convexHull_mono (hst : s ⊆ t) : convexHull 𝕜 s ⊆ convexHull 𝕜 t :=
  (convexHull 𝕜).Monotone hst
#align convex_hull_mono convexHull_mono
-/

#print Convex.convexHull_eq /-
theorem Convex.convexHull_eq (hs : Convex 𝕜 s) : convexHull 𝕜 s = s :=
  ClosureOperator.ofPred_isClosed hs
#align convex.convex_hull_eq Convex.convexHull_eq
-/

#print convexHull_univ /-
@[simp]
theorem convexHull_univ : convexHull 𝕜 (univ : Set E) = univ :=
  ClosureOperator.closure_top (convexHull 𝕜)
#align convex_hull_univ convexHull_univ
-/

#print convexHull_empty /-
@[simp]
theorem convexHull_empty : convexHull 𝕜 (∅ : Set E) = ∅ :=
  convex_empty.convexHull_eq
#align convex_hull_empty convexHull_empty
-/

#print convexHull_empty_iff /-
@[simp]
theorem convexHull_empty_iff : convexHull 𝕜 s = ∅ ↔ s = ∅ :=
  by
  constructor
  · intro h
    rw [← Set.subset_empty_iff, ← h]
    exact subset_convexHull 𝕜 _
  · rintro rfl
    exact convexHull_empty
#align convex_hull_empty_iff convexHull_empty_iff
-/

#print convexHull_nonempty_iff /-
@[simp]
theorem convexHull_nonempty_iff : (convexHull 𝕜 s).Nonempty ↔ s.Nonempty :=
  by
  rw [nonempty_iff_ne_empty, nonempty_iff_ne_empty, Ne.def, Ne.def]
  exact not_congr convexHull_empty_iff
#align convex_hull_nonempty_iff convexHull_nonempty_iff
-/

alias ⟨_, Set.Nonempty.convexHull⟩ := convexHull_nonempty_iff
#align set.nonempty.convex_hull Set.Nonempty.convexHull

attribute [protected] Set.Nonempty.convexHull

#print segment_subset_convexHull /-
theorem segment_subset_convexHull (hx : x ∈ s) (hy : y ∈ s) : segment 𝕜 x y ⊆ convexHull 𝕜 s :=
  (convex_convexHull _ _).segment_subset (subset_convexHull _ _ hx) (subset_convexHull _ _ hy)
#align segment_subset_convex_hull segment_subset_convexHull
-/

#print convexHull_singleton /-
@[simp]
theorem convexHull_singleton (x : E) : convexHull 𝕜 ({x} : Set E) = {x} :=
  (convex_singleton x).convexHull_eq
#align convex_hull_singleton convexHull_singleton
-/

#print convexHull_zero /-
@[simp]
theorem convexHull_zero : convexHull 𝕜 (0 : Set E) = 0 :=
  convexHull_singleton 0
#align convex_hull_zero convexHull_zero
-/

#print convexHull_pair /-
@[simp]
theorem convexHull_pair (x y : E) : convexHull 𝕜 {x, y} = segment 𝕜 x y :=
  by
  refine'
    (convexHull_min _ <| convex_segment _ _).antisymm
      (segment_subset_convexHull (mem_insert _ _) <| mem_insert_of_mem _ <| mem_singleton _)
  rw [insert_subset, singleton_subset_iff]
  exact ⟨left_mem_segment _ _ _, right_mem_segment _ _ _⟩
#align convex_hull_pair convexHull_pair
-/

#print convexHull_convexHull_union_left /-
theorem convexHull_convexHull_union_left (s t : Set E) :
    convexHull 𝕜 (convexHull 𝕜 s ∪ t) = convexHull 𝕜 (s ∪ t) :=
  ClosureOperator.closure_sup_closure_left _ _ _
#align convex_hull_convex_hull_union_left convexHull_convexHull_union_left
-/

#print convexHull_convexHull_union_right /-
theorem convexHull_convexHull_union_right (s t : Set E) :
    convexHull 𝕜 (s ∪ convexHull 𝕜 t) = convexHull 𝕜 (s ∪ t) :=
  ClosureOperator.closure_sup_closure_right _ _ _
#align convex_hull_convex_hull_union_right convexHull_convexHull_union_right
-/

#print Convex.convex_remove_iff_not_mem_convexHull_remove /-
theorem Convex.convex_remove_iff_not_mem_convexHull_remove {s : Set E} (hs : Convex 𝕜 s) (x : E) :
    Convex 𝕜 (s \ {x}) ↔ x ∉ convexHull 𝕜 (s \ {x}) :=
  by
  constructor
  · rintro hsx hx
    rw [hsx.convex_hull_eq] at hx
    exact hx.2 (mem_singleton _)
  rintro hx
  suffices h : s \ {x} = convexHull 𝕜 (s \ {x}); · convert convex_convexHull 𝕜 _
  exact
    subset.antisymm (subset_convexHull 𝕜 _) fun y hy =>
      ⟨convexHull_min (diff_subset _ _) hs hy, by rintro (rfl : y = x); exact hx hy⟩
#align convex.convex_remove_iff_not_mem_convex_hull_remove Convex.convex_remove_iff_not_mem_convexHull_remove
-/

#print IsLinearMap.image_convexHull /-
theorem IsLinearMap.image_convexHull {f : E → F} (hf : IsLinearMap 𝕜 f) (s : Set E) :
    convexHull 𝕜 (f '' s) = f '' convexHull 𝕜 s :=
  Set.Subset.antisymm
    (convexHull_min (image_subset _ (subset_convexHull 𝕜 s)) <|
      (convex_convexHull 𝕜 s).is_linear_image hf)
    (image_subset_iff.2 <|
      convexHull_min (image_subset_iff.1 <| subset_convexHull 𝕜 _)
        ((convex_convexHull 𝕜 _).is_linear_preimage hf))
#align is_linear_map.convex_hull_image IsLinearMap.image_convexHull
-/

#print LinearMap.image_convexHull /-
theorem LinearMap.image_convexHull (f : E →ₗ[𝕜] F) (s : Set E) :
    convexHull 𝕜 (f '' s) = f '' convexHull 𝕜 s :=
  f.isLinear.image_convexHull s
#align linear_map.convex_hull_image LinearMap.image_convexHull
-/

end AddCommMonoid

end OrderedSemiring

section OrderedCommSemiring

variable [OrderedCommSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]

#print convexHull_smul /-
theorem convexHull_smul (a : 𝕜) (s : Set E) : convexHull 𝕜 (a • s) = a • convexHull 𝕜 s :=
  (LinearMap.lsmul _ _ a).image_convexHull _
#align convex_hull_smul convexHull_smul
-/

end OrderedCommSemiring

section OrderedRing

variable [OrderedRing 𝕜]

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F] (s : Set E)

#print AffineMap.image_convexHull /-
theorem AffineMap.image_convexHull (f : E →ᵃ[𝕜] F) : f '' convexHull 𝕜 s = convexHull 𝕜 (f '' s) :=
  by
  apply Set.Subset.antisymm
  · rw [Set.image_subset_iff]
    refine' convexHull_min _ ((convex_convexHull 𝕜 (⇑f '' s)).affine_preimage f)
    rw [← Set.image_subset_iff]
    exact subset_convexHull 𝕜 (f '' s)
  ·
    exact
      convexHull_min (Set.image_subset _ (subset_convexHull 𝕜 s))
        ((convex_convexHull 𝕜 s).affine_image f)
#align affine_map.image_convex_hull AffineMap.image_convexHull
-/

#print convexHull_subset_affineSpan /-
theorem convexHull_subset_affineSpan : convexHull 𝕜 s ⊆ (affineSpan 𝕜 s : Set E) :=
  convexHull_min (subset_affineSpan 𝕜 s) (affineSpan 𝕜 s).Convex
#align convex_hull_subset_affine_span convexHull_subset_affineSpan
-/

#print affineSpan_convexHull /-
@[simp]
theorem affineSpan_convexHull : affineSpan 𝕜 (convexHull 𝕜 s) = affineSpan 𝕜 s :=
  by
  refine' le_antisymm _ (affineSpan_mono 𝕜 (subset_convexHull 𝕜 s))
  rw [affineSpan_le]
  exact convexHull_subset_affineSpan s
#align affine_span_convex_hull affineSpan_convexHull
-/

#print convexHull_neg /-
theorem convexHull_neg (s : Set E) : convexHull 𝕜 (-s) = -convexHull 𝕜 s := by
  simp_rw [← image_neg]; exact (AffineMap.image_convexHull _ <| -1).symm
#align convex_hull_neg convexHull_neg
-/

end AddCommGroup

end OrderedRing

end convexHull

