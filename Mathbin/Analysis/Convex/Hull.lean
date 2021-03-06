/-
Copyright (c) 2020 Yury Kudriashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudriashov, YaΓ«l Dillies
-/
import Mathbin.Analysis.Convex.Basic
import Mathbin.Order.Closure

/-!
# Convex hull

This file defines the convex hull of a set `s` in a module. `convex_hull π s` is the smallest convex
set containing `s`. In order theory speak, this is a closure operator.

## Implementation notes

`convex_hull` is defined as a closure operator. This gives access to the `closure_operator` API
while the impact on writing code is minimal as `convex_hull π s` is automatically elaborated as
`β(convex_hull π) s`.
-/


open Set

open Pointwise

variable {π E F : Type _}

section convexHull

section OrderedSemiring

variable [OrderedSemiring π]

section AddCommMonoidβ

variable (π) [AddCommMonoidβ E] [AddCommMonoidβ F] [Module π E] [Module π F]

/-- The convex hull of a set `s` is the minimal convex set that includes `s`. -/
def convexHull : ClosureOperator (Set E) :=
  ClosureOperator.mkβ (fun s => β (t : Set E) (hst : s β t) (ht : Convex π t), t) (Convex π)
    (fun s => Set.subset_Inter fun t => Set.subset_Inter fun hst => Set.subset_Inter fun ht => hst)
    (fun s => convex_Inter fun t => convex_Inter fun ht => convex_Inter id) fun s t hst ht =>
    Set.Inter_subset_of_subset t <| Set.Inter_subset_of_subset hst <| Set.Inter_subset _ ht

variable (s : Set E)

theorem subset_convex_hull : s β convexHull π s :=
  (convexHull π).le_closure s

theorem convex_convex_hull : Convex π (convexHull π s) :=
  ClosureOperator.closure_mem_mkβ s

theorem convex_hull_eq_Inter : convexHull π s = β (t : Set E) (hst : s β t) (ht : Convex π t), t :=
  rfl

variable {π s} {t : Set E} {x y : E}

theorem mem_convex_hull_iff : x β convexHull π s β β t, s β t β Convex π t β x β t := by
  simp_rw [convex_hull_eq_Inter, mem_Inter]

theorem convex_hull_min (hst : s β t) (ht : Convex π t) : convexHull π s β t :=
  ClosureOperator.closure_le_mkβ_iff (show s β€ t from hst) ht

theorem Convex.convex_hull_subset_iff (ht : Convex π t) : convexHull π s β t β s β t :=
  β¨(subset_convex_hull _ _).trans, fun h => convex_hull_min h htβ©

@[mono]
theorem convex_hull_mono (hst : s β t) : convexHull π s β convexHull π t :=
  (convexHull π).Monotone hst

theorem Convex.convex_hull_eq (hs : Convex π s) : convexHull π s = s :=
  ClosureOperator.mem_mkβ_closed hs

@[simp]
theorem convex_hull_univ : convexHull π (Univ : Set E) = univ :=
  ClosureOperator.closure_top (convexHull π)

@[simp]
theorem convex_hull_empty : convexHull π (β : Set E) = β :=
  convex_empty.convex_hull_eq

@[simp]
theorem convex_hull_empty_iff : convexHull π s = β β s = β := by
  constructor
  Β· intro h
    rw [β Set.subset_empty_iff, β h]
    exact subset_convex_hull π _
    
  Β· rintro rfl
    exact convex_hull_empty
    

@[simp]
theorem convex_hull_nonempty_iff : (convexHull π s).Nonempty β s.Nonempty := by
  rw [β ne_empty_iff_nonempty, β ne_empty_iff_nonempty, Ne.def, Ne.def]
  exact not_congr convex_hull_empty_iff

alias convex_hull_nonempty_iff β _ Set.Nonempty.convex_hull

attribute [protected] Set.Nonempty.convex_hull

theorem segment_subset_convex_hull (hx : x β s) (hy : y β s) : Segment π x y β convexHull π s :=
  (convex_convex_hull _ _).segment_subset (subset_convex_hull _ _ hx) (subset_convex_hull _ _ hy)

@[simp]
theorem convex_hull_singleton (x : E) : convexHull π ({x} : Set E) = {x} :=
  (convex_singleton x).convex_hull_eq

@[simp]
theorem convex_hull_pair (x y : E) : convexHull π {x, y} = Segment π x y := by
  refine'
    (convex_hull_min _ <| convex_segment _ _).antisymm
      (segment_subset_convex_hull (mem_insert _ _) <| mem_insert_of_mem _ <| mem_singleton _)
  rw [insert_subset, singleton_subset_iff]
  exact β¨left_mem_segment _ _ _, right_mem_segment _ _ _β©

theorem convex_hull_convex_hull_union_left (s t : Set E) : convexHull π (convexHull π s βͺ t) = convexHull π (s βͺ t) :=
  ClosureOperator.closure_sup_closure_left _ _ _

theorem convex_hull_convex_hull_union_right (s t : Set E) : convexHull π (s βͺ convexHull π t) = convexHull π (s βͺ t) :=
  ClosureOperator.closure_sup_closure_right _ _ _

theorem Convex.convex_remove_iff_not_mem_convex_hull_remove {s : Set E} (hs : Convex π s) (x : E) :
    Convex π (s \ {x}) β x β convexHull π (s \ {x}) := by
  constructor
  Β· rintro hsx hx
    rw [hsx.convex_hull_eq] at hx
    exact hx.2 (mem_singleton _)
    
  rintro hx
  suffices h : s \ {x} = convexHull π (s \ {x})
  Β· convert convex_convex_hull π _
    
  exact
    subset.antisymm (subset_convex_hull π _) fun y hy =>
      β¨convex_hull_min (diff_subset _ _) hs hy, by
        rintro (rfl : y = x)
        exact hx hyβ©

theorem IsLinearMap.convex_hull_image {f : E β F} (hf : IsLinearMap π f) (s : Set E) :
    convexHull π (f '' s) = f '' convexHull π s :=
  Set.Subset.antisymm
    (convex_hull_min (image_subset _ (subset_convex_hull π s)) <| (convex_convex_hull π s).is_linear_image hf)
    (image_subset_iff.2 <|
      convex_hull_min (image_subset_iff.1 <| subset_convex_hull π _) ((convex_convex_hull π _).is_linear_preimage hf))

theorem LinearMap.convex_hull_image (f : E ββ[π] F) (s : Set E) : convexHull π (f '' s) = f '' convexHull π s :=
  f.is_linear.convex_hull_image s

end AddCommMonoidβ

end OrderedSemiring

section OrderedCommSemiring

variable [OrderedCommSemiring π] [AddCommMonoidβ E] [Module π E]

theorem convex_hull_smul (a : π) (s : Set E) : convexHull π (a β’ s) = a β’ convexHull π s :=
  (LinearMap.lsmul _ _ a).convex_hull_image _

end OrderedCommSemiring

section OrderedRing

variable [OrderedRing π]

section AddCommGroupβ

variable [AddCommGroupβ E] [AddCommGroupβ F] [Module π E] [Module π F] (s : Set E)

theorem AffineMap.image_convex_hull (f : E βα΅[π] F) : f '' convexHull π s = convexHull π (f '' s) := by
  apply Set.Subset.antisymm
  Β· rw [Set.image_subset_iff]
    refine' convex_hull_min _ ((convex_convex_hull π (βf '' s)).affine_preimage f)
    rw [β Set.image_subset_iff]
    exact subset_convex_hull π (f '' s)
    
  Β· exact convex_hull_min (Set.image_subset _ (subset_convex_hull π s)) ((convex_convex_hull π s).affine_image f)
    

theorem convex_hull_subset_affine_span : convexHull π s β (affineSpan π s : Set E) :=
  convex_hull_min (subset_affine_span π s) (affineSpan π s).Convex

@[simp]
theorem affine_span_convex_hull : affineSpan π (convexHull π s) = affineSpan π s := by
  refine' le_antisymmβ _ (affine_span_mono π (subset_convex_hull π s))
  rw [affine_span_le]
  exact convex_hull_subset_affine_span s

theorem convex_hull_neg (s : Set E) : convexHull π (-s) = -convexHull π s := by
  simp_rw [β image_neg]
  exact (AffineMap.image_convex_hull _ <| -1).symm

end AddCommGroupβ

end OrderedRing

end convexHull

