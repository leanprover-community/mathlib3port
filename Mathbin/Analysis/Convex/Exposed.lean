/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathbin.Analysis.Convex.Extreme
import Mathbin.Analysis.Convex.Function
import Mathbin.Analysis.Normed.Order.Basic

/-!
# Exposed sets

This file defines exposed sets and exposed points for sets in a real vector space.

An exposed subset of `A` is a subset of `A` that is the set of all maximal points of a functional
(a continuous linear map `E → 𝕜`) over `A`. By convention, `∅` is an exposed subset of all sets.
This allows for better functoriality of the definition (the intersection of two exposed subsets is
exposed, faces of a polytope form a bounded lattice).
This is an analytic notion of "being on the side of". It is stronger than being extreme (see
`is_exposed.is_extreme`), but weaker (for exposed points) than being a vertex.

An exposed set of `A` is sometimes called a "face of `A`", but we decided to reserve this
terminology to the more specific notion of a face of a polytope (sometimes hopefully soon out
on mathlib!).

## Main declarations

* `is_exposed 𝕜 A B`: States that `B` is an exposed set of `A` (in the literature, `A` is often
  implicit).
* `is_exposed.is_extreme`: An exposed set is also extreme.

## References

See chapter 8 of [Barry Simon, *Convexity*][simon2011]

## TODO

Define intrinsic frontier/interior and prove the lemmas related to exposed sets and points.

Generalise to Locally Convex Topological Vector Spaces™

More not-yet-PRed stuff is available on the branch `sperner_again`.
-/


open Classical Affine BigOperators

open Set

variable (𝕜 : Type _) {E : Type _} [NormedLinearOrderedField 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]
  {l : E →L[𝕜] 𝕜} {A B C : Set E} {X : Finset E} {x : E}

/-- A set `B` is exposed with respect to `A` iff it maximizes some functional over `A` (and contains
all points maximizing it). Written `is_exposed 𝕜 A B`. -/
def IsExposed (A B : Set E) : Prop :=
  B.Nonempty → ∃ l : E →L[𝕜] 𝕜, B = { x ∈ A | ∀ y ∈ A, l y ≤ l x }
#align is_exposed IsExposed

variable {𝕜}

/-- A useful way to build exposed sets from intersecting `A` with halfspaces (modelled by an
inequality with a functional). -/
def ContinuousLinearMap.toExposed (l : E →L[𝕜] 𝕜) (A : Set E) : Set E :=
  { x ∈ A | ∀ y ∈ A, l y ≤ l x }
#align continuous_linear_map.to_exposed ContinuousLinearMap.toExposed

theorem ContinuousLinearMap.toExposed.isExposed : IsExposed 𝕜 A (l.toExposed A) := fun h => ⟨l, rfl⟩
#align continuous_linear_map.to_exposed.is_exposed ContinuousLinearMap.toExposed.isExposed

theorem isExposedEmpty : IsExposed 𝕜 A ∅ := fun ⟨x, hx⟩ => by
  exfalso
  exact hx
#align is_exposed_empty isExposedEmpty

namespace IsExposed

protected theorem subset (hAB : IsExposed 𝕜 A B) : B ⊆ A := by
  rintro x hx
  obtain ⟨_, rfl⟩ := hAB ⟨x, hx⟩
  exact hx.1
#align is_exposed.subset IsExposed.subset

@[refl]
protected theorem refl (A : Set E) : IsExposed 𝕜 A A := fun ⟨w, hw⟩ =>
  ⟨0, Subset.antisymm (fun x hx => ⟨hx, fun y hy => le_refl 0⟩) fun x hx => hx.1⟩
#align is_exposed.refl IsExposed.refl

protected theorem antisymm (hB : IsExposed 𝕜 A B) (hA : IsExposed 𝕜 B A) : A = B :=
  hA.Subset.antisymm hB.Subset
#align is_exposed.antisymm IsExposed.antisymm

/- `is_exposed` is *not* transitive: Consider a (topologically) open cube with vertices
`A₀₀₀, ..., A₁₁₁` and add to it the triangle `A₀₀₀A₀₀₁A₀₁₀`. Then `A₀₀₁A₀₁₀` is an exposed subset
of `A₀₀₀A₀₀₁A₀₁₀` which is an exposed subset of the cube, but `A₀₀₁A₀₁₀` is not itself an exposed
subset of the cube. -/
protected theorem mono (hC : IsExposed 𝕜 A C) (hBA : B ⊆ A) (hCB : C ⊆ B) : IsExposed 𝕜 B C := by
  rintro ⟨w, hw⟩
  obtain ⟨l, rfl⟩ := hC ⟨w, hw⟩
  exact
    ⟨l,
      subset.antisymm (fun x hx => ⟨hCB hx, fun y hy => hx.2 y (hBA hy)⟩) fun x hx =>
        ⟨hBA hx.1, fun y hy => (hw.2 y hy).trans (hx.2 w (hCB hw))⟩⟩
#align is_exposed.mono IsExposed.mono

/-- If `B` is an exposed subset of `A`, then `B` is the intersection of `A` with some closed
halfspace. The converse is *not* true. It would require that the corresponding open halfspace
doesn't intersect `A`. -/
theorem eq_inter_halfspace (hAB : IsExposed 𝕜 A B) : ∃ l : E →L[𝕜] 𝕜, ∃ a, B = { x ∈ A | a ≤ l x } := by
  obtain hB | hB := B.eq_empty_or_nonempty
  · refine' ⟨0, 1, _⟩
    rw [hB, eq_comm, eq_empty_iff_forall_not_mem]
    rintro x ⟨-, h⟩
    rw [ContinuousLinearMap.zero_apply] at h
    linarith
    
  obtain ⟨l, rfl⟩ := hAB hB
  obtain ⟨w, hw⟩ := hB
  exact
    ⟨l, l w, subset.antisymm (fun x hx => ⟨hx.1, hx.2 w hw.1⟩) fun x hx => ⟨hx.1, fun y hy => (hw.2 y hy).trans hx.2⟩⟩
#align is_exposed.eq_inter_halfspace IsExposed.eq_inter_halfspace

protected theorem inter (hB : IsExposed 𝕜 A B) (hC : IsExposed 𝕜 A C) : IsExposed 𝕜 A (B ∩ C) := by
  rintro ⟨w, hwB, hwC⟩
  obtain ⟨l₁, rfl⟩ := hB ⟨w, hwB⟩
  obtain ⟨l₂, rfl⟩ := hC ⟨w, hwC⟩
  refine' ⟨l₁ + l₂, subset.antisymm _ _⟩
  · rintro x ⟨⟨hxA, hxB⟩, ⟨-, hxC⟩⟩
    exact ⟨hxA, fun z hz => add_le_add (hxB z hz) (hxC z hz)⟩
    
  rintro x ⟨hxA, hx⟩
  refine' ⟨⟨hxA, fun y hy => _⟩, hxA, fun y hy => _⟩
  · exact (add_le_add_iff_right (l₂ x)).1 ((add_le_add (hwB.2 y hy) (hwC.2 x hxA)).trans (hx w hwB.1))
    
  · exact (add_le_add_iff_left (l₁ x)).1 (le_trans (add_le_add (hwB.2 x hxA) (hwC.2 y hy)) (hx w hwB.1))
    
#align is_exposed.inter IsExposed.inter

theorem sInter {F : Finset (Set E)} (hF : F.Nonempty) (hAF : ∀ B ∈ F, IsExposed 𝕜 A B) : IsExposed 𝕜 A (⋂₀ F) := by
  revert hF F
  refine' Finset.induction _ _
  · rintro h
    exfalso
    exact not_nonempty_empty h
    
  rintro C F _ hF _ hCF
  rw [Finset.coe_insert, sInter_insert]
  obtain rfl | hFnemp := F.eq_empty_or_nonempty
  · rw [Finset.coe_empty, sInter_empty, inter_univ]
    exact hCF C (Finset.mem_singleton_self C)
    
  exact (hCF C (Finset.mem_insert_self C F)).inter (hF hFnemp fun B hB => hCF B (Finset.mem_insert_of_mem hB))
#align is_exposed.sInter IsExposed.sInter

theorem interLeft (hC : IsExposed 𝕜 A C) (hCB : C ⊆ B) : IsExposed 𝕜 (A ∩ B) C := by
  rintro ⟨w, hw⟩
  obtain ⟨l, rfl⟩ := hC ⟨w, hw⟩
  exact
    ⟨l,
      subset.antisymm (fun x hx => ⟨⟨hx.1, hCB hx⟩, fun y hy => hx.2 y hy.1⟩) fun x ⟨⟨hxC, _⟩, hx⟩ =>
        ⟨hxC, fun y hy => (hw.2 y hy).trans (hx w ⟨hC.subset hw, hCB hw⟩)⟩⟩
#align is_exposed.inter_left IsExposed.interLeft

theorem interRight (hC : IsExposed 𝕜 B C) (hCA : C ⊆ A) : IsExposed 𝕜 (A ∩ B) C := by
  rw [inter_comm]
  exact hC.inter_left hCA
#align is_exposed.inter_right IsExposed.interRight

protected theorem is_extreme (hAB : IsExposed 𝕜 A B) : IsExtreme 𝕜 A B := by
  refine' ⟨hAB.subset, fun x₁ hx₁A x₂ hx₂A x hxB hx => _⟩
  obtain ⟨l, rfl⟩ := hAB ⟨x, hxB⟩
  have hl : ConvexOn 𝕜 univ l := l.to_linear_map.convex_on convex_univ
  have hlx₁ := hxB.2 x₁ hx₁A
  have hlx₂ := hxB.2 x₂ hx₂A
  refine' ⟨⟨hx₁A, fun y hy => _⟩, ⟨hx₂A, fun y hy => _⟩⟩
  · rw [hlx₁.antisymm (hl.le_left_of_right_le (mem_univ _) (mem_univ _) hx hlx₂)]
    exact hxB.2 y hy
    
  · rw [hlx₂.antisymm (hl.le_right_of_left_le (mem_univ _) (mem_univ _) hx hlx₁)]
    exact hxB.2 y hy
    
#align is_exposed.is_extreme IsExposed.is_extreme

protected theorem convex (hAB : IsExposed 𝕜 A B) (hA : Convex 𝕜 A) : Convex 𝕜 B := by
  obtain rfl | hB := B.eq_empty_or_nonempty
  · exact convex_empty
    
  obtain ⟨l, rfl⟩ := hAB hB
  exact fun x₁ hx₁ x₂ hx₂ a b ha hb hab =>
    ⟨hA hx₁.1 hx₂.1 ha hb hab, fun y hy =>
      ((l.to_linear_map.concave_on convex_univ).convex_ge _ ⟨mem_univ _, hx₁.2 y hy⟩ ⟨mem_univ _, hx₂.2 y hy⟩ ha hb
          hab).2⟩
#align is_exposed.convex IsExposed.convex

protected theorem isClosed [OrderClosedTopology 𝕜] (hAB : IsExposed 𝕜 A B) (hA : IsClosed A) : IsClosed B := by
  obtain ⟨l, a, rfl⟩ := hAB.eq_inter_halfspace
  exact hA.is_closed_le continuous_on_const l.continuous.continuous_on
#align is_exposed.is_closed IsExposed.isClosed

protected theorem is_compact [OrderClosedTopology 𝕜] [T2Space E] (hAB : IsExposed 𝕜 A B) (hA : IsCompact A) :
    IsCompact B :=
  is_compact_of_is_closed_subset hA (hAB.IsClosed hA.IsClosed) hAB.Subset
#align is_exposed.is_compact IsExposed.is_compact

end IsExposed

variable (𝕜)

/-- A point is exposed with respect to `A` iff there exists an hyperplane whose intersection with
`A` is exactly that point. -/
def Set.exposedPoints (A : Set E) : Set E :=
  { x ∈ A | ∃ l : E →L[𝕜] 𝕜, ∀ y ∈ A, l y ≤ l x ∧ (l x ≤ l y → y = x) }
#align set.exposed_points Set.exposedPoints

variable {𝕜}

theorem exposed_point_def : x ∈ A.exposedPoints 𝕜 ↔ x ∈ A ∧ ∃ l : E →L[𝕜] 𝕜, ∀ y ∈ A, l y ≤ l x ∧ (l x ≤ l y → y = x) :=
  Iff.rfl
#align exposed_point_def exposed_point_def

theorem exposed_points_subset : A.exposedPoints 𝕜 ⊆ A := fun x hx => hx.1
#align exposed_points_subset exposed_points_subset

@[simp]
theorem exposed_points_empty : (∅ : Set E).exposedPoints 𝕜 = ∅ :=
  subset_empty_iff.1 exposed_points_subset
#align exposed_points_empty exposed_points_empty

/-- Exposed points exactly correspond to exposed singletons. -/
theorem mem_exposed_points_iff_exposed_singleton : x ∈ A.exposedPoints 𝕜 ↔ IsExposed 𝕜 A {x} := by
  use fun ⟨hxA, l, hl⟩ h =>
    ⟨l,
      Eq.symm $ eq_singleton_iff_unique_mem.2 ⟨⟨hxA, fun y hy => (hl y hy).1⟩, fun z hz => (hl z hz.1).2 (hz.2 x hxA)⟩⟩
  rintro h
  obtain ⟨l, hl⟩ := h ⟨x, mem_singleton _⟩
  rw [eq_comm, eq_singleton_iff_unique_mem] at hl
  exact ⟨hl.1.1, l, fun y hy => ⟨hl.1.2 y hy, fun hxy => hl.2 y ⟨hy, fun z hz => (hl.1.2 z hz).trans hxy⟩⟩⟩
#align mem_exposed_points_iff_exposed_singleton mem_exposed_points_iff_exposed_singleton

theorem exposed_points_subset_extreme_points : A.exposedPoints 𝕜 ⊆ A.extremePoints 𝕜 := fun x hx =>
  mem_extreme_points_iff_extreme_singleton.2 (mem_exposed_points_iff_exposed_singleton.1 hx).IsExtreme
#align exposed_points_subset_extreme_points exposed_points_subset_extreme_points

