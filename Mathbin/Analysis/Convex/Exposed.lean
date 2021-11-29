import Mathbin.Analysis.Convex.Extreme 
import Mathbin.Analysis.Convex.Function 
import Mathbin.Analysis.NormedSpace.Ordered

/-!
# Exposed sets

This file defines exposed sets and exposed points for sets in a real vector space.

An exposed subset of `A` is a subset of `A` that is the set of all maximal points of a functional
(a continuous linear map `E → 𝕜`) over `A`. By convention, `∅` is an exposed subset of all sets.
This allows for better functioriality of the definition (the intersection of two exposed subsets is
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


open_locale Classical Affine BigOperators

open Set

variable (𝕜 : Type _) {E : Type _} [NormedLinearOrderedField 𝕜] [NormedGroup E] [NormedSpace 𝕜 E] {l : E →L[𝕜] 𝕜}
  {A B C : Set E} {X : Finset E} {x : E}

/-- A set `B` is exposed with respect to `A` iff it maximizes some functional over `A` (and contains
all points maximizing it). Written `is_exposed 𝕜 A B`. -/
def IsExposed (A B : Set E) : Prop :=
  B.nonempty → ∃ l : E →L[𝕜] 𝕜, B = { x∈A | ∀ y _ : y ∈ A, l y ≤ l x }

variable {𝕜}

/-- A useful way to build exposed sets from intersecting `A` with halfspaces (modelled by an
inequality with a functional). -/
def ContinuousLinearMap.ToExposed (l : E →L[𝕜] 𝕜) (A : Set E) : Set E :=
  { x∈A | ∀ y _ : y ∈ A, l y ≤ l x }

theorem ContinuousLinearMap.ToExposed.is_exposed : IsExposed 𝕜 A (l.to_exposed A) :=
  fun h => ⟨l, rfl⟩

theorem is_exposed_empty : IsExposed 𝕜 A ∅ :=
  fun ⟨x, hx⟩ =>
    by 
      exfalso 
      exact hx

namespace IsExposed

protected theorem subset (hAB : IsExposed 𝕜 A B) : B ⊆ A :=
  by 
    rintro x hx 
    obtain ⟨_, rfl⟩ := hAB ⟨x, hx⟩
    exact hx.1

@[refl]
protected theorem refl (A : Set E) : IsExposed 𝕜 A A :=
  fun ⟨w, hw⟩ =>
    ⟨0,
      subset.antisymm
        (fun x hx =>
          ⟨hx,
            fun y hy =>
              by 
                exact le_reflₓ 0⟩)
        fun x hx => hx.1⟩

protected theorem antisymm (hB : IsExposed 𝕜 A B) (hA : IsExposed 𝕜 B A) : A = B :=
  hA.subset.antisymm hB.subset

protected theorem mono (hC : IsExposed 𝕜 A C) (hBA : B ⊆ A) (hCB : C ⊆ B) : IsExposed 𝕜 B C :=
  by 
    rintro ⟨w, hw⟩
    obtain ⟨l, rfl⟩ := hC ⟨w, hw⟩
    exact
      ⟨l,
        subset.antisymm (fun x hx => ⟨hCB hx, fun y hy => hx.2 y (hBA hy)⟩)
          fun x hx => ⟨hBA hx.1, fun y hy => (hw.2 y hy).trans (hx.2 w (hCB hw))⟩⟩

/-- If `B` is an exposed subset of `A`, then `B` is the intersection of `A` with some closed
halfspace. The converse is *not* true. It would require that the corresponding open halfspace
doesn't intersect `A`. -/
theorem eq_inter_halfspace (hAB : IsExposed 𝕜 A B) : ∃ l : E →L[𝕜] 𝕜, ∃ a, B = { x∈A | a ≤ l x } :=
  by 
    obtain hB | hB := B.eq_empty_or_nonempty
    ·
      refine' ⟨0, 1, _⟩
      rw [hB, eq_comm, eq_empty_iff_forall_not_mem]
      rintro x ⟨-, h⟩
      rw [ContinuousLinearMap.zero_apply] at h 
      linarith 
    obtain ⟨l, rfl⟩ := hAB hB 
    obtain ⟨w, hw⟩ := hB 
    exact
      ⟨l, l w, subset.antisymm (fun x hx => ⟨hx.1, hx.2 w hw.1⟩) fun x hx => ⟨hx.1, fun y hy => (hw.2 y hy).trans hx.2⟩⟩

protected theorem inter (hB : IsExposed 𝕜 A B) (hC : IsExposed 𝕜 A C) : IsExposed 𝕜 A (B ∩ C) :=
  by 
    rintro ⟨w, hwB, hwC⟩
    obtain ⟨l₁, rfl⟩ := hB ⟨w, hwB⟩
    obtain ⟨l₂, rfl⟩ := hC ⟨w, hwC⟩
    refine' ⟨l₁+l₂, subset.antisymm _ _⟩
    ·
      rintro x ⟨⟨hxA, hxB⟩, ⟨-, hxC⟩⟩
      exact ⟨hxA, fun z hz => add_le_add (hxB z hz) (hxC z hz)⟩
    rintro x ⟨hxA, hx⟩
    refine' ⟨⟨hxA, fun y hy => _⟩, hxA, fun y hy => _⟩
    ·
      exact (add_le_add_iff_right (l₂ x)).1 ((add_le_add (hwB.2 y hy) (hwC.2 x hxA)).trans (hx w hwB.1))
    ·
      exact (add_le_add_iff_left (l₁ x)).1 (le_transₓ (add_le_add (hwB.2 x hxA) (hwC.2 y hy)) (hx w hwB.1))

theorem sInter {F : Finset (Set E)} (hF : F.nonempty) (hAF : ∀ B _ : B ∈ F, IsExposed 𝕜 A B) : IsExposed 𝕜 A (⋂₀F) :=
  by 
    revert hF F 
    refine' Finset.induction _ _
    ·
      rintro h 
      exfalso 
      exact empty_not_nonempty h 
    rintro C F _ hF _ hCF 
    rw [Finset.coe_insert, sInter_insert]
    obtain rfl | hFnemp := F.eq_empty_or_nonempty
    ·
      rw [Finset.coe_empty, sInter_empty, inter_univ]
      exact hCF C (Finset.mem_singleton_self C)
    exact (hCF C (Finset.mem_insert_self C F)).inter (hF hFnemp fun B hB => hCF B (Finset.mem_insert_of_mem hB))

theorem inter_left (hC : IsExposed 𝕜 A C) (hCB : C ⊆ B) : IsExposed 𝕜 (A ∩ B) C :=
  by 
    rintro ⟨w, hw⟩
    obtain ⟨l, rfl⟩ := hC ⟨w, hw⟩
    exact
      ⟨l,
        subset.antisymm (fun x hx => ⟨⟨hx.1, hCB hx⟩, fun y hy => hx.2 y hy.1⟩)
          fun x ⟨⟨hxC, _⟩, hx⟩ => ⟨hxC, fun y hy => (hw.2 y hy).trans (hx w ⟨hC.subset hw, hCB hw⟩)⟩⟩

theorem inter_right (hC : IsExposed 𝕜 B C) (hCA : C ⊆ A) : IsExposed 𝕜 (A ∩ B) C :=
  by 
    rw [inter_comm]
    exact hC.inter_left hCA

-- error in Analysis.Convex.Exposed: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected theorem is_extreme (hAB : is_exposed 𝕜 A B) : is_extreme 𝕜 A B :=
begin
  refine [expr ⟨hAB.subset, λ x₁ x₂ hx₁A hx₂A x hxB hx, _⟩],
  obtain ["⟨", ident l, ",", ident rfl, "⟩", ":=", expr hAB ⟨x, hxB⟩],
  have [ident hl] [":", expr convex_on 𝕜 univ l] [":=", expr l.to_linear_map.convex_on convex_univ],
  have [ident hlx₁] [] [":=", expr hxB.2 x₁ hx₁A],
  have [ident hlx₂] [] [":=", expr hxB.2 x₂ hx₂A],
  refine [expr ⟨⟨hx₁A, λ y hy, _⟩, ⟨hx₂A, λ y hy, _⟩⟩],
  { rw [expr hlx₁.antisymm (hl.le_left_of_right_le (mem_univ _) (mem_univ _) hx hlx₂)] [],
    exact [expr hxB.2 y hy] },
  { rw [expr hlx₂.antisymm (hl.le_right_of_left_le (mem_univ _) (mem_univ _) hx hlx₁)] [],
    exact [expr hxB.2 y hy] }
end

protected theorem Convex (hAB : IsExposed 𝕜 A B) (hA : Convex 𝕜 A) : Convex 𝕜 B :=
  by 
    obtain rfl | hB := B.eq_empty_or_nonempty
    ·
      exact convex_empty 
    obtain ⟨l, rfl⟩ := hAB hB 
    exact
      fun x₁ x₂ hx₁ hx₂ a b ha hb hab =>
        ⟨hA hx₁.1 hx₂.1 ha hb hab,
          fun y hy =>
            ((l.to_linear_map.concave_on convex_univ).convex_ge _ ⟨mem_univ _, hx₁.2 y hy⟩ ⟨mem_univ _, hx₂.2 y hy⟩ ha
                hb hab).2⟩

protected theorem IsClosed [OrderClosedTopology 𝕜] (hAB : IsExposed 𝕜 A B) (hA : IsClosed A) : IsClosed B :=
  by 
    obtain ⟨l, a, rfl⟩ := hAB.eq_inter_halfspace 
    exact hA.is_closed_le continuous_on_const l.continuous.continuous_on

protected theorem IsCompact [OrderClosedTopology 𝕜] (hAB : IsExposed 𝕜 A B) (hA : IsCompact A) : IsCompact B :=
  compact_of_is_closed_subset hA (hAB.is_closed hA.is_closed) hAB.subset

end IsExposed

variable (𝕜)

/-- A point is exposed with respect to `A` iff there exists an hyperplane whose intersection with
`A` is exactly that point. -/
def Set.ExposedPoints (A : Set E) : Set E :=
  { x∈A | ∃ l : E →L[𝕜] 𝕜, ∀ y _ : y ∈ A, l y ≤ l x ∧ (l x ≤ l y → y = x) }

variable {𝕜}

theorem exposed_point_def :
  x ∈ A.exposed_points 𝕜 ↔ x ∈ A ∧ ∃ l : E →L[𝕜] 𝕜, ∀ y _ : y ∈ A, l y ≤ l x ∧ (l x ≤ l y → y = x) :=
  Iff.rfl

theorem exposed_points_subset : A.exposed_points 𝕜 ⊆ A :=
  fun x hx => hx.1

@[simp]
theorem exposed_points_empty : (∅ : Set E).ExposedPoints 𝕜 = ∅ :=
  subset_empty_iff.1 exposed_points_subset

/-- Exposed points exactly correspond to exposed singletons. -/
theorem mem_exposed_points_iff_exposed_singleton : x ∈ A.exposed_points 𝕜 ↔ IsExposed 𝕜 A {x} :=
  by 
    use
      fun ⟨hxA, l, hl⟩ h =>
        ⟨l,
          Eq.symm$
            eq_singleton_iff_unique_mem.2 ⟨⟨hxA, fun y hy => (hl y hy).1⟩, fun z hz => (hl z hz.1).2 (hz.2 x hxA)⟩⟩
    rintro h 
    obtain ⟨l, hl⟩ := h ⟨x, mem_singleton _⟩
    rw [eq_comm, eq_singleton_iff_unique_mem] at hl 
    exact ⟨hl.1.1, l, fun y hy => ⟨hl.1.2 y hy, fun hxy => hl.2 y ⟨hy, fun z hz => (hl.1.2 z hz).trans hxy⟩⟩⟩

theorem exposed_points_subset_extreme_points : A.exposed_points 𝕜 ⊆ A.extreme_points 𝕜 :=
  fun x hx => mem_extreme_points_iff_extreme_singleton.2 (mem_exposed_points_iff_exposed_singleton.1 hx).IsExtreme

