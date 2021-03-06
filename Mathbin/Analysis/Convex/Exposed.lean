/-
Copyright (c) 2021 YaΓ«l Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YaΓ«l Dillies, Bhavik Mehta
-/
import Mathbin.Analysis.Convex.Extreme
import Mathbin.Analysis.Convex.Function
import Mathbin.Analysis.NormedSpace.Ordered

/-!
# Exposed sets

This file defines exposed sets and exposed points for sets in a real vector space.

An exposed subset of `A` is a subset of `A` that is the set of all maximal points of a functional
(a continuous linear map `E β π`) over `A`. By convention, `β` is an exposed subset of all sets.
This allows for better functoriality of the definition (the intersection of two exposed subsets is
exposed, faces of a polytope form a bounded lattice).
This is an analytic notion of "being on the side of". It is stronger than being extreme (see
`is_exposed.is_extreme`), but weaker (for exposed points) than being a vertex.

An exposed set of `A` is sometimes called a "face of `A`", but we decided to reserve this
terminology to the more specific notion of a face of a polytope (sometimes hopefully soon out
on mathlib!).

## Main declarations

* `is_exposed π A B`: States that `B` is an exposed set of `A` (in the literature, `A` is often
  implicit).
* `is_exposed.is_extreme`: An exposed set is also extreme.

## References

See chapter 8 of [Barry Simon, *Convexity*][simon2011]

## TODO

Define intrinsic frontier/interior and prove the lemmas related to exposed sets and points.

Generalise to Locally Convex Topological Vector Spacesβ’

More not-yet-PRed stuff is available on the branch `sperner_again`.
-/


open Classical Affine BigOperators

open Set

variable (π : Type _) {E : Type _} [NormedLinearOrderedField π] [NormedGroup E] [NormedSpace π E] {l : E βL[π] π}
  {A B C : Set E} {X : Finset E} {x : E}

/-- A set `B` is exposed with respect to `A` iff it maximizes some functional over `A` (and contains
all points maximizing it). Written `is_exposed π A B`. -/
def IsExposed (A B : Set E) : Prop :=
  B.Nonempty β β l : E βL[π] π, B = { x β A | β, β y β A, β, l y β€ l x }

variable {π}

/-- A useful way to build exposed sets from intersecting `A` with halfspaces (modelled by an
inequality with a functional). -/
def ContinuousLinearMap.ToExposed (l : E βL[π] π) (A : Set E) : Set E :=
  { x β A | β, β y β A, β, l y β€ l x }

theorem ContinuousLinearMap.ToExposed.is_exposed : IsExposed π A (l.ToExposed A) := fun h => β¨l, rflβ©

theorem is_exposed_empty : IsExposed π A β := fun β¨x, hxβ© => by
  exfalso
  exact hx

namespace IsExposed

protected theorem subset (hAB : IsExposed π A B) : B β A := by
  rintro x hx
  obtain β¨_, rflβ© := hAB β¨x, hxβ©
  exact hx.1

@[refl]
protected theorem refl (A : Set E) : IsExposed π A A := fun β¨w, hwβ© =>
  β¨0, Subset.antisymm (fun x hx => β¨hx, fun y hy => le_reflβ 0β©) fun x hx => hx.1β©

protected theorem antisymm (hB : IsExposed π A B) (hA : IsExposed π B A) : A = B :=
  hA.Subset.antisymm hB.Subset

/- `is_exposed` is *not* transitive: Consider a (topologically) open cube with vertices
`Aβββ, ..., Aβββ` and add to it the triangle `AβββAβββAβββ`. Then `AβββAβββ` is an exposed subset
of `AβββAβββAβββ` which is an exposed subset of the cube, but `AβββAβββ` is not itself an exposed
subset of the cube. -/
protected theorem mono (hC : IsExposed π A C) (hBA : B β A) (hCB : C β B) : IsExposed π B C := by
  rintro β¨w, hwβ©
  obtain β¨l, rflβ© := hC β¨w, hwβ©
  exact
    β¨l,
      subset.antisymm (fun x hx => β¨hCB hx, fun y hy => hx.2 y (hBA hy)β©) fun x hx =>
        β¨hBA hx.1, fun y hy => (hw.2 y hy).trans (hx.2 w (hCB hw))β©β©

/-- If `B` is an exposed subset of `A`, then `B` is the intersection of `A` with some closed
halfspace. The converse is *not* true. It would require that the corresponding open halfspace
doesn't intersect `A`. -/
theorem eq_inter_halfspace (hAB : IsExposed π A B) : β l : E βL[π] π, β a, B = { x β A | a β€ l x } := by
  obtain hB | hB := B.eq_empty_or_nonempty
  Β· refine' β¨0, 1, _β©
    rw [hB, eq_comm, eq_empty_iff_forall_not_mem]
    rintro x β¨-, hβ©
    rw [ContinuousLinearMap.zero_apply] at h
    linarith
    
  obtain β¨l, rflβ© := hAB hB
  obtain β¨w, hwβ© := hB
  exact
    β¨l, l w, subset.antisymm (fun x hx => β¨hx.1, hx.2 w hw.1β©) fun x hx => β¨hx.1, fun y hy => (hw.2 y hy).trans hx.2β©β©

protected theorem inter (hB : IsExposed π A B) (hC : IsExposed π A C) : IsExposed π A (B β© C) := by
  rintro β¨w, hwB, hwCβ©
  obtain β¨lβ, rflβ© := hB β¨w, hwBβ©
  obtain β¨lβ, rflβ© := hC β¨w, hwCβ©
  refine' β¨lβ + lβ, subset.antisymm _ _β©
  Β· rintro x β¨β¨hxA, hxBβ©, β¨-, hxCβ©β©
    exact β¨hxA, fun z hz => add_le_add (hxB z hz) (hxC z hz)β©
    
  rintro x β¨hxA, hxβ©
  refine' β¨β¨hxA, fun y hy => _β©, hxA, fun y hy => _β©
  Β· exact (add_le_add_iff_right (lβ x)).1 ((add_le_add (hwB.2 y hy) (hwC.2 x hxA)).trans (hx w hwB.1))
    
  Β· exact (add_le_add_iff_left (lβ x)).1 (le_transβ (add_le_add (hwB.2 x hxA) (hwC.2 y hy)) (hx w hwB.1))
    

theorem sInter {F : Finset (Set E)} (hF : F.Nonempty) (hAF : β, β B β F, β, IsExposed π A B) : IsExposed π A (ββ F) :=
  by
  revert hF F
  refine' Finset.induction _ _
  Β· rintro h
    exfalso
    exact empty_not_nonempty h
    
  rintro C F _ hF _ hCF
  rw [Finset.coe_insert, sInter_insert]
  obtain rfl | hFnemp := F.eq_empty_or_nonempty
  Β· rw [Finset.coe_empty, sInter_empty, inter_univ]
    exact hCF C (Finset.mem_singleton_self C)
    
  exact (hCF C (Finset.mem_insert_self C F)).inter (hF hFnemp fun B hB => hCF B (Finset.mem_insert_of_mem hB))

theorem inter_left (hC : IsExposed π A C) (hCB : C β B) : IsExposed π (A β© B) C := by
  rintro β¨w, hwβ©
  obtain β¨l, rflβ© := hC β¨w, hwβ©
  exact
    β¨l,
      subset.antisymm (fun x hx => β¨β¨hx.1, hCB hxβ©, fun y hy => hx.2 y hy.1β©) fun x β¨β¨hxC, _β©, hxβ© =>
        β¨hxC, fun y hy => (hw.2 y hy).trans (hx w β¨hC.subset hw, hCB hwβ©)β©β©

theorem inter_right (hC : IsExposed π B C) (hCA : C β A) : IsExposed π (A β© B) C := by
  rw [inter_comm]
  exact hC.inter_left hCA

protected theorem is_extreme (hAB : IsExposed π A B) : IsExtreme π A B := by
  refine' β¨hAB.subset, fun xβ hxβA xβ hxβA x hxB hx => _β©
  obtain β¨l, rflβ© := hAB β¨x, hxBβ©
  have hl : ConvexOn π univ l := l.to_linear_map.convex_on convex_univ
  have hlxβ := hxB.2 xβ hxβA
  have hlxβ := hxB.2 xβ hxβA
  refine' β¨β¨hxβA, fun y hy => _β©, β¨hxβA, fun y hy => _β©β©
  Β· rw [hlxβ.antisymm (hl.le_left_of_right_le (mem_univ _) (mem_univ _) hx hlxβ)]
    exact hxB.2 y hy
    
  Β· rw [hlxβ.antisymm (hl.le_right_of_left_le (mem_univ _) (mem_univ _) hx hlxβ)]
    exact hxB.2 y hy
    

protected theorem convex (hAB : IsExposed π A B) (hA : Convex π A) : Convex π B := by
  obtain rfl | hB := B.eq_empty_or_nonempty
  Β· exact convex_empty
    
  obtain β¨l, rflβ© := hAB hB
  exact fun xβ xβ hxβ hxβ a b ha hb hab =>
    β¨hA hxβ.1 hxβ.1 ha hb hab, fun y hy =>
      ((l.to_linear_map.concave_on convex_univ).convex_ge _ β¨mem_univ _, hxβ.2 y hyβ© β¨mem_univ _, hxβ.2 y hyβ© ha hb
          hab).2β©

protected theorem is_closed [OrderClosedTopology π] (hAB : IsExposed π A B) (hA : IsClosed A) : IsClosed B := by
  obtain β¨l, a, rflβ© := hAB.eq_inter_halfspace
  exact hA.is_closed_le continuous_on_const l.continuous.continuous_on

protected theorem is_compact [OrderClosedTopology π] (hAB : IsExposed π A B) (hA : IsCompact A) : IsCompact B :=
  compact_of_is_closed_subset hA (hAB.IsClosed hA.IsClosed) hAB.Subset

end IsExposed

variable (π)

/-- A point is exposed with respect to `A` iff there exists an hyperplane whose intersection with
`A` is exactly that point. -/
def Set.ExposedPoints (A : Set E) : Set E :=
  { x β A | β l : E βL[π] π, β, β y β A, β, l y β€ l x β§ (l x β€ l y β y = x) }

variable {π}

theorem exposed_point_def :
    x β A.ExposedPoints π β x β A β§ β l : E βL[π] π, β, β y β A, β, l y β€ l x β§ (l x β€ l y β y = x) :=
  Iff.rfl

theorem exposed_points_subset : A.ExposedPoints π β A := fun x hx => hx.1

@[simp]
theorem exposed_points_empty : (β : Set E).ExposedPoints π = β :=
  subset_empty_iff.1 exposed_points_subset

/-- Exposed points exactly correspond to exposed singletons. -/
theorem mem_exposed_points_iff_exposed_singleton : x β A.ExposedPoints π β IsExposed π A {x} := by
  use fun β¨hxA, l, hlβ© h =>
    β¨l,
      Eq.symm <| eq_singleton_iff_unique_mem.2 β¨β¨hxA, fun y hy => (hl y hy).1β©, fun z hz => (hl z hz.1).2 (hz.2 x hxA)β©β©
  rintro h
  obtain β¨l, hlβ© := h β¨x, mem_singleton _β©
  rw [eq_comm, eq_singleton_iff_unique_mem] at hl
  exact β¨hl.1.1, l, fun y hy => β¨hl.1.2 y hy, fun hxy => hl.2 y β¨hy, fun z hz => (hl.1.2 z hz).trans hxyβ©β©β©

theorem exposed_points_subset_extreme_points : A.ExposedPoints π β A.ExtremePoints π := fun x hx =>
  mem_extreme_points_iff_extreme_singleton.2 (mem_exposed_points_iff_exposed_singleton.1 hx).IsExtreme

