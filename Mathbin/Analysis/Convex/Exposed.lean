/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta

! This file was ported from Lean 3 source module analysis.convex.exposed
! leanprover-community/mathlib commit ce38d86c0b2d427ce208c3cee3159cb421d2b3c4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Convex.Extreme
import Mathbin.Analysis.Convex.Function
import Mathbin.Topology.Algebra.Module.Basic
import Mathbin.Topology.Order.Basic

/-!
# Exposed sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

section PreorderSemiring

variable (𝕜 : Type _) {E : Type _} [TopologicalSpace 𝕜] [Semiring 𝕜] [Preorder 𝕜] [AddCommMonoid E]
  [TopologicalSpace E] [Module 𝕜 E] {A B : Set E}

#print IsExposed /-
/-- A set `B` is exposed with respect to `A` iff it maximizes some functional over `A` (and contains
all points maximizing it). Written `is_exposed 𝕜 A B`. -/
def IsExposed (A B : Set E) : Prop :=
  B.Nonempty → ∃ l : E →L[𝕜] 𝕜, B = { x ∈ A | ∀ y ∈ A, l y ≤ l x }
#align is_exposed IsExposed
-/

end PreorderSemiring

section OrderedRing

variable {𝕜 : Type _} {E : Type _} [TopologicalSpace 𝕜] [OrderedRing 𝕜] [AddCommMonoid E]
  [TopologicalSpace E] [Module 𝕜 E] {l : E →L[𝕜] 𝕜} {A B C : Set E} {X : Finset E} {x : E}

#print ContinuousLinearMap.toExposed /-
/-- A useful way to build exposed sets from intersecting `A` with halfspaces (modelled by an
inequality with a functional). -/
def ContinuousLinearMap.toExposed (l : E →L[𝕜] 𝕜) (A : Set E) : Set E :=
  { x ∈ A | ∀ y ∈ A, l y ≤ l x }
#align continuous_linear_map.to_exposed ContinuousLinearMap.toExposed
-/

/- warning: continuous_linear_map.to_exposed.is_exposed -> ContinuousLinearMap.toExposed.isExposed is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} 𝕜] [_inst_2 : OrderedRing.{u1} 𝕜] [_inst_3 : AddCommMonoid.{u2} E] [_inst_4 : TopologicalSpace.{u2} E] [_inst_5 : Module.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)) _inst_3] {l : ContinuousLinearMap.{u1, u1, u2, u1} 𝕜 𝕜 (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)) (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)))) E _inst_4 _inst_3 𝕜 _inst_1 (AddCommGroup.toAddCommMonoid.{u1} 𝕜 (OrderedAddCommGroup.toAddCommGroup.{u1} 𝕜 (OrderedRing.toOrderedAddCommGroup.{u1} 𝕜 _inst_2))) _inst_5 (Semiring.toModule.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)))} {A : Set.{u2} E}, IsExposed.{u1, u2} 𝕜 E _inst_1 (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (OrderedRing.toOrderedAddCommGroup.{u1} 𝕜 _inst_2))) _inst_3 _inst_4 _inst_5 A (ContinuousLinearMap.toExposed.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 l A)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} 𝕜] [_inst_2 : OrderedRing.{u2} 𝕜] [_inst_3 : AddCommMonoid.{u1} E] [_inst_4 : TopologicalSpace.{u1} E] [_inst_5 : Module.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)) _inst_3] {l : ContinuousLinearMap.{u2, u2, u1, u2} 𝕜 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)) (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)))) E _inst_4 _inst_3 𝕜 _inst_1 (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} 𝕜 (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} 𝕜 (OrderedRing.toOrderedAddCommGroup.{u2} 𝕜 _inst_2))) _inst_5 (Semiring.toModule.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)))} {A : Set.{u1} E}, IsExposed.{u2, u1} 𝕜 E _inst_1 (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u2} 𝕜 (OrderedRing.toPartialOrder.{u2} 𝕜 _inst_2)) _inst_3 _inst_4 _inst_5 A (ContinuousLinearMap.toExposed.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 l A)
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.to_exposed.is_exposed ContinuousLinearMap.toExposed.isExposedₓ'. -/
theorem ContinuousLinearMap.toExposed.isExposed : IsExposed 𝕜 A (l.toExposed A) := fun h => ⟨l, rfl⟩
#align continuous_linear_map.to_exposed.is_exposed ContinuousLinearMap.toExposed.isExposed

/- warning: is_exposed_empty -> isExposed_empty is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} 𝕜] [_inst_2 : OrderedRing.{u1} 𝕜] [_inst_3 : AddCommMonoid.{u2} E] [_inst_4 : TopologicalSpace.{u2} E] [_inst_5 : Module.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)) _inst_3] {A : Set.{u2} E}, IsExposed.{u1, u2} 𝕜 E _inst_1 (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (OrderedRing.toOrderedAddCommGroup.{u1} 𝕜 _inst_2))) _inst_3 _inst_4 _inst_5 A (EmptyCollection.emptyCollection.{u2} (Set.{u2} E) (Set.hasEmptyc.{u2} E))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} 𝕜] [_inst_2 : OrderedRing.{u2} 𝕜] [_inst_3 : AddCommMonoid.{u1} E] [_inst_4 : TopologicalSpace.{u1} E] [_inst_5 : Module.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)) _inst_3] {A : Set.{u1} E}, IsExposed.{u2, u1} 𝕜 E _inst_1 (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u2} 𝕜 (OrderedRing.toPartialOrder.{u2} 𝕜 _inst_2)) _inst_3 _inst_4 _inst_5 A (EmptyCollection.emptyCollection.{u1} (Set.{u1} E) (Set.instEmptyCollectionSet.{u1} E))
Case conversion may be inaccurate. Consider using '#align is_exposed_empty isExposed_emptyₓ'. -/
theorem isExposed_empty : IsExposed 𝕜 A ∅ := fun ⟨x, hx⟩ =>
  by
  exfalso
  exact hx
#align is_exposed_empty isExposed_empty

namespace IsExposed

/- warning: is_exposed.subset -> IsExposed.subset is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} 𝕜] [_inst_2 : OrderedRing.{u1} 𝕜] [_inst_3 : AddCommMonoid.{u2} E] [_inst_4 : TopologicalSpace.{u2} E] [_inst_5 : Module.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)) _inst_3] {A : Set.{u2} E} {B : Set.{u2} E}, (IsExposed.{u1, u2} 𝕜 E _inst_1 (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (OrderedRing.toOrderedAddCommGroup.{u1} 𝕜 _inst_2))) _inst_3 _inst_4 _inst_5 A B) -> (HasSubset.Subset.{u2} (Set.{u2} E) (Set.hasSubset.{u2} E) B A)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} 𝕜] [_inst_2 : OrderedRing.{u2} 𝕜] [_inst_3 : AddCommMonoid.{u1} E] [_inst_4 : TopologicalSpace.{u1} E] [_inst_5 : Module.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)) _inst_3] {A : Set.{u1} E} {B : Set.{u1} E}, (IsExposed.{u2, u1} 𝕜 E _inst_1 (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u2} 𝕜 (OrderedRing.toPartialOrder.{u2} 𝕜 _inst_2)) _inst_3 _inst_4 _inst_5 A B) -> (HasSubset.Subset.{u1} (Set.{u1} E) (Set.instHasSubsetSet.{u1} E) B A)
Case conversion may be inaccurate. Consider using '#align is_exposed.subset IsExposed.subsetₓ'. -/
protected theorem subset (hAB : IsExposed 𝕜 A B) : B ⊆ A :=
  by
  rintro x hx
  obtain ⟨_, rfl⟩ := hAB ⟨x, hx⟩
  exact hx.1
#align is_exposed.subset IsExposed.subset

#print IsExposed.refl /-
@[refl]
protected theorem refl (A : Set E) : IsExposed 𝕜 A A := fun ⟨w, hw⟩ =>
  ⟨0, Subset.antisymm (fun x hx => ⟨hx, fun y hy => le_refl 0⟩) fun x hx => hx.1⟩
#align is_exposed.refl IsExposed.refl
-/

/- warning: is_exposed.antisymm -> IsExposed.antisymm is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} 𝕜] [_inst_2 : OrderedRing.{u1} 𝕜] [_inst_3 : AddCommMonoid.{u2} E] [_inst_4 : TopologicalSpace.{u2} E] [_inst_5 : Module.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)) _inst_3] {A : Set.{u2} E} {B : Set.{u2} E}, (IsExposed.{u1, u2} 𝕜 E _inst_1 (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (OrderedRing.toOrderedAddCommGroup.{u1} 𝕜 _inst_2))) _inst_3 _inst_4 _inst_5 A B) -> (IsExposed.{u1, u2} 𝕜 E _inst_1 (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (OrderedRing.toOrderedAddCommGroup.{u1} 𝕜 _inst_2))) _inst_3 _inst_4 _inst_5 B A) -> (Eq.{succ u2} (Set.{u2} E) A B)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} 𝕜] [_inst_2 : OrderedRing.{u2} 𝕜] [_inst_3 : AddCommMonoid.{u1} E] [_inst_4 : TopologicalSpace.{u1} E] [_inst_5 : Module.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)) _inst_3] {A : Set.{u1} E} {B : Set.{u1} E}, (IsExposed.{u2, u1} 𝕜 E _inst_1 (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u2} 𝕜 (OrderedRing.toPartialOrder.{u2} 𝕜 _inst_2)) _inst_3 _inst_4 _inst_5 A B) -> (IsExposed.{u2, u1} 𝕜 E _inst_1 (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u2} 𝕜 (OrderedRing.toPartialOrder.{u2} 𝕜 _inst_2)) _inst_3 _inst_4 _inst_5 B A) -> (Eq.{succ u1} (Set.{u1} E) A B)
Case conversion may be inaccurate. Consider using '#align is_exposed.antisymm IsExposed.antisymmₓ'. -/
protected theorem antisymm (hB : IsExposed 𝕜 A B) (hA : IsExposed 𝕜 B A) : A = B :=
  hA.Subset.antisymm hB.Subset
#align is_exposed.antisymm IsExposed.antisymm

/- warning: is_exposed.mono -> IsExposed.mono is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} 𝕜] [_inst_2 : OrderedRing.{u1} 𝕜] [_inst_3 : AddCommMonoid.{u2} E] [_inst_4 : TopologicalSpace.{u2} E] [_inst_5 : Module.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)) _inst_3] {A : Set.{u2} E} {B : Set.{u2} E} {C : Set.{u2} E}, (IsExposed.{u1, u2} 𝕜 E _inst_1 (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (OrderedRing.toOrderedAddCommGroup.{u1} 𝕜 _inst_2))) _inst_3 _inst_4 _inst_5 A C) -> (HasSubset.Subset.{u2} (Set.{u2} E) (Set.hasSubset.{u2} E) B A) -> (HasSubset.Subset.{u2} (Set.{u2} E) (Set.hasSubset.{u2} E) C B) -> (IsExposed.{u1, u2} 𝕜 E _inst_1 (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (OrderedRing.toOrderedAddCommGroup.{u1} 𝕜 _inst_2))) _inst_3 _inst_4 _inst_5 B C)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} 𝕜] [_inst_2 : OrderedRing.{u2} 𝕜] [_inst_3 : AddCommMonoid.{u1} E] [_inst_4 : TopologicalSpace.{u1} E] [_inst_5 : Module.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)) _inst_3] {A : Set.{u1} E} {B : Set.{u1} E} {C : Set.{u1} E}, (IsExposed.{u2, u1} 𝕜 E _inst_1 (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u2} 𝕜 (OrderedRing.toPartialOrder.{u2} 𝕜 _inst_2)) _inst_3 _inst_4 _inst_5 A C) -> (HasSubset.Subset.{u1} (Set.{u1} E) (Set.instHasSubsetSet.{u1} E) B A) -> (HasSubset.Subset.{u1} (Set.{u1} E) (Set.instHasSubsetSet.{u1} E) C B) -> (IsExposed.{u2, u1} 𝕜 E _inst_1 (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u2} 𝕜 (OrderedRing.toPartialOrder.{u2} 𝕜 _inst_2)) _inst_3 _inst_4 _inst_5 B C)
Case conversion may be inaccurate. Consider using '#align is_exposed.mono IsExposed.monoₓ'. -/
/- `is_exposed` is *not* transitive: Consider a (topologically) open cube with vertices
`A₀₀₀, ..., A₁₁₁` and add to it the triangle `A₀₀₀A₀₀₁A₀₁₀`. Then `A₀₀₁A₀₁₀` is an exposed subset
of `A₀₀₀A₀₀₁A₀₁₀` which is an exposed subset of the cube, but `A₀₀₁A₀₁₀` is not itself an exposed
subset of the cube. -/
protected theorem mono (hC : IsExposed 𝕜 A C) (hBA : B ⊆ A) (hCB : C ⊆ B) : IsExposed 𝕜 B C :=
  by
  rintro ⟨w, hw⟩
  obtain ⟨l, rfl⟩ := hC ⟨w, hw⟩
  exact
    ⟨l,
      subset.antisymm (fun x hx => ⟨hCB hx, fun y hy => hx.2 y (hBA hy)⟩) fun x hx =>
        ⟨hBA hx.1, fun y hy => (hw.2 y hy).trans (hx.2 w (hCB hw))⟩⟩
#align is_exposed.mono IsExposed.mono

/- warning: is_exposed.eq_inter_halfspace' -> IsExposed.eq_inter_halfspace' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_exposed.eq_inter_halfspace' IsExposed.eq_inter_halfspace'ₓ'. -/
/-- If `B` is a nonempty exposed subset of `A`, then `B` is the intersection of `A` with some closed
halfspace. The converse is *not* true. It would require that the corresponding open halfspace
doesn't intersect `A`. -/
theorem eq_inter_halfspace' {A B : Set E} (hAB : IsExposed 𝕜 A B) (hB : B.Nonempty) :
    ∃ l : E →L[𝕜] 𝕜, ∃ a, B = { x ∈ A | a ≤ l x } :=
  by
  obtain ⟨l, rfl⟩ := hAB hB
  obtain ⟨w, hw⟩ := hB
  exact
    ⟨l, l w,
      subset.antisymm (fun x hx => ⟨hx.1, hx.2 w hw.1⟩) fun x hx =>
        ⟨hx.1, fun y hy => (hw.2 y hy).trans hx.2⟩⟩
#align is_exposed.eq_inter_halfspace' IsExposed.eq_inter_halfspace'

/- warning: is_exposed.eq_inter_halfspace -> IsExposed.eq_inter_halfspace is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_exposed.eq_inter_halfspace IsExposed.eq_inter_halfspaceₓ'. -/
/-- For nontrivial `𝕜`, if `B` is an exposed subset of `A`, then `B` is the intersection of `A` with
some closed halfspace. The converse is *not* true. It would require that the corresponding open
halfspace doesn't intersect `A`. -/
theorem eq_inter_halfspace [Nontrivial 𝕜] {A B : Set E} (hAB : IsExposed 𝕜 A B) :
    ∃ l : E →L[𝕜] 𝕜, ∃ a, B = { x ∈ A | a ≤ l x } :=
  by
  obtain rfl | hB := B.eq_empty_or_nonempty
  · refine' ⟨0, 1, _⟩
    rw [eq_comm, eq_empty_iff_forall_not_mem]
    rintro x ⟨-, h⟩
    rw [ContinuousLinearMap.zero_apply] at h
    have : ¬(1 : 𝕜) ≤ 0 := not_le_of_lt zero_lt_one
    contradiction
  exact hAB.eq_inter_halfspace' hB
#align is_exposed.eq_inter_halfspace IsExposed.eq_inter_halfspace

/- warning: is_exposed.inter -> IsExposed.inter is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} 𝕜] [_inst_2 : OrderedRing.{u1} 𝕜] [_inst_3 : AddCommMonoid.{u2} E] [_inst_4 : TopologicalSpace.{u2} E] [_inst_5 : Module.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)) _inst_3] [_inst_6 : ContinuousAdd.{u1} 𝕜 _inst_1 (Distrib.toHasAdd.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)))] {A : Set.{u2} E} {B : Set.{u2} E} {C : Set.{u2} E}, (IsExposed.{u1, u2} 𝕜 E _inst_1 (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (OrderedRing.toOrderedAddCommGroup.{u1} 𝕜 _inst_2))) _inst_3 _inst_4 _inst_5 A B) -> (IsExposed.{u1, u2} 𝕜 E _inst_1 (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (OrderedRing.toOrderedAddCommGroup.{u1} 𝕜 _inst_2))) _inst_3 _inst_4 _inst_5 A C) -> (IsExposed.{u1, u2} 𝕜 E _inst_1 (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (OrderedRing.toOrderedAddCommGroup.{u1} 𝕜 _inst_2))) _inst_3 _inst_4 _inst_5 A (Inter.inter.{u2} (Set.{u2} E) (Set.hasInter.{u2} E) B C))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} 𝕜] [_inst_2 : OrderedRing.{u2} 𝕜] [_inst_3 : AddCommMonoid.{u1} E] [_inst_4 : TopologicalSpace.{u1} E] [_inst_5 : Module.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)) _inst_3] [_inst_6 : ContinuousAdd.{u2} 𝕜 _inst_1 (Distrib.toAdd.{u2} 𝕜 (NonUnitalNonAssocSemiring.toDistrib.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (OrderedRing.toRing.{u2} 𝕜 _inst_2))))))] {A : Set.{u1} E} {B : Set.{u1} E} {C : Set.{u1} E}, (IsExposed.{u2, u1} 𝕜 E _inst_1 (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u2} 𝕜 (OrderedRing.toPartialOrder.{u2} 𝕜 _inst_2)) _inst_3 _inst_4 _inst_5 A B) -> (IsExposed.{u2, u1} 𝕜 E _inst_1 (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u2} 𝕜 (OrderedRing.toPartialOrder.{u2} 𝕜 _inst_2)) _inst_3 _inst_4 _inst_5 A C) -> (IsExposed.{u2, u1} 𝕜 E _inst_1 (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u2} 𝕜 (OrderedRing.toPartialOrder.{u2} 𝕜 _inst_2)) _inst_3 _inst_4 _inst_5 A (Inter.inter.{u1} (Set.{u1} E) (Set.instInterSet.{u1} E) B C))
Case conversion may be inaccurate. Consider using '#align is_exposed.inter IsExposed.interₓ'. -/
protected theorem inter [ContinuousAdd 𝕜] {A B C : Set E} (hB : IsExposed 𝕜 A B)
    (hC : IsExposed 𝕜 A C) : IsExposed 𝕜 A (B ∩ C) :=
  by
  rintro ⟨w, hwB, hwC⟩
  obtain ⟨l₁, rfl⟩ := hB ⟨w, hwB⟩
  obtain ⟨l₂, rfl⟩ := hC ⟨w, hwC⟩
  refine' ⟨l₁ + l₂, subset.antisymm _ _⟩
  · rintro x ⟨⟨hxA, hxB⟩, ⟨-, hxC⟩⟩
    exact ⟨hxA, fun z hz => add_le_add (hxB z hz) (hxC z hz)⟩
  rintro x ⟨hxA, hx⟩
  refine' ⟨⟨hxA, fun y hy => _⟩, hxA, fun y hy => _⟩
  ·
    exact
      (add_le_add_iff_right (l₂ x)).1 ((add_le_add (hwB.2 y hy) (hwC.2 x hxA)).trans (hx w hwB.1))
  ·
    exact
      (add_le_add_iff_left (l₁ x)).1 (le_trans (add_le_add (hwB.2 x hxA) (hwC.2 y hy)) (hx w hwB.1))
#align is_exposed.inter IsExposed.inter

/- warning: is_exposed.sInter -> IsExposed.sInter is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} 𝕜] [_inst_2 : OrderedRing.{u1} 𝕜] [_inst_3 : AddCommMonoid.{u2} E] [_inst_4 : TopologicalSpace.{u2} E] [_inst_5 : Module.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)) _inst_3] {A : Set.{u2} E} [_inst_6 : ContinuousAdd.{u1} 𝕜 _inst_1 (Distrib.toHasAdd.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)))] {F : Finset.{u2} (Set.{u2} E)}, (Finset.Nonempty.{u2} (Set.{u2} E) F) -> (forall (B : Set.{u2} E), (Membership.Mem.{u2, u2} (Set.{u2} E) (Finset.{u2} (Set.{u2} E)) (Finset.hasMem.{u2} (Set.{u2} E)) B F) -> (IsExposed.{u1, u2} 𝕜 E _inst_1 (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (OrderedRing.toOrderedAddCommGroup.{u1} 𝕜 _inst_2))) _inst_3 _inst_4 _inst_5 A B)) -> (IsExposed.{u1, u2} 𝕜 E _inst_1 (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (OrderedRing.toOrderedAddCommGroup.{u1} 𝕜 _inst_2))) _inst_3 _inst_4 _inst_5 A (Set.sInter.{u2} E ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} (Set.{u2} E)) (Set.{u2} (Set.{u2} E)) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} (Set.{u2} E)) (Set.{u2} (Set.{u2} E)) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} (Set.{u2} E)) (Set.{u2} (Set.{u2} E)) (Finset.Set.hasCoeT.{u2} (Set.{u2} E)))) F)))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} 𝕜] [_inst_2 : OrderedRing.{u2} 𝕜] [_inst_3 : AddCommMonoid.{u1} E] [_inst_4 : TopologicalSpace.{u1} E] [_inst_5 : Module.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)) _inst_3] {A : Set.{u1} E} [_inst_6 : ContinuousAdd.{u2} 𝕜 _inst_1 (Distrib.toAdd.{u2} 𝕜 (NonUnitalNonAssocSemiring.toDistrib.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (OrderedRing.toRing.{u2} 𝕜 _inst_2))))))] {F : Finset.{u1} (Set.{u1} E)}, (Finset.Nonempty.{u1} (Set.{u1} E) F) -> (forall (B : Set.{u1} E), (Membership.mem.{u1, u1} (Set.{u1} E) (Finset.{u1} (Set.{u1} E)) (Finset.instMembershipFinset.{u1} (Set.{u1} E)) B F) -> (IsExposed.{u2, u1} 𝕜 E _inst_1 (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u2} 𝕜 (OrderedRing.toPartialOrder.{u2} 𝕜 _inst_2)) _inst_3 _inst_4 _inst_5 A B)) -> (IsExposed.{u2, u1} 𝕜 E _inst_1 (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u2} 𝕜 (OrderedRing.toPartialOrder.{u2} 𝕜 _inst_2)) _inst_3 _inst_4 _inst_5 A (Set.sInter.{u1} E (Finset.toSet.{u1} (Set.{u1} E) F)))
Case conversion may be inaccurate. Consider using '#align is_exposed.sInter IsExposed.sInterₓ'. -/
theorem sInter [ContinuousAdd 𝕜] {F : Finset (Set E)} (hF : F.Nonempty)
    (hAF : ∀ B ∈ F, IsExposed 𝕜 A B) : IsExposed 𝕜 A (⋂₀ F) :=
  by
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
  exact
    (hCF C (Finset.mem_insert_self C F)).inter
      (hF hFnemp fun B hB => hCF B (Finset.mem_insert_of_mem hB))
#align is_exposed.sInter IsExposed.sInter

/- warning: is_exposed.inter_left -> IsExposed.inter_left is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} 𝕜] [_inst_2 : OrderedRing.{u1} 𝕜] [_inst_3 : AddCommMonoid.{u2} E] [_inst_4 : TopologicalSpace.{u2} E] [_inst_5 : Module.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)) _inst_3] {A : Set.{u2} E} {B : Set.{u2} E} {C : Set.{u2} E}, (IsExposed.{u1, u2} 𝕜 E _inst_1 (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (OrderedRing.toOrderedAddCommGroup.{u1} 𝕜 _inst_2))) _inst_3 _inst_4 _inst_5 A C) -> (HasSubset.Subset.{u2} (Set.{u2} E) (Set.hasSubset.{u2} E) C B) -> (IsExposed.{u1, u2} 𝕜 E _inst_1 (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (OrderedRing.toOrderedAddCommGroup.{u1} 𝕜 _inst_2))) _inst_3 _inst_4 _inst_5 (Inter.inter.{u2} (Set.{u2} E) (Set.hasInter.{u2} E) A B) C)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} 𝕜] [_inst_2 : OrderedRing.{u2} 𝕜] [_inst_3 : AddCommMonoid.{u1} E] [_inst_4 : TopologicalSpace.{u1} E] [_inst_5 : Module.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)) _inst_3] {A : Set.{u1} E} {B : Set.{u1} E} {C : Set.{u1} E}, (IsExposed.{u2, u1} 𝕜 E _inst_1 (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u2} 𝕜 (OrderedRing.toPartialOrder.{u2} 𝕜 _inst_2)) _inst_3 _inst_4 _inst_5 A C) -> (HasSubset.Subset.{u1} (Set.{u1} E) (Set.instHasSubsetSet.{u1} E) C B) -> (IsExposed.{u2, u1} 𝕜 E _inst_1 (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u2} 𝕜 (OrderedRing.toPartialOrder.{u2} 𝕜 _inst_2)) _inst_3 _inst_4 _inst_5 (Inter.inter.{u1} (Set.{u1} E) (Set.instInterSet.{u1} E) A B) C)
Case conversion may be inaccurate. Consider using '#align is_exposed.inter_left IsExposed.inter_leftₓ'. -/
theorem inter_left (hC : IsExposed 𝕜 A C) (hCB : C ⊆ B) : IsExposed 𝕜 (A ∩ B) C :=
  by
  rintro ⟨w, hw⟩
  obtain ⟨l, rfl⟩ := hC ⟨w, hw⟩
  exact
    ⟨l,
      subset.antisymm (fun x hx => ⟨⟨hx.1, hCB hx⟩, fun y hy => hx.2 y hy.1⟩)
        fun x ⟨⟨hxC, _⟩, hx⟩ => ⟨hxC, fun y hy => (hw.2 y hy).trans (hx w ⟨hC.subset hw, hCB hw⟩)⟩⟩
#align is_exposed.inter_left IsExposed.inter_left

/- warning: is_exposed.inter_right -> IsExposed.inter_right is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} 𝕜] [_inst_2 : OrderedRing.{u1} 𝕜] [_inst_3 : AddCommMonoid.{u2} E] [_inst_4 : TopologicalSpace.{u2} E] [_inst_5 : Module.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)) _inst_3] {A : Set.{u2} E} {B : Set.{u2} E} {C : Set.{u2} E}, (IsExposed.{u1, u2} 𝕜 E _inst_1 (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (OrderedRing.toOrderedAddCommGroup.{u1} 𝕜 _inst_2))) _inst_3 _inst_4 _inst_5 B C) -> (HasSubset.Subset.{u2} (Set.{u2} E) (Set.hasSubset.{u2} E) C A) -> (IsExposed.{u1, u2} 𝕜 E _inst_1 (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (OrderedRing.toOrderedAddCommGroup.{u1} 𝕜 _inst_2))) _inst_3 _inst_4 _inst_5 (Inter.inter.{u2} (Set.{u2} E) (Set.hasInter.{u2} E) A B) C)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} 𝕜] [_inst_2 : OrderedRing.{u2} 𝕜] [_inst_3 : AddCommMonoid.{u1} E] [_inst_4 : TopologicalSpace.{u1} E] [_inst_5 : Module.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)) _inst_3] {A : Set.{u1} E} {B : Set.{u1} E} {C : Set.{u1} E}, (IsExposed.{u2, u1} 𝕜 E _inst_1 (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u2} 𝕜 (OrderedRing.toPartialOrder.{u2} 𝕜 _inst_2)) _inst_3 _inst_4 _inst_5 B C) -> (HasSubset.Subset.{u1} (Set.{u1} E) (Set.instHasSubsetSet.{u1} E) C A) -> (IsExposed.{u2, u1} 𝕜 E _inst_1 (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u2} 𝕜 (OrderedRing.toPartialOrder.{u2} 𝕜 _inst_2)) _inst_3 _inst_4 _inst_5 (Inter.inter.{u1} (Set.{u1} E) (Set.instInterSet.{u1} E) A B) C)
Case conversion may be inaccurate. Consider using '#align is_exposed.inter_right IsExposed.inter_rightₓ'. -/
theorem inter_right (hC : IsExposed 𝕜 B C) (hCA : C ⊆ A) : IsExposed 𝕜 (A ∩ B) C :=
  by
  rw [inter_comm]
  exact hC.inter_left hCA
#align is_exposed.inter_right IsExposed.inter_right

/- warning: is_exposed.is_closed -> IsExposed.isClosed is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} 𝕜] [_inst_2 : OrderedRing.{u1} 𝕜] [_inst_3 : AddCommMonoid.{u2} E] [_inst_4 : TopologicalSpace.{u2} E] [_inst_5 : Module.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)) _inst_3] [_inst_6 : OrderClosedTopology.{u1} 𝕜 _inst_1 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (OrderedRing.toOrderedAddCommGroup.{u1} 𝕜 _inst_2)))] {A : Set.{u2} E} {B : Set.{u2} E}, (IsExposed.{u1, u2} 𝕜 E _inst_1 (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (OrderedRing.toOrderedAddCommGroup.{u1} 𝕜 _inst_2))) _inst_3 _inst_4 _inst_5 A B) -> (IsClosed.{u2} E _inst_4 A) -> (IsClosed.{u2} E _inst_4 B)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} 𝕜] [_inst_2 : OrderedRing.{u2} 𝕜] [_inst_3 : AddCommMonoid.{u1} E] [_inst_4 : TopologicalSpace.{u1} E] [_inst_5 : Module.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)) _inst_3] [_inst_6 : OrderClosedTopology.{u2} 𝕜 _inst_1 (PartialOrder.toPreorder.{u2} 𝕜 (OrderedRing.toPartialOrder.{u2} 𝕜 _inst_2))] {A : Set.{u1} E} {B : Set.{u1} E}, (IsExposed.{u2, u1} 𝕜 E _inst_1 (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u2} 𝕜 (OrderedRing.toPartialOrder.{u2} 𝕜 _inst_2)) _inst_3 _inst_4 _inst_5 A B) -> (IsClosed.{u1} E _inst_4 A) -> (IsClosed.{u1} E _inst_4 B)
Case conversion may be inaccurate. Consider using '#align is_exposed.is_closed IsExposed.isClosedₓ'. -/
protected theorem isClosed [OrderClosedTopology 𝕜] {A B : Set E} (hAB : IsExposed 𝕜 A B)
    (hA : IsClosed A) : IsClosed B :=
  by
  obtain rfl | hB := B.eq_empty_or_nonempty
  · simp
  obtain ⟨l, a, rfl⟩ := hAB.eq_inter_halfspace' hB
  exact hA.is_closed_le continuousOn_const l.continuous.continuous_on
#align is_exposed.is_closed IsExposed.isClosed

/- warning: is_exposed.is_compact -> IsExposed.isCompact is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} 𝕜] [_inst_2 : OrderedRing.{u1} 𝕜] [_inst_3 : AddCommMonoid.{u2} E] [_inst_4 : TopologicalSpace.{u2} E] [_inst_5 : Module.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)) _inst_3] [_inst_6 : OrderClosedTopology.{u1} 𝕜 _inst_1 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (OrderedRing.toOrderedAddCommGroup.{u1} 𝕜 _inst_2)))] [_inst_7 : T2Space.{u2} E _inst_4] {A : Set.{u2} E} {B : Set.{u2} E}, (IsExposed.{u1, u2} 𝕜 E _inst_1 (Ring.toSemiring.{u1} 𝕜 (OrderedRing.toRing.{u1} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (OrderedRing.toOrderedAddCommGroup.{u1} 𝕜 _inst_2))) _inst_3 _inst_4 _inst_5 A B) -> (IsCompact.{u2} E _inst_4 A) -> (IsCompact.{u2} E _inst_4 B)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} 𝕜] [_inst_2 : OrderedRing.{u2} 𝕜] [_inst_3 : AddCommMonoid.{u1} E] [_inst_4 : TopologicalSpace.{u1} E] [_inst_5 : Module.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)) _inst_3] [_inst_6 : OrderClosedTopology.{u2} 𝕜 _inst_1 (PartialOrder.toPreorder.{u2} 𝕜 (OrderedRing.toPartialOrder.{u2} 𝕜 _inst_2))] [_inst_7 : T2Space.{u1} E _inst_4] {A : Set.{u1} E} {B : Set.{u1} E}, (IsExposed.{u2, u1} 𝕜 E _inst_1 (OrderedSemiring.toSemiring.{u2} 𝕜 (OrderedRing.toOrderedSemiring.{u2} 𝕜 _inst_2)) (PartialOrder.toPreorder.{u2} 𝕜 (OrderedRing.toPartialOrder.{u2} 𝕜 _inst_2)) _inst_3 _inst_4 _inst_5 A B) -> (IsCompact.{u1} E _inst_4 A) -> (IsCompact.{u1} E _inst_4 B)
Case conversion may be inaccurate. Consider using '#align is_exposed.is_compact IsExposed.isCompactₓ'. -/
protected theorem isCompact [OrderClosedTopology 𝕜] [T2Space E] {A B : Set E}
    (hAB : IsExposed 𝕜 A B) (hA : IsCompact A) : IsCompact B :=
  isCompact_of_isClosed_subset hA (hAB.IsClosed hA.IsClosed) hAB.Subset
#align is_exposed.is_compact IsExposed.isCompact

end IsExposed

variable (𝕜)

#print Set.exposedPoints /-
/-- A point is exposed with respect to `A` iff there exists an hyperplane whose intersection with
`A` is exactly that point. -/
def Set.exposedPoints (A : Set E) : Set E :=
  { x ∈ A | ∃ l : E →L[𝕜] 𝕜, ∀ y ∈ A, l y ≤ l x ∧ (l x ≤ l y → y = x) }
#align set.exposed_points Set.exposedPoints
-/

variable {𝕜}

/- warning: exposed_point_def -> exposed_point_def is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align exposed_point_def exposed_point_defₓ'. -/
theorem exposed_point_def :
    x ∈ A.exposedPoints 𝕜 ↔ x ∈ A ∧ ∃ l : E →L[𝕜] 𝕜, ∀ y ∈ A, l y ≤ l x ∧ (l x ≤ l y → y = x) :=
  Iff.rfl
#align exposed_point_def exposed_point_def

#print exposedPoints_subset /-
theorem exposedPoints_subset : A.exposedPoints 𝕜 ⊆ A := fun x hx => hx.1
#align exposed_points_subset exposedPoints_subset
-/

#print exposedPoints_empty /-
@[simp]
theorem exposedPoints_empty : (∅ : Set E).exposedPoints 𝕜 = ∅ :=
  subset_empty_iff.1 exposedPoints_subset
#align exposed_points_empty exposedPoints_empty
-/

#print mem_exposedPoints_iff_exposed_singleton /-
/-- Exposed points exactly correspond to exposed singletons. -/
theorem mem_exposedPoints_iff_exposed_singleton : x ∈ A.exposedPoints 𝕜 ↔ IsExposed 𝕜 A {x} :=
  by
  use fun ⟨hxA, l, hl⟩ h =>
    ⟨l,
      Eq.symm <|
        eq_singleton_iff_unique_mem.2
          ⟨⟨hxA, fun y hy => (hl y hy).1⟩, fun z hz => (hl z hz.1).2 (hz.2 x hxA)⟩⟩
  rintro h
  obtain ⟨l, hl⟩ := h ⟨x, mem_singleton _⟩
  rw [eq_comm, eq_singleton_iff_unique_mem] at hl
  exact
    ⟨hl.1.1, l, fun y hy =>
      ⟨hl.1.2 y hy, fun hxy => hl.2 y ⟨hy, fun z hz => (hl.1.2 z hz).trans hxy⟩⟩⟩
#align mem_exposed_points_iff_exposed_singleton mem_exposedPoints_iff_exposed_singleton
-/

end OrderedRing

section LinearOrderedRing

variable {𝕜 : Type _} {E : Type _} [TopologicalSpace 𝕜] [LinearOrderedRing 𝕜] [AddCommMonoid E]
  [TopologicalSpace E] [Module 𝕜 E] {A B C : Set E}

namespace IsExposed

/- warning: is_exposed.convex -> IsExposed.convex is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} 𝕜] [_inst_2 : LinearOrderedRing.{u1} 𝕜] [_inst_3 : AddCommMonoid.{u2} E] [_inst_4 : TopologicalSpace.{u2} E] [_inst_5 : Module.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (StrictOrderedRing.toRing.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 _inst_2))) _inst_3] {A : Set.{u2} E} {B : Set.{u2} E}, (IsExposed.{u1, u2} 𝕜 E _inst_1 (Ring.toSemiring.{u1} 𝕜 (StrictOrderedRing.toRing.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 _inst_2))) (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 _inst_2)))) _inst_3 _inst_4 _inst_5 A B) -> (Convex.{u1, u2} 𝕜 E (StrictOrderedSemiring.toOrderedSemiring.{u1} 𝕜 (StrictOrderedRing.toStrictOrderedSemiring.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 _inst_2))) _inst_3 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_3))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (StrictOrderedRing.toRing.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 _inst_2))))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_3))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (StrictOrderedRing.toRing.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 _inst_2)))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_3))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (StrictOrderedRing.toRing.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 _inst_2))) _inst_3 _inst_5)))) A) -> (Convex.{u1, u2} 𝕜 E (StrictOrderedSemiring.toOrderedSemiring.{u1} 𝕜 (StrictOrderedRing.toStrictOrderedSemiring.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 _inst_2))) _inst_3 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_3))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (StrictOrderedRing.toRing.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 _inst_2))))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_3))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (StrictOrderedRing.toRing.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 _inst_2)))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_3))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (StrictOrderedRing.toRing.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 _inst_2))) _inst_3 _inst_5)))) B)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} 𝕜] [_inst_2 : LinearOrderedRing.{u2} 𝕜] [_inst_3 : AddCommMonoid.{u1} E] [_inst_4 : TopologicalSpace.{u1} E] [_inst_5 : Module.{u2, u1} 𝕜 E (StrictOrderedSemiring.toSemiring.{u2} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} 𝕜 (LinearOrderedRing.toLinearOrderedSemiring.{u2} 𝕜 _inst_2))) _inst_3] {A : Set.{u1} E} {B : Set.{u1} E}, (IsExposed.{u2, u1} 𝕜 E _inst_1 (StrictOrderedSemiring.toSemiring.{u2} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} 𝕜 (LinearOrderedRing.toLinearOrderedSemiring.{u2} 𝕜 _inst_2))) (PartialOrder.toPreorder.{u2} 𝕜 (StrictOrderedRing.toPartialOrder.{u2} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u2} 𝕜 _inst_2))) _inst_3 _inst_4 _inst_5 A B) -> (Convex.{u2, u1} 𝕜 E (StrictOrderedSemiring.toOrderedSemiring.{u2} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} 𝕜 (LinearOrderedRing.toLinearOrderedSemiring.{u2} 𝕜 _inst_2))) _inst_3 (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_3)) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (MonoidWithZero.toZero.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (StrictOrderedSemiring.toSemiring.{u2} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} 𝕜 (LinearOrderedRing.toLinearOrderedSemiring.{u2} 𝕜 _inst_2))))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_3)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (StrictOrderedSemiring.toSemiring.{u2} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} 𝕜 (LinearOrderedRing.toLinearOrderedSemiring.{u2} 𝕜 _inst_2)))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_3)) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (StrictOrderedSemiring.toSemiring.{u2} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} 𝕜 (LinearOrderedRing.toLinearOrderedSemiring.{u2} 𝕜 _inst_2))) _inst_3 _inst_5)))) A) -> (Convex.{u2, u1} 𝕜 E (StrictOrderedSemiring.toOrderedSemiring.{u2} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} 𝕜 (LinearOrderedRing.toLinearOrderedSemiring.{u2} 𝕜 _inst_2))) _inst_3 (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_3)) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (MonoidWithZero.toZero.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (StrictOrderedSemiring.toSemiring.{u2} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} 𝕜 (LinearOrderedRing.toLinearOrderedSemiring.{u2} 𝕜 _inst_2))))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_3)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (StrictOrderedSemiring.toSemiring.{u2} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} 𝕜 (LinearOrderedRing.toLinearOrderedSemiring.{u2} 𝕜 _inst_2)))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_3)) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (StrictOrderedSemiring.toSemiring.{u2} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} 𝕜 (LinearOrderedRing.toLinearOrderedSemiring.{u2} 𝕜 _inst_2))) _inst_3 _inst_5)))) B)
Case conversion may be inaccurate. Consider using '#align is_exposed.convex IsExposed.convexₓ'. -/
protected theorem convex (hAB : IsExposed 𝕜 A B) (hA : Convex 𝕜 A) : Convex 𝕜 B :=
  by
  obtain rfl | hB := B.eq_empty_or_nonempty
  · exact convex_empty
  obtain ⟨l, rfl⟩ := hAB hB
  exact fun x₁ hx₁ x₂ hx₂ a b ha hb hab =>
    ⟨hA hx₁.1 hx₂.1 ha hb hab, fun y hy =>
      ((l.to_linear_map.concave_on convex_univ).convex_ge _ ⟨mem_univ _, hx₁.2 y hy⟩
          ⟨mem_univ _, hx₂.2 y hy⟩ ha hb hab).2⟩
#align is_exposed.convex IsExposed.convex

/- warning: is_exposed.is_extreme -> IsExposed.isExtreme is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} 𝕜] [_inst_2 : LinearOrderedRing.{u1} 𝕜] [_inst_3 : AddCommMonoid.{u2} E] [_inst_4 : TopologicalSpace.{u2} E] [_inst_5 : Module.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (StrictOrderedRing.toRing.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 _inst_2))) _inst_3] {A : Set.{u2} E} {B : Set.{u2} E}, (IsExposed.{u1, u2} 𝕜 E _inst_1 (Ring.toSemiring.{u1} 𝕜 (StrictOrderedRing.toRing.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 _inst_2))) (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 _inst_2)))) _inst_3 _inst_4 _inst_5 A B) -> (IsExtreme.{u1, u2} 𝕜 E (StrictOrderedSemiring.toOrderedSemiring.{u1} 𝕜 (StrictOrderedRing.toStrictOrderedSemiring.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 _inst_2))) _inst_3 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_3))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (StrictOrderedRing.toRing.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 _inst_2))))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_3))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (StrictOrderedRing.toRing.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 _inst_2)))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_3))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (StrictOrderedRing.toRing.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 _inst_2))) _inst_3 _inst_5)))) A B)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} 𝕜] [_inst_2 : LinearOrderedRing.{u2} 𝕜] [_inst_3 : AddCommMonoid.{u1} E] [_inst_4 : TopologicalSpace.{u1} E] [_inst_5 : Module.{u2, u1} 𝕜 E (StrictOrderedSemiring.toSemiring.{u2} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} 𝕜 (LinearOrderedRing.toLinearOrderedSemiring.{u2} 𝕜 _inst_2))) _inst_3] {A : Set.{u1} E} {B : Set.{u1} E}, (IsExposed.{u2, u1} 𝕜 E _inst_1 (StrictOrderedSemiring.toSemiring.{u2} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} 𝕜 (LinearOrderedRing.toLinearOrderedSemiring.{u2} 𝕜 _inst_2))) (PartialOrder.toPreorder.{u2} 𝕜 (StrictOrderedRing.toPartialOrder.{u2} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u2} 𝕜 _inst_2))) _inst_3 _inst_4 _inst_5 A B) -> (IsExtreme.{u2, u1} 𝕜 E (StrictOrderedSemiring.toOrderedSemiring.{u2} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} 𝕜 (LinearOrderedRing.toLinearOrderedSemiring.{u2} 𝕜 _inst_2))) _inst_3 (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_3)) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (MonoidWithZero.toZero.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (StrictOrderedSemiring.toSemiring.{u2} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} 𝕜 (LinearOrderedRing.toLinearOrderedSemiring.{u2} 𝕜 _inst_2))))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_3)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (StrictOrderedSemiring.toSemiring.{u2} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} 𝕜 (LinearOrderedRing.toLinearOrderedSemiring.{u2} 𝕜 _inst_2)))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_3)) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (StrictOrderedSemiring.toSemiring.{u2} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} 𝕜 (LinearOrderedRing.toLinearOrderedSemiring.{u2} 𝕜 _inst_2))) _inst_3 _inst_5)))) A B)
Case conversion may be inaccurate. Consider using '#align is_exposed.is_extreme IsExposed.isExtremeₓ'. -/
protected theorem isExtreme (hAB : IsExposed 𝕜 A B) : IsExtreme 𝕜 A B :=
  by
  refine' ⟨hAB.subset, fun x₁ hx₁A x₂ hx₂A x hxB hx => _⟩
  obtain ⟨l, rfl⟩ := hAB ⟨x, hxB⟩
  have hl : ConvexOn 𝕜 univ l := l.to_linear_map.convex_on convex_univ
  have hlx₁ := hxB.2 x₁ hx₁A
  have hlx₂ := hxB.2 x₂ hx₂A
  refine' ⟨⟨hx₁A, fun y hy => _⟩, ⟨hx₂A, fun y hy => _⟩⟩
  · have := @ConvexOn.le_left_of_right_le 𝕜 E 𝕜 _ _ _
    rw [hlx₁.antisymm (hl.le_left_of_right_le (mem_univ _) (mem_univ _) hx hlx₂)]
    exact hxB.2 y hy
  · rw [hlx₂.antisymm (hl.le_right_of_left_le (mem_univ _) (mem_univ _) hx hlx₁)]
    exact hxB.2 y hy
#align is_exposed.is_extreme IsExposed.isExtreme

end IsExposed

#print exposedPoints_subset_extremePoints /-
theorem exposedPoints_subset_extremePoints : A.exposedPoints 𝕜 ⊆ A.extremePoints 𝕜 := fun x hx =>
  mem_extremePoints_iff_extreme_singleton.2 (mem_exposedPoints_iff_exposed_singleton.1 hx).IsExtreme
#align exposed_points_subset_extreme_points exposedPoints_subset_extremePoints
-/

end LinearOrderedRing

