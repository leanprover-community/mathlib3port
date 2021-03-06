/-
Copyright (c) 2021 YaΓ«l Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YaΓ«l Dillies, Bhavik Mehta
-/
import Mathbin.Analysis.Convex.Hull

/-!
# Extreme sets

This file defines extreme sets and extreme points for sets in a module.

An extreme set of `A` is a subset of `A` that is as far as it can get in any outward direction: If
point `x` is in it and point `y β A`, then the line passing through `x` and `y` leaves `A` at `x`.
This is an analytic notion of "being on the side of". It is weaker than being exposed (see
`is_exposed.is_extreme`).

## Main declarations

* `is_extreme π A B`: States that `B` is an extreme set of `A` (in the literature, `A` is often
  implicit).
* `set.extreme_points π A`: Set of extreme points of `A` (corresponding to extreme singletons).
* `convex.mem_extreme_points_iff_convex_diff`: A useful equivalent condition to being an extreme
  point: `x` is an extreme point iff `A \ {x}` is convex.

## Implementation notes

The exact definition of extremeness has been carefully chosen so as to make as many lemmas
unconditional (in particular, the Krein-Milman theorem doesn't need the set to be convex!).
In practice, `A` is often assumed to be a convex set.

## References

See chapter 8 of [Barry Simon, *Convexity*][simon2011]

## TODO

Define intrinsic frontier and prove lemmas related to extreme sets and points.

More not-yet-PRed stuff is available on the branch `sperner_again`.
-/


open Classical Affine

open Set

variable (π : Type _) {E : Type _}

section HasSmul

variable [OrderedSemiring π] [AddCommMonoidβ E] [HasSmul π E]

/-- A set `B` is an extreme subset of `A` if `B β A` and all points of `B` only belong to open
segments whose ends are in `B`. -/
def IsExtreme (A B : Set E) : Prop :=
  B β A β§ β β¦xββ¦, xβ β A β β β¦xββ¦, xβ β A β β β¦xβ¦, x β B β x β OpenSegment π xβ xβ β xβ β B β§ xβ β B

/-- A point `x` is an extreme point of a set `A` if `x` belongs to no open segment with ends in
`A`, except for the obvious `open_segment x x`. -/
def Set.ExtremePoints (A : Set E) : Set E :=
  { x β A | β β¦xββ¦, xβ β A β β β¦xββ¦, xβ β A β x β OpenSegment π xβ xβ β xβ = x β§ xβ = x }

@[refl]
protected theorem IsExtreme.refl (A : Set E) : IsExtreme π A A :=
  β¨Subset.rfl, fun xβ hxβA xβ hxβA x hxA hx => β¨hxβA, hxβAβ©β©

variable {π} {A B C : Set E} {x : E}

protected theorem IsExtreme.rfl : IsExtreme π A A :=
  IsExtreme.refl π A

@[trans]
protected theorem IsExtreme.trans (hAB : IsExtreme π A B) (hBC : IsExtreme π B C) : IsExtreme π A C := by
  refine' β¨subset.trans hBC.1 hAB.1, fun xβ hxβA xβ hxβA x hxC hx => _β©
  obtain β¨hxβB, hxβBβ© := hAB.2 hxβA hxβA (hBC.1 hxC) hx
  exact hBC.2 hxβB hxβB hxC hx

protected theorem IsExtreme.antisymm : AntiSymmetric (IsExtreme π : Set E β Set E β Prop) := fun A B hAB hBA =>
  Subset.antisymm hBA.1 hAB.1

instance : IsPartialOrder (Set E) (IsExtreme π) where
  refl := IsExtreme.refl π
  trans := fun A B C => IsExtreme.trans
  antisymm := IsExtreme.antisymm

theorem IsExtreme.inter (hAB : IsExtreme π A B) (hAC : IsExtreme π A C) : IsExtreme π A (B β© C) := by
  use subset.trans (inter_subset_left _ _) hAB.1
  rintro xβ hxβA xβ hxβA x β¨hxB, hxCβ© hx
  obtain β¨hxβB, hxβBβ© := hAB.2 hxβA hxβA hxB hx
  obtain β¨hxβC, hxβCβ© := hAC.2 hxβA hxβA hxC hx
  exact β¨β¨hxβB, hxβCβ©, hxβB, hxβCβ©

protected theorem IsExtreme.mono (hAC : IsExtreme π A C) (hBA : B β A) (hCB : C β B) : IsExtreme π B C :=
  β¨hCB, fun xβ hxβB xβ hxβB x hxC hx => hAC.2 (hBA hxβB) (hBA hxβB) hxC hxβ©

theorem is_extreme_Inter {ΞΉ : Type _} [Nonempty ΞΉ] {F : ΞΉ β Set E} (hAF : β i : ΞΉ, IsExtreme π A (F i)) :
    IsExtreme π A (β i : ΞΉ, F i) := by
  obtain i := Classical.arbitrary ΞΉ
  refine' β¨Inter_subset_of_subset i (hAF i).1, fun xβ hxβA xβ hxβA x hxF hx => _β©
  simp_rw [mem_Inter] at hxFβ’
  have h := fun i => (hAF i).2 hxβA hxβA (hxF i) hx
  exact β¨fun i => (h i).1, fun i => (h i).2β©

theorem is_extreme_bInter {F : Set (Set E)} (hF : F.Nonempty) (hAF : β, β B β F, β, IsExtreme π A B) :
    IsExtreme π A (β B β F, B) := by
  obtain β¨B, hBβ© := hF
  refine' β¨(bInter_subset_of_mem hB).trans (hAF B hB).1, fun xβ hxβA xβ hxβA x hxF hx => _β©
  simp_rw [mem_Interβ] at hxFβ’
  have h := fun B hB => (hAF B hB).2 hxβA hxβA (hxF B hB) hx
  exact β¨fun B hB => (h B hB).1, fun B hB => (h B hB).2β©

theorem is_extreme_sInter {F : Set (Set E)} (hF : F.Nonempty) (hAF : β, β B β F, β, IsExtreme π A B) :
    IsExtreme π A (ββ F) := by
  obtain β¨B, hBβ© := hF
  refine' β¨(sInter_subset_of_mem hB).trans (hAF B hB).1, fun xβ hxβA xβ hxβA x hxF hx => _β©
  simp_rw [mem_sInter] at hxFβ’
  have h := fun B hB => (hAF B hB).2 hxβA hxβA (hxF B hB) hx
  exact β¨fun B hB => (h B hB).1, fun B hB => (h B hB).2β©

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (xβ xβ Β«expr β Β» A)
theorem extreme_points_def :
    x β A.ExtremePoints π β x β A β§ β (xβ xβ) (_ : xβ β A) (_ : xβ β A), x β OpenSegment π xβ xβ β xβ = x β§ xβ = x :=
  Iff.rfl

/-- x is an extreme point to A iff {x} is an extreme set of A. -/
theorem mem_extreme_points_iff_extreme_singleton : x β A.ExtremePoints π β IsExtreme π A {x} := by
  refine' β¨_, fun hx => β¨singleton_subset_iff.1 hx.1, fun xβ hxβ xβ hxβ => hx.2 hxβ hxβ rflβ©β©
  rintro β¨hxA, hAxβ©
  use singleton_subset_iff.2 hxA
  rintro xβ hxβA xβ hxβA y (rfl : y = x)
  exact hAx hxβA hxβA

theorem extreme_points_subset : A.ExtremePoints π β A := fun x hx => hx.1

@[simp]
theorem extreme_points_empty : (β : Set E).ExtremePoints π = β :=
  subset_empty_iff.1 extreme_points_subset

@[simp]
theorem extreme_points_singleton : ({x} : Set E).ExtremePoints π = {x} :=
  extreme_points_subset.antisymm <| singleton_subset_iff.2 β¨mem_singleton x, fun xβ hxβ xβ hxβ _ => β¨hxβ, hxββ©β©

theorem inter_extreme_points_subset_extreme_points_of_subset (hBA : B β A) :
    B β© A.ExtremePoints π β B.ExtremePoints π := fun x β¨hxB, hxAβ© =>
  β¨hxB, fun xβ hxβ xβ hxβ hx => hxA.2 (hBA hxβ) (hBA hxβ) hxβ©

theorem IsExtreme.extreme_points_subset_extreme_points (hAB : IsExtreme π A B) :
    B.ExtremePoints π β A.ExtremePoints π := fun x hx =>
  mem_extreme_points_iff_extreme_singleton.2 (hAB.trans (mem_extreme_points_iff_extreme_singleton.1 hx))

theorem IsExtreme.extreme_points_eq (hAB : IsExtreme π A B) : B.ExtremePoints π = B β© A.ExtremePoints π :=
  Subset.antisymm (fun x hx => β¨hx.1, hAB.extreme_points_subset_extreme_points hxβ©)
    (inter_extreme_points_subset_extreme_points_of_subset hAB.1)

end HasSmul

section OrderedSemiring

variable {π} [OrderedSemiring π] [AddCommGroupβ E] [Module π E] {A B : Set E} {x : E}

theorem IsExtreme.convex_diff (hA : Convex π A) (hAB : IsExtreme π A B) : Convex π (A \ B) :=
  convex_iff_open_segment_subset.2 fun xβ xβ β¨hxβA, hxβBβ© β¨hxβA, hxβBβ© x hx =>
    β¨hA.open_segment_subset hxβA hxβA hx, fun hxB => hxβB (hAB.2 hxβA hxβA hxB hx).1β©

end OrderedSemiring

section LinearOrderedRing

variable {π} [LinearOrderedRing π] [AddCommGroupβ E] [Module π E]

variable [DenselyOrdered π] [NoZeroSmulDivisors π E] {A B : Set E} {x : E}

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (xβ xβ Β«expr β Β» A)
/-- A useful restatement using `segment`: `x` is an extreme point iff the only (closed) segments
that contain it are those with `x` as one of their endpoints. -/
theorem mem_extreme_points_iff_forall_segment :
    x β A.ExtremePoints π β x β A β§ β (xβ xβ) (_ : xβ β A) (_ : xβ β A), x β Segment π xβ xβ β xβ = x β¨ xβ = x := by
  refine' and_congr_right fun hxA => forallβ_congrβ fun xβ hβ xβ hβ => _
  constructor
  Β· rw [β insert_endpoints_open_segment]
    rintro H (rfl | rfl | hx)
    exacts[Or.inl rfl, Or.inr rfl, Or.inl <| (H hx).1]
    
  Β· intro H hx
    rcases H (open_segment_subset_segment _ _ _ hx) with (rfl | rfl)
    exacts[β¨rfl, (left_mem_open_segment_iff.1 hx).symmβ©, β¨right_mem_open_segment_iff.1 hx, rflβ©]
    

theorem Convex.mem_extreme_points_iff_convex_diff (hA : Convex π A) :
    x β A.ExtremePoints π β x β A β§ Convex π (A \ {x}) := by
  use fun hx => β¨hx.1, (mem_extreme_points_iff_extreme_singleton.1 hx).convex_diff hAβ©
  rintro β¨hxA, hAxβ©
  refine' mem_extreme_points_iff_forall_segment.2 β¨hxA, fun xβ hxβ xβ hxβ hx => _β©
  rw [convex_iff_segment_subset] at hAx
  by_contra' h
  exact (hAx β¨hxβ, fun hxβ => h.1 (mem_singleton_iff.2 hxβ)β© β¨hxβ, fun hxβ => h.2 (mem_singleton_iff.2 hxβ)β© hx).2 rfl

theorem Convex.mem_extreme_points_iff_mem_diff_convex_hull_diff (hA : Convex π A) :
    x β A.ExtremePoints π β x β A \ convexHull π (A \ {x}) := by
  rw [hA.mem_extreme_points_iff_convex_diff, hA.convex_remove_iff_not_mem_convex_hull_remove, mem_diff]

theorem extreme_points_convex_hull_subset : (convexHull π A).ExtremePoints π β A := by
  rintro x hx
  rw [(convex_convex_hull π _).mem_extreme_points_iff_convex_diff] at hx
  by_contra
  exact (convex_hull_min (subset_diff.2 β¨subset_convex_hull π _, disjoint_singleton_right.2 hβ©) hx.2 hx.1).2 rfl
  infer_instance

end LinearOrderedRing

