import Mathbin.Analysis.Convex.Hull

/-!
# Extreme sets

This file defines extreme sets and extreme points for sets in a module.

An extreme set of `A` is a subset of `A` that is as far as it can get in any outward direction: If
point `x` is in it and point `y ∈ A`, then the line passing through `x` and `y` leaves `A` at `x`.
This is an analytic notion of "being on the side of". It is weaker than being exposed (see
`is_exposed.is_extreme`).

## Main declarations

* `is_extreme 𝕜 A B`: States that `B` is an extreme set of `A` (in the literature, `A` is often
  implicit).
* `set.extreme_points 𝕜 A`: Set of extreme points of `A` (corresponding to extreme singletons).
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


open_locale Classical Affine

open Set

variable(𝕜 : Type _){E : Type _}

section HasScalar

variable[OrderedSemiring 𝕜][AddCommMonoidₓ E][HasScalar 𝕜 E]

/-- A set `B` is an extreme subset of `A` if `B ⊆ A` and all points of `B` only belong to open
segments whose ends are in `B`. -/
def IsExtreme (A B : Set E) : Prop :=
  B ⊆ A ∧ ∀ x₁ x₂ _ : x₁ ∈ A _ : x₂ ∈ A, ∀ x _ : x ∈ B, x ∈ OpenSegment 𝕜 x₁ x₂ → x₁ ∈ B ∧ x₂ ∈ B

/-- A point `x` is an extreme point of a set `A` if `x` belongs to no open segment with ends in
`A`, except for the obvious `open_segment x x`. -/
def Set.ExtremePoints (A : Set E) : Set E :=
  { x ∈ A | ∀ x₁ x₂ _ : x₁ ∈ A _ : x₂ ∈ A, x ∈ OpenSegment 𝕜 x₁ x₂ → x₁ = x ∧ x₂ = x }

@[refl]
protected theorem IsExtreme.refl (A : Set E) : IsExtreme 𝕜 A A :=
  ⟨subset.rfl, fun x₁ x₂ hx₁A hx₂A x hxA hx => ⟨hx₁A, hx₂A⟩⟩

variable{𝕜}{A B C : Set E}{x : E}

protected theorem IsExtreme.rfl : IsExtreme 𝕜 A A :=
  IsExtreme.refl 𝕜 A

@[trans]
protected theorem IsExtreme.trans (hAB : IsExtreme 𝕜 A B) (hBC : IsExtreme 𝕜 B C) : IsExtreme 𝕜 A C :=
  by 
    use subset.trans hBC.1 hAB.1
    rintro x₁ x₂ hx₁A hx₂A x hxC hx 
    obtain ⟨hx₁B, hx₂B⟩ := hAB.2 x₁ x₂ hx₁A hx₂A x (hBC.1 hxC) hx 
    exact hBC.2 x₁ x₂ hx₁B hx₂B x hxC hx

protected theorem IsExtreme.antisymm : AntiSymmetric (IsExtreme 𝕜 : Set E → Set E → Prop) :=
  fun A B hAB hBA => subset.antisymm hBA.1 hAB.1

instance  : IsPartialOrder (Set E) (IsExtreme 𝕜) :=
  { refl := IsExtreme.refl 𝕜, trans := fun A B C => IsExtreme.trans, antisymm := IsExtreme.antisymm }

theorem IsExtreme.inter (hAB : IsExtreme 𝕜 A B) (hAC : IsExtreme 𝕜 A C) : IsExtreme 𝕜 A (B ∩ C) :=
  by 
    use subset.trans (inter_subset_left _ _) hAB.1
    rintro x₁ x₂ hx₁A hx₂A x ⟨hxB, hxC⟩ hx 
    obtain ⟨hx₁B, hx₂B⟩ := hAB.2 x₁ x₂ hx₁A hx₂A x hxB hx 
    obtain ⟨hx₁C, hx₂C⟩ := hAC.2 x₁ x₂ hx₁A hx₂A x hxC hx 
    exact ⟨⟨hx₁B, hx₁C⟩, hx₂B, hx₂C⟩

protected theorem IsExtreme.mono (hAC : IsExtreme 𝕜 A C) (hBA : B ⊆ A) (hCB : C ⊆ B) : IsExtreme 𝕜 B C :=
  ⟨hCB, fun x₁ x₂ hx₁B hx₂B x hxC hx => hAC.2 x₁ x₂ (hBA hx₁B) (hBA hx₂B) x hxC hx⟩

theorem is_extreme_Inter {ι : Type _} [Nonempty ι] {F : ι → Set E} (hAF : ∀ i : ι, IsExtreme 𝕜 A (F i)) :
  IsExtreme 𝕜 A (⋂i : ι, F i) :=
  by 
    obtain i := Classical.arbitrary ι 
    use Inter_subset_of_subset i (hAF i).1
    rintro x₁ x₂ hx₁A hx₂A x hxF hx 
    simpRw [mem_Inter]  at hxF⊢
    have h := fun i => (hAF i).2 x₁ x₂ hx₁A hx₂A x (hxF i) hx 
    exact ⟨fun i => (h i).1, fun i => (h i).2⟩

theorem is_extreme_bInter {F : Set (Set E)} (hF : F.nonempty) (hAF : ∀ B _ : B ∈ F, IsExtreme 𝕜 A B) :
  IsExtreme 𝕜 A (⋂(B : _)(_ : B ∈ F), B) :=
  by 
    obtain ⟨B, hB⟩ := hF 
    refine' ⟨(bInter_subset_of_mem hB).trans (hAF B hB).1, fun x₁ x₂ hx₁A hx₂A x hxF hx => _⟩
    simpRw [mem_bInter_iff]  at hxF⊢
    have h := fun B hB => (hAF B hB).2 x₁ x₂ hx₁A hx₂A x (hxF B hB) hx 
    exact ⟨fun B hB => (h B hB).1, fun B hB => (h B hB).2⟩

theorem is_extreme_sInter {F : Set (Set E)} (hF : F.nonempty) (hAF : ∀ B _ : B ∈ F, IsExtreme 𝕜 A B) :
  IsExtreme 𝕜 A (⋂₀F) :=
  by 
    obtain ⟨B, hB⟩ := hF 
    refine' ⟨(sInter_subset_of_mem hB).trans (hAF B hB).1, fun x₁ x₂ hx₁A hx₂A x hxF hx => _⟩
    simpRw [mem_sInter]  at hxF⊢
    have h := fun B hB => (hAF B hB).2 x₁ x₂ hx₁A hx₂A x (hxF B hB) hx 
    exact ⟨fun B hB => (h B hB).1, fun B hB => (h B hB).2⟩

theorem extreme_points_def :
  x ∈ A.extreme_points 𝕜 ↔ x ∈ A ∧ ∀ x₁ x₂ _ : x₁ ∈ A _ : x₂ ∈ A, x ∈ OpenSegment 𝕜 x₁ x₂ → x₁ = x ∧ x₂ = x :=
  Iff.rfl

/-- x is an extreme point to A iff {x} is an extreme set of A. -/
theorem mem_extreme_points_iff_extreme_singleton : x ∈ A.extreme_points 𝕜 ↔ IsExtreme 𝕜 A {x} :=
  by 
    refine' ⟨_, fun hx => ⟨singleton_subset_iff.1 hx.1, fun x₁ x₂ hx₁ hx₂ => hx.2 x₁ x₂ hx₁ hx₂ x rfl⟩⟩
    rintro ⟨hxA, hAx⟩
    use singleton_subset_iff.2 hxA 
    rintro x₁ x₂ hx₁A hx₂A y (rfl : y = x)
    exact hAx x₁ x₂ hx₁A hx₂A

theorem extreme_points_subset : A.extreme_points 𝕜 ⊆ A :=
  fun x hx => hx.1

@[simp]
theorem extreme_points_empty : (∅ : Set E).ExtremePoints 𝕜 = ∅ :=
  subset_empty_iff.1 extreme_points_subset

@[simp]
theorem extreme_points_singleton : ({x} : Set E).ExtremePoints 𝕜 = {x} :=
  extreme_points_subset.antisymm$ singleton_subset_iff.2 ⟨mem_singleton x, fun x₁ x₂ hx₁ hx₂ _ => ⟨hx₁, hx₂⟩⟩

theorem inter_extreme_points_subset_extreme_points_of_subset (hBA : B ⊆ A) :
  B ∩ A.extreme_points 𝕜 ⊆ B.extreme_points 𝕜 :=
  fun x ⟨hxB, hxA⟩ => ⟨hxB, fun x₁ x₂ hx₁ hx₂ hx => hxA.2 x₁ x₂ (hBA hx₁) (hBA hx₂) hx⟩

theorem IsExtreme.extreme_points_subset_extreme_points (hAB : IsExtreme 𝕜 A B) :
  B.extreme_points 𝕜 ⊆ A.extreme_points 𝕜 :=
  fun x hx => mem_extreme_points_iff_extreme_singleton.2 (hAB.trans (mem_extreme_points_iff_extreme_singleton.1 hx))

theorem IsExtreme.extreme_points_eq (hAB : IsExtreme 𝕜 A B) : B.extreme_points 𝕜 = B ∩ A.extreme_points 𝕜 :=
  subset.antisymm (fun x hx => ⟨hx.1, hAB.extreme_points_subset_extreme_points hx⟩)
    (inter_extreme_points_subset_extreme_points_of_subset hAB.1)

end HasScalar

section OrderedSemiring

variable{𝕜}[OrderedSemiring 𝕜][AddCommGroupₓ E][Module 𝕜 E]{A B : Set E}{x : E}

theorem IsExtreme.convex_diff (hA : Convex 𝕜 A) (hAB : IsExtreme 𝕜 A B) : Convex 𝕜 (A \ B) :=
  convex_iff_open_segment_subset.2
    fun x₁ x₂ ⟨hx₁A, hx₁B⟩ ⟨hx₂A, hx₂B⟩ x hx =>
      ⟨hA.open_segment_subset hx₁A hx₂A hx, fun hxB => hx₁B (hAB.2 x₁ x₂ hx₁A hx₂A x hxB hx).1⟩

end OrderedSemiring

section LinearOrderedField

variable{𝕜}[LinearOrderedField 𝕜][AddCommGroupₓ E][Module 𝕜 E]{A B : Set E}{x : E}

-- error in Analysis.Convex.Extreme: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contra: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
/-- A useful restatement using `segment`: `x` is an extreme point iff the only (closed) segments
that contain it are those with `x` as one of their endpoints. -/
theorem mem_extreme_points_iff_forall_segment
[no_zero_smul_divisors 𝕜 E] : «expr ↔ »(«expr ∈ »(x, A.extreme_points 𝕜), «expr ∧ »(«expr ∈ »(x, A), ∀
  x₁ x₂ «expr ∈ » A, «expr ∈ »(x, segment 𝕜 x₁ x₂) → «expr ∨ »(«expr = »(x₁, x), «expr = »(x₂, x)))) :=
begin
  split,
  { rintro ["⟨", ident hxA, ",", ident hAx, "⟩"],
    use [expr hxA],
    rintro [ident x₁, ident x₂, ident hx₁, ident hx₂, ident hx],
    by_contra [],
    push_neg ["at", ident h],
    exact [expr h.1 (hAx _ _ hx₁ hx₂ (mem_open_segment_of_ne_left_right 𝕜 h.1 h.2 hx)).1] },
  rintro ["⟨", ident hxA, ",", ident hAx, "⟩"],
  use [expr hxA],
  rintro [ident x₁, ident x₂, ident hx₁, ident hx₂, ident hx],
  obtain [ident rfl, "|", ident rfl, ":=", expr hAx x₁ x₂ hx₁ hx₂ (open_segment_subset_segment 𝕜 _ _ hx)],
  { exact [expr ⟨rfl, (left_mem_open_segment_iff.1 hx).symm⟩] },
  exact [expr ⟨right_mem_open_segment_iff.1 hx, rfl⟩]
end

-- error in Analysis.Convex.Extreme: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contra: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem convex.mem_extreme_points_iff_convex_diff
(hA : convex 𝕜 A) : «expr ↔ »(«expr ∈ »(x, A.extreme_points 𝕜), «expr ∧ »(«expr ∈ »(x, A), convex 𝕜 «expr \ »(A, {x}))) :=
begin
  use [expr λ hx, ⟨hx.1, (mem_extreme_points_iff_extreme_singleton.1 hx).convex_diff hA⟩],
  rintro ["⟨", ident hxA, ",", ident hAx, "⟩"],
  refine [expr mem_extreme_points_iff_forall_segment.2 ⟨hxA, λ x₁ x₂ hx₁ hx₂ hx, _⟩],
  rw [expr convex_iff_segment_subset] ["at", ident hAx],
  by_contra [],
  push_neg ["at", ident h],
  exact [expr (hAx ⟨hx₁, λ hx₁, h.1 (mem_singleton_iff.2 hx₁)⟩ ⟨hx₂, λ hx₂, h.2 (mem_singleton_iff.2 hx₂)⟩ hx).2 rfl]
end

theorem Convex.mem_extreme_points_iff_mem_diff_convex_hull_diff (hA : Convex 𝕜 A) :
  x ∈ A.extreme_points 𝕜 ↔ x ∈ A \ convexHull 𝕜 (A \ {x}) :=
  by 
    rw [hA.mem_extreme_points_iff_convex_diff, hA.convex_remove_iff_not_mem_convex_hull_remove, mem_diff]

-- error in Analysis.Convex.Extreme: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contra: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem extreme_points_convex_hull_subset : «expr ⊆ »((convex_hull 𝕜 A).extreme_points 𝕜, A) :=
begin
  rintro [ident x, ident hx],
  rw [expr (convex_convex_hull 𝕜 _).mem_extreme_points_iff_convex_diff] ["at", ident hx],
  by_contra [],
  exact [expr (convex_hull_min (subset_diff.2 ⟨subset_convex_hull 𝕜 _, disjoint_singleton_right.2 h⟩) hx.2 hx.1).2 rfl]
end

end LinearOrderedField

