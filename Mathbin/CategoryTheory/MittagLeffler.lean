/-
Copyright (c) 2022 Rémi Bottinelli, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli, Junyan Xu

! This file was ported from Lean 3 source module category_theory.mittag_leffler
! leanprover-community/mathlib commit 740acc0e6f9adf4423f92a485d0456fc271482da
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Filtered
import Mathbin.Data.Set.Finite

/-!
# The Mittag-Leffler condition

This files defines the Mittag-Leffler condition for cofiltered systems and (TODO) other properties
of such systems and their sections.

## Main definitions

Given a functor `F : J ⥤ Type v`:

* For `j : J`, `F.eventual_range j` is the intersections of all ranges of morphisms `F.map f`
  where `f` has codomain `j`.
* `F.is_mittag_leffler` states that the functor `F` satisfies the Mittag-Leffler
  condition: the ranges of morphisms `F.map f` (with `f` having codomain `j`) stabilize.
* If `J` is cofiltered `F.to_eventual_ranges` is the subfunctor of `F` obtained by restriction
  to `F.eventual_range`.
* `F.to_preimages` restricts a functor to preimages of a given set in some `F.obj i`. If `J` is
  cofiltered, then it is Mittag-Leffler if `F` is, see `is_mittag_leffler.to_preimages`.

## Main statements

* `is_mittag_leffler_of_exists_finite_range` shows that if `J` is cofiltered and for all `j`,
  there exists some `i` and `f : i ⟶ j` such that the range of `F.map f` is finite, then
  `F` is Mittag-Leffler.
* `to_eventual_ranges_surjective` shows that if `F` is Mittag-Leffler, then `F.to_eventual_ranges`
  has all morphisms `F.map f` surjective.

## Todo

* Specialize to inverse systems and fintype systems.
* Prove [Stacks: Lemma 0597](https://stacks.math.columbia.edu/tag/0597)

## References

* [Stacks: Mittag-Leffler systems](https://stacks.math.columbia.edu/tag/0594)

## Tags

Mittag-Leffler, surjective, eventual range, inverse system,

-/


universe u v

namespace CategoryTheory

namespace Functor

open IsCofiltered Set FunctorToTypes

variable {J : Type u} [Category J] (F : J ⥤ Type v) {i j k : J} (s : Set (F.obj i))

/-- The eventual range of the functor `F : J ⥤ Type v` at index `j : J` is the intersection
of the ranges of all maps `F.map f` with `i : J` and `f : i ⟶ j`.
-/
def eventualRange (j : J) :=
  ⋂ (i) (f : i ⟶ j), range (F.map f)
#align category_theory.functor.eventual_range CategoryTheory.Functor.eventualRange

theorem mem_eventualRange_iff {x : F.obj j} :
    x ∈ F.eventualRange j ↔ ∀ ⦃i⦄ (f : i ⟶ j), x ∈ range (F.map f) :=
  mem_interᵢ₂
#align category_theory.functor.mem_eventual_range_iff CategoryTheory.Functor.mem_eventualRange_iff

/-- The functor `F : J ⥤ Type v` satisfies the Mittag-Leffler condition if for all `j : J`,
there exists some `i : J` and `f : i ⟶ j` such that for all `k : J` and `g : k ⟶ j`, the range
of `F.map f` is contained in that of `F.map g`;
in other words (see `is_mittag_leffler_iff_eventual_range`), the eventual range at `j` is attained
by some `f : i ⟶ j`.
-/
def IsMittagLeffler : Prop :=
  ∀ j : J, ∃ (i : _)(f : i ⟶ j), ∀ ⦃k⦄ (g : k ⟶ j), range (F.map f) ⊆ range (F.map g)
#align category_theory.functor.is_mittag_leffler CategoryTheory.Functor.IsMittagLeffler

theorem isMittagLeffler_iff_eventualRange :
    F.IsMittagLeffler ↔ ∀ j : J, ∃ (i : _)(f : i ⟶ j), F.eventualRange j = range (F.map f) :=
  forall_congr' fun j =>
    exists₂_congr fun i f =>
      ⟨fun h => (interᵢ₂_subset _ _).antisymm <| subset_interᵢ₂ h, fun h => h ▸ interᵢ₂_subset⟩
#align category_theory.functor.is_mittag_leffler_iff_eventual_range CategoryTheory.Functor.isMittagLeffler_iff_eventualRange

theorem IsMittagLeffler.subset_image_eventualRange (h : F.IsMittagLeffler) (f : j ⟶ i) :
    F.eventualRange i ⊆ F.map f '' F.eventualRange j :=
  by
  obtain ⟨k, g, hg⟩ := F.is_mittag_leffler_iff_eventual_range.1 h j
  rw [hg]; intro x hx
  obtain ⟨x, rfl⟩ := F.mem_eventual_range_iff.1 hx (g ≫ f)
  refine' ⟨_, ⟨x, rfl⟩, by simpa only [F.map_comp] ⟩
#align category_theory.functor.is_mittag_leffler.subset_image_eventual_range CategoryTheory.Functor.IsMittagLeffler.subset_image_eventualRange

theorem eventualRange_eq_range_precomp (f : i ⟶ j) (g : j ⟶ k)
    (h : F.eventualRange k = range (F.map g)) : F.eventualRange k = range (F.map <| f ≫ g) :=
  by
  apply subset_antisymm
  · apply Inter₂_subset
  · rw [h, F.map_comp]
    apply range_comp_subset_range
#align category_theory.functor.eventual_range_eq_range_precomp CategoryTheory.Functor.eventualRange_eq_range_precomp

theorem isMittagLeffler_of_surjective (h : ∀ (i j : J) (f : i ⟶ j), (F.map f).Surjective) :
    F.IsMittagLeffler := fun j =>
  ⟨j, 𝟙 j, fun k g => by rw [map_id, types_id, range_id, (h k j g).range_eq]⟩
#align category_theory.functor.is_mittag_leffler_of_surjective CategoryTheory.Functor.isMittagLeffler_of_surjective

/-- The subfunctor of `F` obtained by restricting to the preimages of a set `s ∈ F.obj i`. -/
@[simps]
def toPreimages : J ⥤ Type v where
  obj j := ⋂ f : j ⟶ i, F.map f ⁻¹' s
  map j k g :=
    MapsTo.restrict (F.map g) _ _ fun x h =>
      by
      rw [mem_Inter] at h⊢; intro f
      rw [← mem_preimage, preimage_preimage]
      convert h (g ≫ f); rw [F.map_comp]; rfl
  map_id' j := by
    simp_rw [F.map_id]
    ext
    rfl
  map_comp' j k l f g := by
    simp_rw [F.map_comp]
    rfl
#align category_theory.functor.to_preimages CategoryTheory.Functor.toPreimages

variable [IsCofilteredOrEmpty J]

theorem eventualRange_mapsTo (f : j ⟶ i) :
    (F.eventualRange j).MapsTo (F.map f) (F.eventualRange i) := fun x hx =>
  by
  rw [mem_eventual_range_iff] at hx⊢
  intro k f'
  obtain ⟨l, g, g', he⟩ := cospan f f'
  obtain ⟨x, rfl⟩ := hx g
  rw [← map_comp_apply, he, F.map_comp]
  exact ⟨_, rfl⟩
#align category_theory.functor.eventual_range_maps_to CategoryTheory.Functor.eventualRange_mapsTo

theorem IsMittagLeffler.eq_image_eventualRange (h : F.IsMittagLeffler) (f : j ⟶ i) :
    F.eventualRange i = F.map f '' F.eventualRange j :=
  (h.subset_image_eventualRange F f).antisymm <| mapsTo'.1 (F.eventualRange_mapsTo f)
#align category_theory.functor.is_mittag_leffler.eq_image_eventual_range CategoryTheory.Functor.IsMittagLeffler.eq_image_eventualRange

theorem eventualRange_eq_iff {f : i ⟶ j} :
    F.eventualRange j = range (F.map f) ↔
      ∀ ⦃k⦄ (g : k ⟶ i), range (F.map f) ⊆ range (F.map <| g ≫ f) :=
  by
  rw [subset_antisymm_iff, eventual_range, and_iff_right (Inter₂_subset _ _), subset_Inter₂_iff]
  refine' ⟨fun h k g => h _ _, fun h j' f' => _⟩
  obtain ⟨k, g, g', he⟩ := cospan f f'
  refine' (h g).trans _
  rw [he, F.map_comp]
  apply range_comp_subset_range
#align category_theory.functor.eventual_range_eq_iff CategoryTheory.Functor.eventualRange_eq_iff

theorem isMittagLeffler_iff_subset_range_comp :
    F.IsMittagLeffler ↔
      ∀ j : J, ∃ (i : _)(f : i ⟶ j), ∀ ⦃k⦄ (g : k ⟶ i), range (F.map f) ⊆ range (F.map <| g ≫ f) :=
  by simp_rw [is_mittag_leffler_iff_eventual_range, eventual_range_eq_iff]
#align category_theory.functor.is_mittag_leffler_iff_subset_range_comp CategoryTheory.Functor.isMittagLeffler_iff_subset_range_comp

theorem IsMittagLeffler.toPreimages (h : F.IsMittagLeffler) : (F.toPreimages s).IsMittagLeffler :=
  (isMittagLeffler_iff_subset_range_comp _).2 fun j =>
    by
    obtain ⟨j₁, g₁, f₁, -⟩ := cone_objs i j
    obtain ⟨j₂, f₂, h₂⟩ := F.is_mittag_leffler_iff_eventual_range.1 h j₁
    refine' ⟨j₂, f₂ ≫ f₁, fun j₃ f₃ => _⟩
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    have : F.map f₂ x ∈ F.eventual_range j₁ := by
      rw [h₂]
      exact ⟨_, rfl⟩
    obtain ⟨y, hy, h₃⟩ := h.subset_image_eventual_range F (f₃ ≫ f₂) this
    refine' ⟨⟨y, mem_Inter.2 fun g₂ => _⟩, Subtype.ext _⟩
    · obtain ⟨j₄, f₄, h₄⟩ := cone_maps g₂ ((f₃ ≫ f₂) ≫ g₁)
      obtain ⟨y, rfl⟩ := F.mem_eventual_range_iff.1 hy f₄
      rw [← map_comp_apply] at h₃
      rw [mem_preimage, ← map_comp_apply, h₄, ← category.assoc, map_comp_apply, h₃, ←
        map_comp_apply]
      apply mem_Inter.1 hx
    · simp_rw [to_preimages_map, maps_to.coe_restrict_apply, Subtype.coe_mk]
      rw [← category.assoc, map_comp_apply, h₃, map_comp_apply]
#align category_theory.functor.is_mittag_leffler.to_preimages CategoryTheory.Functor.IsMittagLeffler.toPreimages

theorem isMittagLeffler_of_exists_finite_range
    (h : ∀ j : J, ∃ (i : _)(f : i ⟶ j), (range <| F.map f).Finite) : F.IsMittagLeffler := fun j =>
  by
  obtain ⟨i, hi, hf⟩ := h j
  obtain ⟨m, ⟨i, f, hm⟩, hmin⟩ :=
    finset.is_well_founded_lt.wf.has_min
      { s : Finset (F.obj j) | ∃ (i : _)(f : i ⟶ j), ↑s = range (F.map f) }
      ⟨_, i, hi, hf.coe_to_finset⟩
  refine'
    ⟨i, f, fun k g =>
      (directed_on_range.mp <| F.ranges_directed j).is_bot_of_is_min ⟨⟨i, f⟩, rfl⟩ _ _
        ⟨⟨k, g⟩, rfl⟩⟩
  rintro _ ⟨⟨k', g'⟩, rfl⟩ hl
  refine' (eq_of_le_of_not_lt hl _).ge
  have := hmin _ ⟨k', g', (m.finite_to_set.subset <| hm.substr hl).coe_toFinset⟩
  rwa [Finset.lt_iff_ssubset, ← Finset.coe_ssubset, Set.Finite.coe_toFinset, hm] at this
#align category_theory.functor.is_mittag_leffler_of_exists_finite_range CategoryTheory.Functor.isMittagLeffler_of_exists_finite_range

/-- The subfunctor of `F` obtained by restricting to the eventual range at each index.
-/
@[simps]
def toEventualRanges : J ⥤ Type v
    where
  obj j := F.eventualRange j
  map i j f := (F.eventualRange_mapsTo f).restrict _ _ _
  map_id' i := by
    simp_rw [F.map_id]
    ext
    rfl
  map_comp' _ _ _ _ _ := by
    simp_rw [F.map_comp]
    rfl
#align category_theory.functor.to_eventual_ranges CategoryTheory.Functor.toEventualRanges

/-- The sections of the functor `F : J ⥤ Type v` are in bijection with the sections of
`F.eventual_ranges`.
-/
def toEventualRangesSectionsEquiv : F.toEventualRanges.sections ≃ F.sections
    where
  toFun s := ⟨_, fun i j f => Subtype.coe_inj.2 <| s.Prop f⟩
  invFun s :=
    ⟨fun j => ⟨_, mem_interᵢ₂.2 fun i f => ⟨_, s.Prop f⟩⟩, fun i j f => Subtype.ext <| s.Prop f⟩
  left_inv _ := by
    ext
    rfl
  right_inv _ := by
    ext
    rfl
#align category_theory.functor.to_eventual_ranges_sections_equiv CategoryTheory.Functor.toEventualRangesSectionsEquiv

/--
If `F` satisfies the Mittag-Leffler condition, its restriction to eventual ranges is a surjective
functor.
-/
theorem surjective_toEventualRanges (h : F.IsMittagLeffler) (f : i ⟶ j) :
    (F.toEventualRanges.map f).Surjective := fun ⟨x, hx⟩ =>
  by
  obtain ⟨y, hy, rfl⟩ := h.subset_image_eventual_range F f hx
  exact ⟨⟨y, hy⟩, rfl⟩
#align category_theory.functor.surjective_to_eventual_ranges CategoryTheory.Functor.surjective_toEventualRanges

/-- If `F` is nonempty at each index and Mittag-Leffler, then so is `F.to_eventual_ranges`. -/
theorem toEventualRanges_nonempty (h : F.IsMittagLeffler) [∀ j : J, Nonempty (F.obj j)] (j : J) :
    Nonempty (F.toEventualRanges.obj j) :=
  by
  let ⟨i, f, h⟩ := F.isMittagLeffler_iff_eventualRange.1 h j
  rw [to_eventual_ranges_obj, h]
  infer_instance
#align category_theory.functor.to_eventual_ranges_nonempty CategoryTheory.Functor.toEventualRanges_nonempty

/-- If `F` has all arrows surjective, then it "factors through a poset". -/
theorem thin_diagram_of_surjective (Fsur : ∀ (i j : J) (f : i ⟶ j), (F.map f).Surjective) (i j)
    (f g : i ⟶ j) : F.map f = F.map g :=
  let ⟨k, φ, hφ⟩ := cone_maps f g
  (Fsur k i φ).injective_comp_right <| by simp_rw [← types_comp, ← F.map_comp, hφ]
#align category_theory.functor.thin_diagram_of_surjective CategoryTheory.Functor.thin_diagram_of_surjective

end Functor

end CategoryTheory

