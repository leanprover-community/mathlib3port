/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Patrick Massot
-/
import Mathbin.Topology.Basic

/-!
# Neighborhoods of a set

In this file we define the filter `๐หข s` or `nhds_set s` consisting of all neighborhoods of a set
`s`.

## Main Properties

There are a couple different notions equivalent to `s โ ๐หข t`:
* `s โ interior t` using `subset_interior_iff_mem_nhds_set`
* `โ (x : ฮฑ), x โ t โ s โ ๐ x` using `mem_nhds_set_iff_forall`
* `โ U : set ฮฑ, is_open U โง t โ U โง U โ s` using `mem_nhds_set_iff_exists`

Furthermore, we have the following results:
* `monotone_nhds_set`: `๐หข` is monotone
* In Tโ-spaces, `๐หข`is strictly monotone and hence injective:
  `strict_mono_nhds_set`/`injective_nhds_set`. These results are in `topology.separation`.
-/


open Set Filter

open TopologicalSpace

variable {ฮฑ : Type _} [TopologicalSpace ฮฑ] {s t sโ sโ tโ tโ : Set ฮฑ} {x : ฮฑ}

/-- The filter of neighborhoods of a set in a topological space. -/
def nhdsSet (s : Set ฮฑ) : Filter ฮฑ :=
  sup (nhds '' s)

-- mathport name: ยซexpr๐หขยป
localized [TopologicalSpace] notation "๐หข" => nhdsSet

theorem mem_nhds_set_iff_forall : s โ ๐หข t โ โ x : ฮฑ, x โ t โ s โ ๐ x := by
  simp_rw [nhdsSet, Filter.mem_Sup, ball_image_iff]

theorem subset_interior_iff_mem_nhds_set : s โ Interior t โ t โ ๐หข s := by
  simp_rw [mem_nhds_set_iff_forall, subset_interior_iff_nhds]

theorem mem_nhds_set_iff_exists : s โ ๐หข t โ โ U : Set ฮฑ, IsOpen U โง t โ U โง U โ s := by
  rw [โ subset_interior_iff_mem_nhds_set, subset_interior_iff]

theorem has_basis_nhds_set (s : Set ฮฑ) : (๐หข s).HasBasis (fun U => IsOpen U โง s โ U) fun U => U :=
  โจfun t => by
    simp [โ mem_nhds_set_iff_exists, โ and_assoc]โฉ

theorem IsOpen.mem_nhds_set (hU : IsOpen s) : s โ ๐หข t โ t โ s := by
  rw [โ subset_interior_iff_mem_nhds_set, interior_eq_iff_open.mpr hU]

@[simp]
theorem nhds_set_singleton : ๐หข {x} = ๐ x := by
  ext
  rw [โ subset_interior_iff_mem_nhds_set, โ mem_interior_iff_mem_nhds, singleton_subset_iff]

theorem mem_nhds_set_interior : s โ ๐หข (Interior s) :=
  subset_interior_iff_mem_nhds_set.mp Subset.rfl

theorem mem_nhds_set_empty : s โ ๐หข (โ : Set ฮฑ) :=
  subset_interior_iff_mem_nhds_set.mp <| empty_subset _

@[simp]
theorem nhds_set_empty : ๐หข (โ : Set ฮฑ) = โฅ := by
  ext
  simp [โ mem_nhds_set_empty]

@[simp]
theorem nhds_set_univ : ๐หข (Univ : Set ฮฑ) = โค := by
  ext
  rw [โ subset_interior_iff_mem_nhds_set, univ_subset_iff, interior_eq_univ, mem_top]

theorem monotone_nhds_set : Monotone (๐หข : Set ฮฑ โ Filter ฮฑ) := fun s t hst => Sup_le_Sup <| image_subset _ hst

@[simp]
theorem nhds_set_union (s t : Set ฮฑ) : ๐หข (s โช t) = ๐หข sโ๐หข t := by
  simp only [โ nhdsSet, โ image_union, โ Sup_union]

theorem union_mem_nhds_set (hโ : sโ โ ๐หข tโ) (hโ : sโ โ ๐หข tโ) : sโ โช sโ โ ๐หข (tโ โช tโ) := by
  rw [nhds_set_union]
  exact union_mem_sup hโ hโ

