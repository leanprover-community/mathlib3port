/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Patrick Massot

! This file was ported from Lean 3 source module topology.nhds_set
! leanprover-community/mathlib commit 1e05171a5e8cf18d98d9cf7b207540acb044acae
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Basic

/-!
# Neighborhoods of a set

In this file we define the filter `𝓝ˢ s` or `nhds_set s` consisting of all neighborhoods of a set
`s`.

## Main Properties

There are a couple different notions equivalent to `s ∈ 𝓝ˢ t`:
* `s ⊆ interior t` using `subset_interior_iff_mem_nhds_set`
* `∀ (x : α), x ∈ t → s ∈ 𝓝 x` using `mem_nhds_set_iff_forall`
* `∃ U : set α, is_open U ∧ t ⊆ U ∧ U ⊆ s` using `mem_nhds_set_iff_exists`

Furthermore, we have the following results:
* `monotone_nhds_set`: `𝓝ˢ` is monotone
* In T₁-spaces, `𝓝ˢ`is strictly monotone and hence injective:
  `strict_mono_nhds_set`/`injective_nhds_set`. These results are in `topology.separation`.
-/


open Set Filter

open TopologicalSpace Filter

variable {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] {s t s₁ s₂ t₁ t₂ : Set α} {x : α}

/-- The filter of neighborhoods of a set in a topological space. -/
def nhdsSet (s : Set α) : Filter α :=
  supₛ (nhds '' s)
#align nhds_set nhdsSet

-- mathport name: nhds_set
scoped[TopologicalSpace] notation "𝓝ˢ" => nhdsSet

theorem nhds_set_diagonal (α) [TopologicalSpace (α × α)] : 𝓝ˢ (diagonal α) = ⨆ x, 𝓝 (x, x) :=
  by
  rw [nhdsSet, ← range_diag, ← range_comp]
  rfl
#align nhds_set_diagonal nhds_set_diagonal

theorem mem_nhds_set_iff_forall : s ∈ 𝓝ˢ t ↔ ∀ x : α, x ∈ t → s ∈ 𝓝 x := by
  simp_rw [nhdsSet, Filter.mem_Sup, ball_image_iff]
#align mem_nhds_set_iff_forall mem_nhds_set_iff_forall

theorem bUnion_mem_nhds_set {t : α → Set α} (h : ∀ x ∈ s, t x ∈ 𝓝 x) : (⋃ x ∈ s, t x) ∈ 𝓝ˢ s :=
  mem_nhds_set_iff_forall.2 fun x hx => mem_of_superset (h x hx) (subset_unionᵢ₂ x hx)
#align bUnion_mem_nhds_set bUnion_mem_nhds_set

theorem subset_interior_iff_mem_nhds_set : s ⊆ interior t ↔ t ∈ 𝓝ˢ s := by
  simp_rw [mem_nhds_set_iff_forall, subset_interior_iff_nhds]
#align subset_interior_iff_mem_nhds_set subset_interior_iff_mem_nhds_set

theorem mem_nhds_set_iff_exists : s ∈ 𝓝ˢ t ↔ ∃ U : Set α, IsOpen U ∧ t ⊆ U ∧ U ⊆ s := by
  rw [← subset_interior_iff_mem_nhds_set, subset_interior_iff]
#align mem_nhds_set_iff_exists mem_nhds_set_iff_exists

theorem has_basis_nhds_set (s : Set α) : (𝓝ˢ s).HasBasis (fun U => IsOpen U ∧ s ⊆ U) fun U => U :=
  ⟨fun t => by simp [mem_nhds_set_iff_exists, and_assoc']⟩
#align has_basis_nhds_set has_basis_nhds_set

theorem IsOpen.mem_nhds_set (hU : IsOpen s) : s ∈ 𝓝ˢ t ↔ t ⊆ s := by
  rw [← subset_interior_iff_mem_nhds_set, interior_eq_iff_is_open.mpr hU]
#align is_open.mem_nhds_set IsOpen.mem_nhds_set

theorem principal_le_nhds_set : 𝓟 s ≤ 𝓝ˢ s := fun s hs =>
  (subset_interior_iff_mem_nhds_set.mpr hs).trans interior_subset
#align principal_le_nhds_set principal_le_nhds_set

@[simp]
theorem nhds_set_eq_principal_iff : 𝓝ˢ s = 𝓟 s ↔ IsOpen s := by
  rw [← principal_le_nhds_set.le_iff_eq, le_principal_iff, mem_nhds_set_iff_forall,
    is_open_iff_mem_nhds]
#align nhds_set_eq_principal_iff nhds_set_eq_principal_iff

alias nhds_set_eq_principal_iff ↔ _ IsOpen.nhds_set_eq

@[simp]
theorem nhds_set_interior : 𝓝ˢ (interior s) = 𝓟 (interior s) :=
  is_open_interior.nhds_set_eq
#align nhds_set_interior nhds_set_interior

@[simp]
theorem nhds_set_singleton : 𝓝ˢ {x} = 𝓝 x := by
  ext
  rw [← subset_interior_iff_mem_nhds_set, ← mem_interior_iff_mem_nhds, singleton_subset_iff]
#align nhds_set_singleton nhds_set_singleton

theorem mem_nhds_set_interior : s ∈ 𝓝ˢ (interior s) :=
  subset_interior_iff_mem_nhds_set.mp Subset.rfl
#align mem_nhds_set_interior mem_nhds_set_interior

@[simp]
theorem nhds_set_empty : 𝓝ˢ (∅ : Set α) = ⊥ := by rw [is_open_empty.nhds_set_eq, principal_empty]
#align nhds_set_empty nhds_set_empty

theorem mem_nhds_set_empty : s ∈ 𝓝ˢ (∅ : Set α) := by simp
#align mem_nhds_set_empty mem_nhds_set_empty

@[simp]
theorem nhds_set_univ : 𝓝ˢ (univ : Set α) = ⊤ := by rw [is_open_univ.nhds_set_eq, principal_univ]
#align nhds_set_univ nhds_set_univ

@[mono]
theorem nhds_set_mono (h : s ⊆ t) : 𝓝ˢ s ≤ 𝓝ˢ t :=
  supₛ_le_supₛ <| image_subset _ h
#align nhds_set_mono nhds_set_mono

theorem monotone_nhds_set : Monotone (𝓝ˢ : Set α → Filter α) := fun s t => nhds_set_mono
#align monotone_nhds_set monotone_nhds_set

theorem nhds_le_nhds_set (h : x ∈ s) : 𝓝 x ≤ 𝓝ˢ s :=
  le_supₛ <| mem_image_of_mem _ h
#align nhds_le_nhds_set nhds_le_nhds_set

@[simp]
theorem nhds_set_union (s t : Set α) : 𝓝ˢ (s ∪ t) = 𝓝ˢ s ⊔ 𝓝ˢ t := by
  simp only [nhdsSet, image_union, supₛ_union]
#align nhds_set_union nhds_set_union

theorem union_mem_nhds_set (h₁ : s₁ ∈ 𝓝ˢ t₁) (h₂ : s₂ ∈ 𝓝ˢ t₂) : s₁ ∪ s₂ ∈ 𝓝ˢ (t₁ ∪ t₂) :=
  by
  rw [nhds_set_union]
  exact union_mem_sup h₁ h₂
#align union_mem_nhds_set union_mem_nhds_set

/-- Preimage of a set neighborhood of `t` under a continuous map `f` is a set neighborhood of `s`
provided that `f` maps `s` to `t`.  -/
theorem Continuous.tendsto_nhds_set {f : α → β} {t : Set β} (hf : Continuous f)
    (hst : MapsTo f s t) : Tendsto f (𝓝ˢ s) (𝓝ˢ t) :=
  ((has_basis_nhds_set s).tendsto_iff (has_basis_nhds_set t)).mpr fun U hU =>
    ⟨f ⁻¹' U, ⟨hU.1.Preimage hf, hst.mono Subset.rfl hU.2⟩, fun x => id⟩
#align continuous.tendsto_nhds_set Continuous.tendsto_nhds_set

