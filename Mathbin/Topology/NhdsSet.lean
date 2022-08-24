/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Patrick Massot
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
  sup (nhds '' s)

-- mathport name: «expr𝓝ˢ»
localized [TopologicalSpace] notation "𝓝ˢ" => nhdsSet

theorem mem_nhds_set_iff_forall : s ∈ 𝓝ˢ t ↔ ∀ x : α, x ∈ t → s ∈ 𝓝 x := by
  simp_rw [nhdsSet, Filter.mem_Sup, ball_image_iff]

theorem subset_interior_iff_mem_nhds_set : s ⊆ Interior t ↔ t ∈ 𝓝ˢ s := by
  simp_rw [mem_nhds_set_iff_forall, subset_interior_iff_nhds]

theorem mem_nhds_set_iff_exists : s ∈ 𝓝ˢ t ↔ ∃ U : Set α, IsOpen U ∧ t ⊆ U ∧ U ⊆ s := by
  rw [← subset_interior_iff_mem_nhds_set, subset_interior_iff]

theorem has_basis_nhds_set (s : Set α) : (𝓝ˢ s).HasBasis (fun U => IsOpen U ∧ s ⊆ U) fun U => U :=
  ⟨fun t => by
    simp [mem_nhds_set_iff_exists, and_assoc]⟩

theorem IsOpen.mem_nhds_set (hU : IsOpen s) : s ∈ 𝓝ˢ t ↔ t ⊆ s := by
  rw [← subset_interior_iff_mem_nhds_set, interior_eq_iff_open.mpr hU]

theorem principal_le_nhds_set : 𝓟 s ≤ 𝓝ˢ s := fun s hs =>
  (subset_interior_iff_mem_nhds_set.mpr hs).trans interior_subset

@[simp]
theorem nhds_set_eq_principal_iff : 𝓝ˢ s = 𝓟 s ↔ IsOpen s := by
  rw [← principal_le_nhds_set.le_iff_eq, le_principal_iff, mem_nhds_set_iff_forall, is_open_iff_mem_nhds]

alias nhds_set_eq_principal_iff ↔ _ IsOpen.nhds_set_eq

@[simp]
theorem nhds_set_interior : 𝓝ˢ (Interior s) = 𝓟 (Interior s) :=
  is_open_interior.nhds_set_eq

@[simp]
theorem nhds_set_singleton : 𝓝ˢ {x} = 𝓝 x := by
  ext
  rw [← subset_interior_iff_mem_nhds_set, ← mem_interior_iff_mem_nhds, singleton_subset_iff]

theorem mem_nhds_set_interior : s ∈ 𝓝ˢ (Interior s) :=
  subset_interior_iff_mem_nhds_set.mp Subset.rfl

@[simp]
theorem nhds_set_empty : 𝓝ˢ (∅ : Set α) = ⊥ := by
  rw [is_open_empty.nhds_set_eq, principal_empty]

theorem mem_nhds_set_empty : s ∈ 𝓝ˢ (∅ : Set α) := by
  simp

@[simp]
theorem nhds_set_univ : 𝓝ˢ (Univ : Set α) = ⊤ := by
  rw [is_open_univ.nhds_set_eq, principal_univ]

theorem monotone_nhds_set : Monotone (𝓝ˢ : Set α → Filter α) := fun s t hst => Sup_le_Sup <| image_subset _ hst

@[simp]
theorem nhds_set_union (s t : Set α) : 𝓝ˢ (s ∪ t) = 𝓝ˢ s⊔𝓝ˢ t := by
  simp only [nhdsSet, image_union, Sup_union]

theorem union_mem_nhds_set (h₁ : s₁ ∈ 𝓝ˢ t₁) (h₂ : s₂ ∈ 𝓝ˢ t₂) : s₁ ∪ s₂ ∈ 𝓝ˢ (t₁ ∪ t₂) := by
  rw [nhds_set_union]
  exact union_mem_sup h₁ h₂

/-- Preimage of a set neighborhood of `t` under a continuous map `f` is a set neighborhood of `s`
provided that `f` maps `s` to `t`.  -/
theorem Continuous.tendsto_nhds_set {f : α → β} {t : Set β} (hf : Continuous f) (hst : MapsTo f s t) :
    Tendsto f (𝓝ˢ s) (𝓝ˢ t) :=
  ((has_basis_nhds_set s).tendsto_iff (has_basis_nhds_set t)).mpr fun U hU =>
    ⟨f ⁻¹' U, ⟨hU.1.Preimage hf, hst.mono Subset.rfl hU.2⟩, fun x => id⟩

