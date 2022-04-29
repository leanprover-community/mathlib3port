/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathbin.Analysis.LocallyConvex.Basic
import Mathbin.Order.Closure

/-!
# Balanced Core and Balanced Hull

## Main definitions

* `balanced_core`: The largest balanced subset of a set `s`.
* `balanced_hull`: The smallest balanced superset of a set `s`.

## Main statements

* `balanced_core_eq_Inter`: Characterization of the balanced core as an intersection over subsets.
* `nhds_basis_closed_balanced`: The closed balanced sets form a basis of the neighborhood filter.

## Implementation details

The balanced core and hull are implemented differently: for the core we take the obvious definition
of the union over all balanced sets that are contained in `s`, whereas for the hull, we take the
union over `r • s`, for `r` the scalars with `∥r∥ ≤ 1`. We show that `balanced_hull` has the
defining properties of a hull in `balanced.hull_minimal` and `subset_balanced_hull`.
For the core we need slightly stronger assumptions to obtain a characterization as an intersection,
this is `balanced_core_eq_Inter`.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

balanced
-/


open Set

open Pointwise TopologicalSpace Filter

variable {𝕜 E ι : Type _}

section BalancedHull

section SemiNormedRing

variable [SemiNormedRing 𝕜]

section HasScalar

variable [HasScalar 𝕜 E]

variable (𝕜)

/-- The largest balanced subset of `s`.-/
def BalancedCore (s : Set E) :=
  ⋃₀{ t : Set E | Balanced 𝕜 t ∧ t ⊆ s }

/-- Helper definition to prove `balanced_core_eq_Inter`-/
def BalancedCoreAux (s : Set E) :=
  ⋂ (r : 𝕜) (hr : 1 ≤ ∥r∥), r • s

/-- The smallest balanced superset of `s`.-/
def BalancedHull (s : Set E) :=
  ⋃ (r : 𝕜) (hr : ∥r∥ ≤ 1), r • s

variable {𝕜}

theorem balanced_core_subset (s : Set E) : BalancedCore 𝕜 s ⊆ s := by
  refine' sUnion_subset fun t ht => _
  simp only [mem_set_of_eq] at ht
  exact ht.2

theorem balanced_core_emptyset : BalancedCore 𝕜 (∅ : Set E) = ∅ :=
  Set.eq_empty_of_subset_empty (balanced_core_subset _)

theorem balanced_core_mem_iff {s : Set E} {x : E} : x ∈ BalancedCore 𝕜 s ↔ ∃ t : Set E, Balanced 𝕜 t ∧ t ⊆ s ∧ x ∈ t :=
  by
  simp_rw [BalancedCore, mem_sUnion, mem_set_of_eq, exists_prop, and_assoc]

theorem smul_balanced_core_subset (s : Set E) {a : 𝕜} (ha : ∥a∥ ≤ 1) : a • BalancedCore 𝕜 s ⊆ BalancedCore 𝕜 s := by
  rw [subset_def]
  intro x hx
  rw [mem_smul_set] at hx
  rcases hx with ⟨y, hy, hx⟩
  rw [balanced_core_mem_iff] at hy
  rcases hy with ⟨t, ht1, ht2, hy⟩
  rw [← hx]
  refine' ⟨t, _, ht1 a ha (smul_mem_smul_set hy)⟩
  rw [mem_set_of_eq]
  exact ⟨ht1, ht2⟩

theorem balanced_core_balanced (s : Set E) : Balanced 𝕜 (BalancedCore 𝕜 s) := fun _ => smul_balanced_core_subset s

/-- The balanced core of `t` is maximal in the sense that it contains any balanced subset
`s` of `t`.-/
theorem Balanced.subset_core_of_subset {s t : Set E} (hs : Balanced 𝕜 s) (h : s ⊆ t) : s ⊆ BalancedCore 𝕜 t := by
  refine' subset_sUnion_of_mem _
  rw [mem_set_of_eq]
  exact ⟨hs, h⟩

theorem balanced_core_aux_mem_iff (s : Set E) (x : E) : x ∈ BalancedCoreAux 𝕜 s ↔ ∀ r : 𝕜 hr : 1 ≤ ∥r∥, x ∈ r • s := by
  rw [BalancedCoreAux, Set.mem_Inter₂]

theorem balanced_hull_mem_iff (s : Set E) (x : E) : x ∈ BalancedHull 𝕜 s ↔ ∃ (r : 𝕜)(hr : ∥r∥ ≤ 1), x ∈ r • s := by
  rw [BalancedHull, Set.mem_Union₂]

/-- The balanced core of `s` is minimal in the sense that it is contained in any balanced superset
`t` of `s`. -/
theorem Balanced.hull_subset_of_subset {s t : Set E} (ht : Balanced 𝕜 t) (h : s ⊆ t) : BalancedHull 𝕜 s ⊆ t := by
  intro x hx
  rcases(balanced_hull_mem_iff _ _).mp hx with ⟨r, hr, hx⟩
  rcases mem_smul_set.mp hx with ⟨y, hy, hx⟩
  rw [← hx]
  exact balanced_mem ht (h hy) hr

end HasScalar

section AddCommMonoidₓ

variable [AddCommMonoidₓ E] [Module 𝕜 E]

theorem balanced_core_nonempty_iff {s : Set E} : (BalancedCore 𝕜 s).Nonempty ↔ (0 : E) ∈ s := by
  constructor <;> intro h
  · cases' h with x hx
    have h' : Balanced 𝕜 (BalancedCore 𝕜 s) := balanced_core_balanced s
    have h'' := h' 0 (LE.le.trans norm_zero.le zero_le_one)
    refine' mem_of_subset_of_mem (subset.trans h'' (balanced_core_subset s)) _
    exact mem_smul_set.mpr ⟨x, hx, zero_smul _ _⟩
    
  refine' nonempty_of_mem (mem_of_subset_of_mem _ (mem_singleton 0))
  exact Balanced.subset_core_of_subset zero_singleton_balanced (singleton_subset_iff.mpr h)

theorem balanced_core_zero_mem {s : Set E} (hs : (0 : E) ∈ s) : (0 : E) ∈ BalancedCore 𝕜 s :=
  balanced_core_mem_iff.mpr ⟨{0}, zero_singleton_balanced, singleton_subset_iff.mpr hs, mem_singleton 0⟩

variable (𝕜)

theorem subset_balanced_hull [NormOneClass 𝕜] {s : Set E} : s ⊆ BalancedHull 𝕜 s := fun _ hx =>
  (balanced_hull_mem_iff _ _).mpr ⟨1, norm_one.le, mem_smul_set.mp ⟨_, hx, one_smul _ _⟩⟩

variable {𝕜}

theorem BalancedHull.balanced (s : Set E) : Balanced 𝕜 (BalancedHull 𝕜 s) := by
  intro a ha
  simp_rw [BalancedHull, smul_set_Union₂, subset_def, mem_Union₂]
  intro x hx
  rcases hx with ⟨r, hr, hx⟩
  use a • r
  constructor
  · rw [smul_eq_mul]
    refine' LE.le.trans (SemiNormedRing.norm_mul _ _) _
    refine' mul_le_one ha (norm_nonneg r) hr
    
  rw [smul_assoc]
  exact hx

end AddCommMonoidₓ

end SemiNormedRing

section NormedField

variable [NormedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E]

@[simp]
theorem balanced_core_aux_empty : BalancedCoreAux 𝕜 (∅ : Set E) = ∅ := by
  rw [BalancedCoreAux, Set.Inter₂_eq_empty_iff]
  intro _
  simp only [smul_set_empty, mem_empty_eq, not_false_iff, exists_prop, and_trueₓ]
  exact ⟨1, norm_one.ge⟩

theorem balanced_core_aux_subset (s : Set E) : BalancedCoreAux 𝕜 s ⊆ s := by
  rw [subset_def]
  intro x hx
  rw [balanced_core_aux_mem_iff] at hx
  have h := hx 1 norm_one.ge
  rw [one_smul] at h
  exact h

theorem balanced_core_aux_balanced {s : Set E} (h0 : (0 : E) ∈ BalancedCoreAux 𝕜 s) :
    Balanced 𝕜 (BalancedCoreAux 𝕜 s) := by
  intro a ha x hx
  rcases mem_smul_set.mp hx with ⟨y, hy, hx⟩
  by_cases' a = 0
  · simp [h] at hx
    rw [← hx]
    exact h0
    
  rw [← hx, balanced_core_aux_mem_iff]
  rw [balanced_core_aux_mem_iff] at hy
  intro r hr
  have h'' : 1 ≤ ∥a⁻¹ • r∥ := by
    rw [smul_eq_mul]
    simp only [norm_mul, norm_inv]
    exact one_le_mul_of_one_le_of_one_le (one_le_inv (norm_pos_iff.mpr h) ha) hr
  have h' := hy (a⁻¹ • r) h''
  rw [smul_assoc] at h'
  exact (mem_inv_smul_set_iff₀ h _ _).mp h'

theorem balanced_core_aux_maximal {s t : Set E} (h : t ⊆ s) (ht : Balanced 𝕜 t) : t ⊆ BalancedCoreAux 𝕜 s := by
  intro x hx
  rw [balanced_core_aux_mem_iff]
  intro r hr
  rw [mem_smul_set_iff_inv_smul_mem₀ (norm_pos_iff.mp (lt_of_lt_of_leₓ zero_lt_one hr))]
  refine' h (balanced_mem ht hx _)
  rw [norm_inv]
  exact inv_le_one hr

theorem balanced_core_subset_balanced_core_aux {s : Set E} : BalancedCore 𝕜 s ⊆ BalancedCoreAux 𝕜 s :=
  balanced_core_aux_maximal (balanced_core_subset s) (balanced_core_balanced s)

theorem balanced_core_eq_Inter {s : Set E} (hs : (0 : E) ∈ s) : BalancedCore 𝕜 s = ⋂ (r : 𝕜) (hr : 1 ≤ ∥r∥), r • s := by
  rw [← BalancedCoreAux]
  refine' subset_antisymm balanced_core_subset_balanced_core_aux _
  refine' Balanced.subset_core_of_subset (balanced_core_aux_balanced _) (balanced_core_aux_subset s)
  refine' mem_of_subset_of_mem balanced_core_subset_balanced_core_aux (balanced_core_zero_mem hs)

theorem subset_balanced_core {U V : Set E} (hV' : (0 : E) ∈ V) (hUV : ∀ a : 𝕜 ha : ∥a∥ ≤ 1, a • U ⊆ V) :
    U ⊆ BalancedCore 𝕜 V := by
  rw [balanced_core_eq_Inter hV']
  refine' Set.subset_Inter₂ fun a ha => _
  rw [← one_smul 𝕜 U, ← mul_inv_cancel (norm_pos_iff.mp (lt_of_lt_of_leₓ zero_lt_one ha)), ← smul_eq_mul, smul_assoc]
  refine' Set.smul_set_mono (hUV a⁻¹ _)
  rw [norm_inv]
  exact inv_le_one ha

end NormedField

end BalancedHull

/-! ### Topological properties -/


section Topology

variable [NondiscreteNormedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] [TopologicalSpace E] [HasContinuousSmul 𝕜 E]

theorem balanced_core_is_closed {U : Set E} (hU : IsClosed U) : IsClosed (BalancedCore 𝕜 U) := by
  by_cases' h : (0 : E) ∈ U
  · rw [balanced_core_eq_Inter h]
    refine' is_closed_Inter fun a => _
    refine' is_closed_Inter fun ha => _
    have ha' := lt_of_lt_of_leₓ zero_lt_one ha
    rw [norm_pos_iff] at ha'
    refine' is_closed_map_smul_of_ne_zero ha' U hU
    
  convert is_closed_empty
  contrapose! h
  exact balanced_core_nonempty_iff.mp (set.ne_empty_iff_nonempty.mp h)

theorem balanced_core_mem_nhds_zero {U : Set E} (hU : U ∈ 𝓝 (0 : E)) : BalancedCore 𝕜 U ∈ 𝓝 (0 : E) := by
  -- Getting neighborhoods of the origin for `0 : 𝕜` and `0 : E`
  have h : Filter.Tendsto (fun x : 𝕜 × E => x.fst • x.snd) (𝓝 (0, 0)) (𝓝 ((0 : 𝕜) • (0 : E))) :=
    continuous_iff_continuous_at.mp HasContinuousSmul.continuous_smul (0, 0)
  rw [smul_zero] at h
  have h' := Filter.HasBasis.prod (@Metric.nhds_basis_ball 𝕜 _ 0) (Filter.basis_sets (𝓝 (0 : E)))
  simp_rw [← nhds_prod_eq, id.def]  at h'
  have h'' := Filter.Tendsto.basis_left h h' U hU
  rcases h'' with ⟨x, hx, h''⟩
  cases' NormedField.exists_norm_lt 𝕜 hx.left with y hy
  have hy' : y ≠ 0 := norm_pos_iff.mp hy.1
  let W := y • x.snd
  rw [← Filter.exists_mem_subset_iff]
  refine' ⟨W, (set_smul_mem_nhds_zero_iff hy').mpr hx.2, _⟩
  -- It remains to show that `W ⊆ balanced_core 𝕜 U`
  refine' subset_balanced_core (mem_of_mem_nhds hU) fun a ha => _
  refine' Set.Subset.trans (fun z hz => _) (set.maps_to'.mp h'')
  rw [Set.image_prod, Set.image2_smul]
  rw [Set.mem_smul_set] at hz
  rcases hz with ⟨z', hz', hz⟩
  rw [← hz, Set.mem_smul]
  refine' ⟨a • y, y⁻¹ • z', _, _, _⟩
  · rw [Algebra.id.smul_eq_mul, mem_ball_zero_iff, norm_mul, ← one_mulₓ x.fst]
    exact mul_lt_mul' ha hy.2 hy.1.le zero_lt_one
    
  · convert Set.smul_mem_smul_set hz'
    rw [← smul_assoc y⁻¹ y x.snd, smul_eq_mul, inv_mul_cancel hy', one_smul]
    
  rw [smul_assoc, ← smul_assoc y y⁻¹ z', smul_eq_mul, mul_inv_cancel hy', one_smul]

variable (𝕜 E)

theorem nhds_basis_closed_balanced [RegularSpace E] :
    (𝓝 (0 : E)).HasBasis (fun s : Set E => s ∈ 𝓝 (0 : E) ∧ IsClosed s ∧ Balanced 𝕜 s) id := by
  refine' (closed_nhds_basis 0).to_has_basis (fun s hs => _) fun s hs => ⟨s, ⟨hs.1, hs.2.1⟩, rfl.subset⟩
  refine' ⟨BalancedCore 𝕜 s, ⟨balanced_core_mem_nhds_zero hs.1, _⟩, balanced_core_subset s⟩
  refine' ⟨balanced_core_is_closed hs.2, balanced_core_balanced s⟩

end Topology

