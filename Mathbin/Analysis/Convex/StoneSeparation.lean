/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Analysis.Convex.Join

#align_import analysis.convex.stone_separation from "leanprover-community/mathlib"@"f2b757fc5c341d88741b9c4630b1e8ba973c5726"

/-!
# Stone's separation theorem

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file prove Stone's separation theorem. This tells us that any two disjoint convex sets can be
separated by a convex set whose complement is also convex.

In locally convex real topological vector spaces, the Hahn-Banach separation theorems provide
stronger statements: one may find a separating hyperplane, instead of merely a convex set whose
complement is convex.
-/


open Set

open scoped BigOperators

variable {𝕜 E ι : Type _} [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E] {s t : Set E}

#print not_disjoint_segment_convexHull_triple /-
/-- In a tetrahedron with vertices `x`, `y`, `p`, `q`, any segment `[u, v]` joining the opposite
edges `[x, p]` and `[y, q]` passes through any triangle of vertices `p`, `q`, `z` where
`z ∈ [x, y]`. -/
theorem not_disjoint_segment_convexHull_triple {p q u v x y z : E} (hz : z ∈ segment 𝕜 x y)
    (hu : u ∈ segment 𝕜 x p) (hv : v ∈ segment 𝕜 y q) :
    ¬Disjoint (segment 𝕜 u v) (convexHull 𝕜 {p, q, z}) :=
  by
  rw [not_disjoint_iff]
  obtain ⟨az, bz, haz, hbz, habz, rfl⟩ := hz
  obtain rfl | haz' := haz.eq_or_lt
  · rw [zero_add] at habz 
    rw [zero_smul, zero_add, habz, one_smul]
    refine' ⟨v, right_mem_segment _ _ _, segment_subset_convexHull _ _ hv⟩ <;> simp
  obtain ⟨av, bv, hav, hbv, habv, rfl⟩ := hv
  obtain rfl | hav' := hav.eq_or_lt
  · rw [zero_add] at habv 
    rw [zero_smul, zero_add, habv, one_smul]
    exact ⟨q, right_mem_segment _ _ _, subset_convexHull _ _ <| by simp⟩
  obtain ⟨au, bu, hau, hbu, habu, rfl⟩ := hu
  have hab : 0 < az * av + bz * au :=
    add_pos_of_pos_of_nonneg (mul_pos haz' hav') (mul_nonneg hbz hau)
  refine'
    ⟨(az * av / (az * av + bz * au)) • (au • x + bu • p) +
        (bz * au / (az * av + bz * au)) • (av • y + bv • q),
      ⟨_, _, _, _, _, rfl⟩, _⟩
  · exact div_nonneg (mul_nonneg haz hav) hab.le
  · exact div_nonneg (mul_nonneg hbz hau) hab.le
  · rw [← add_div, div_self hab.ne']
  rw [smul_add, smul_add, add_add_add_comm, add_comm, ← mul_smul, ← mul_smul]
  classical
#align not_disjoint_segment_convex_hull_triple not_disjoint_segment_convexHull_triple
-/

#print exists_convex_convex_compl_subset /-
/-- **Stone's Separation Theorem** -/
theorem exists_convex_convex_compl_subset (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) (hst : Disjoint s t) :
    ∃ C : Set E, Convex 𝕜 C ∧ Convex 𝕜 (Cᶜ) ∧ s ⊆ C ∧ t ⊆ Cᶜ :=
  by
  let S : Set (Set E) := {C | Convex 𝕜 C ∧ Disjoint C t}
  obtain ⟨C, hC, hsC, hCmax⟩ :=
    zorn_subset_nonempty S
      (fun c hcS hc ⟨t, ht⟩ =>
        ⟨⋃₀ c,
          ⟨hc.directed_on.convex_sUnion fun s hs => (hcS hs).1,
            disjoint_sUnion_left.2 fun c hc => (hcS hc).2⟩,
          fun s => subset_sUnion_of_mem⟩)
      s ⟨hs, hst⟩
  refine'
    ⟨C, hC.1, convex_iff_segment_subset.2 fun x hx y hy z hz hzC => _, hsC, hC.2.subset_compl_left⟩
  suffices h : ∀ c ∈ Cᶜ, ∃ a ∈ C, (segment 𝕜 c a ∩ t).Nonempty
  · obtain ⟨p, hp, u, hu, hut⟩ := h x hx
    obtain ⟨q, hq, v, hv, hvt⟩ := h y hy
    refine'
      not_disjoint_segment_convexHull_triple hz hu hv
        (hC.2.symm.mono (ht.segment_subset hut hvt) <| convexHull_min _ hC.1)
    simp [insert_subset, hp, hq, singleton_subset_iff.2 hzC]
  rintro c hc
  by_contra! h
  suffices h : Disjoint (convexHull 𝕜 (insert c C)) t
  · rw [←
      hCmax _ ⟨convex_convexHull _ _, h⟩ ((subset_insert _ _).trans <| subset_convexHull _ _)] at hc 
    exact hc (subset_convexHull _ _ <| mem_insert _ _)
  rw [convexHull_insert ⟨z, hzC⟩, convexJoin_singleton_left]
  refine' disjoint_Union₂_left.2 fun a ha => disjoint_iff_inf_le.mpr fun b hb => h a _ ⟨b, hb⟩
  rwa [← hC.1.convexHull_eq]
#align exists_convex_convex_compl_subset exists_convex_convex_compl_subset
-/

