/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
import Mathbin.LinearAlgebra.Ray
import Mathbin.Analysis.NormedSpace.Basic

/-!
# Rays in a real normed vector space

In this file we prove some lemmas about the `same_ray` predicate in case of a real normed space. In
this case, for two vectors `x y` in the same ray, the norm of their sum is equal to the sum of their
norms and `∥y∥ • x = ∥x∥ • y`.
-/


open Real

variable {E : Type _} [SemiNormedGroup E] [NormedSpace ℝ E] {F : Type _} [NormedGroup F] [NormedSpace ℝ F]

namespace SameRay

variable {x y : E}

/-- If `x` and `y` are on the same ray, then the triangle inequality becomes the equality: the norm
of `x + y` is the sum of the norms of `x` and `y`. The converse is true for a strictly convex
space. -/
theorem norm_add (h : SameRay ℝ x y) : ∥x + y∥ = ∥x∥ + ∥y∥ := by
  rcases h.exists_eq_smul with ⟨u, a, b, ha, hb, -, rfl, rfl⟩
  rw [← add_smul, norm_smul_of_nonneg (add_nonneg ha hb), norm_smul_of_nonneg ha, norm_smul_of_nonneg hb, add_mulₓ]

theorem norm_sub (h : SameRay ℝ x y) : ∥x - y∥ = abs (∥x∥ - ∥y∥) := by
  rcases h.exists_eq_smul with ⟨u, a, b, ha, hb, -, rfl, rfl⟩
  wlog (discharger := tactic.skip) hab : b ≤ a := le_totalₓ b a using a b, b a
  · rw [← sub_nonneg] at hab
    rw [← sub_smul, norm_smul_of_nonneg hab, norm_smul_of_nonneg ha, norm_smul_of_nonneg hb, ← sub_mul,
      abs_of_nonneg (mul_nonneg hab (norm_nonneg _))]
    
  · intro ha hb hab
    rw [norm_sub_rev, this hb ha hab.symm, abs_sub_comm]
    

theorem norm_smul_eq (h : SameRay ℝ x y) : ∥x∥ • y = ∥y∥ • x := by
  rcases h.exists_eq_smul with ⟨u, a, b, ha, hb, -, rfl, rfl⟩
  simp only [norm_smul_of_nonneg, *, mul_smul, smul_comm ∥u∥]
  apply smul_comm

end SameRay

variable {x y : F}

theorem norm_inj_on_ray_left (hx : x ≠ 0) : { y | SameRay ℝ x y }.InjOn norm := by
  rintro y hy z hz h
  rcases hy.exists_nonneg_left hx with ⟨r, hr, rfl⟩
  rcases hz.exists_nonneg_left hx with ⟨s, hs, rfl⟩
  rw [norm_smul, norm_smul, mul_left_inj' (norm_ne_zero_iff.2 hx), norm_of_nonneg hr, norm_of_nonneg hs] at h
  rw [h]

theorem norm_inj_on_ray_right (hy : y ≠ 0) : { x | SameRay ℝ x y }.InjOn norm := by
  simpa only [same_ray_comm] using norm_inj_on_ray_left hy

theorem same_ray_iff_norm_smul_eq : SameRay ℝ x y ↔ ∥x∥ • y = ∥y∥ • x :=
  ⟨SameRay.norm_smul_eq, fun h =>
    or_iff_not_imp_left.2 fun hx =>
      or_iff_not_imp_left.2 fun hy => ⟨∥y∥, ∥x∥, norm_pos_iff.2 hy, norm_pos_iff.2 hx, h.symm⟩⟩

/-- Two nonzero vectors `x y` in a real normed space are on the same ray if and only if the unit
vectors `∥x∥⁻¹ • x` and `∥y∥⁻¹ • y` are equal. -/
theorem same_ray_iff_inv_norm_smul_eq_of_ne (hx : x ≠ 0) (hy : y ≠ 0) : SameRay ℝ x y ↔ ∥x∥⁻¹ • x = ∥y∥⁻¹ • y := by
  rw [inv_smul_eq_iff₀, smul_comm, eq_comm, inv_smul_eq_iff₀, same_ray_iff_norm_smul_eq] <;> rwa [norm_ne_zero_iff]

alias same_ray_iff_inv_norm_smul_eq_of_ne ↔ SameRay.inv_norm_smul_eq _

/-- Two vectors `x y` in a real normed space are on the ray if and only if one of them is zero or
the unit vectors `∥x∥⁻¹ • x` and `∥y∥⁻¹ • y` are equal. -/
theorem same_ray_iff_inv_norm_smul_eq : SameRay ℝ x y ↔ x = 0 ∨ y = 0 ∨ ∥x∥⁻¹ • x = ∥y∥⁻¹ • y := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp [SameRay.zero_left]
    
  rcases eq_or_ne y 0 with (rfl | hy)
  · simp [SameRay.zero_right]
    
  simp only [same_ray_iff_inv_norm_smul_eq_of_ne hx hy, *, false_orₓ]

theorem same_ray_iff_of_norm_eq (h : ∥x∥ = ∥y∥) : SameRay ℝ x y ↔ x = y := by
  obtain rfl | hy := eq_or_ne y 0
  · rw [norm_zero, norm_eq_zero] at h
    exact iff_of_true (SameRay.zero_right _) h
    
  · exact ⟨fun hxy => norm_inj_on_ray_right hy hxy SameRay.rfl h, fun hxy => hxy ▸ SameRay.rfl⟩
    

theorem not_same_ray_iff_of_norm_eq (h : ∥x∥ = ∥y∥) : ¬SameRay ℝ x y ↔ x ≠ y :=
  (same_ray_iff_of_norm_eq h).Not

