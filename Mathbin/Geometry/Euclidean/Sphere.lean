/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales, Benjamin Davidson

! This file was ported from Lean 3 source module geometry.euclidean.sphere
! leanprover-community/mathlib commit 40acfb6aa7516ffe6f91136691df012a64683390
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Geometry.Euclidean.Basic
import Mathbin.Geometry.Euclidean.Triangle

/-!
# Spheres

This file proves basic geometrical results about distances and angles
in spheres in real inner product spaces and Euclidean affine spaces.

## Main theorems

* `mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi`: Intersecting Chords Theorem (Freek No. 55).
* `mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero`: Intersecting Secants Theorem.
* `mul_dist_add_mul_dist_eq_mul_dist_of_cospherical`: Ptolemy’s Theorem (Freek No. 95).

TODO: The current statement of Ptolemy’s theorem works around the lack of a "cyclic polygon" concept
in mathlib, which is what the theorem statement would naturally use (or two such concepts, since
both a strict version, where all vertices must be distinct, and a weak version, where consecutive
vertices may be equal, would be useful; Ptolemy's theorem should then use the weak one).

An API needs to be built around that concept, which would include:
- strict cyclic implies weak cyclic,
- weak cyclic and consecutive points distinct implies strict cyclic,
- weak/strict cyclic implies weak/strict cyclic for any subsequence,
- any three points on a sphere are weakly or strictly cyclic according to whether they are distinct,
- any number of points on a sphere intersected with a two-dimensional affine subspace are cyclic in
  some order,
- a list of points is cyclic if and only if its reversal is,
- a list of points is cyclic if and only if any cyclic permutation is, while other permutations
  are not when the points are distinct,
- a point P where the diagonals of a cyclic polygon cross exists (and is unique) with weak/strict
  betweenness depending on weak/strict cyclicity,
- four points on a sphere with such a point P are cyclic in the appropriate order,
and so on.
-/


open Real

open EuclideanGeometry RealInnerProductSpace Real

variable {V : Type _} [InnerProductSpace ℝ V]

namespace InnerProductGeometry

/-!
### Geometrical results on spheres in real inner product spaces

This section develops some results on spheres in real inner product spaces,
which are used to deduce corresponding results for Euclidean affine spaces.
-/


theorem mul_norm_eq_abs_sub_sq_norm {x y z : V} (h₁ : ∃ k : ℝ, k ≠ 1 ∧ x + y = k • (x - y))
    (h₂ : ‖z - y‖ = ‖z + y‖) : ‖x - y‖ * ‖x + y‖ = |‖z + y‖ ^ 2 - ‖z - x‖ ^ 2| :=
  by
  obtain ⟨k, hk_ne_one, hk⟩ := h₁
  let r := (k - 1)⁻¹ * (k + 1)
  have hxy : x = r • y :=
    by
    rw [← smul_smul, eq_inv_smul_iff₀ (sub_ne_zero.mpr hk_ne_one), ← sub_eq_zero]
    calc
      (k - 1) • x - (k + 1) • y = k • x - x - (k • y + y) := by
        simp_rw [sub_smul, add_smul, one_smul]
      _ = k • x - k • y - (x + y) := by simp_rw [← sub_sub, sub_right_comm]
      _ = k • (x - y) - (x + y) := by rw [← smul_sub k x y]
      _ = 0 := sub_eq_zero.mpr hk.symm
      
  have hzy : ⟪z, y⟫ = 0 := by
    rwa [inner_eq_zero_iff_angle_eq_pi_div_two, ← norm_add_eq_norm_sub_iff_angle_eq_pi_div_two,
      eq_comm]
  have hzx : ⟪z, x⟫ = 0 := by rw [hxy, inner_smul_right, hzy, mul_zero]
  calc
    ‖x - y‖ * ‖x + y‖ = ‖(r - 1) • y‖ * ‖(r + 1) • y‖ := by simp [sub_smul, add_smul, hxy]
    _ = ‖r - 1‖ * ‖y‖ * (‖r + 1‖ * ‖y‖) := by simp_rw [norm_smul]
    _ = ‖r - 1‖ * ‖r + 1‖ * ‖y‖ ^ 2 := by ring
    _ = |(r - 1) * (r + 1) * ‖y‖ ^ 2| := by simp [abs_mul]
    _ = |r ^ 2 * ‖y‖ ^ 2 - ‖y‖ ^ 2| := by ring_nf
    _ = |‖x‖ ^ 2 - ‖y‖ ^ 2| := by simp [hxy, norm_smul, mul_pow, sq_abs]
    _ = |‖z + y‖ ^ 2 - ‖z - x‖ ^ 2| := by
      simp [norm_add_sq_real, norm_sub_sq_real, hzy, hzx, abs_sub_comm]
    
#align
  inner_product_geometry.mul_norm_eq_abs_sub_sq_norm InnerProductGeometry.mul_norm_eq_abs_sub_sq_norm

end InnerProductGeometry

namespace EuclideanGeometry

/-!
### Geometrical results on spheres in Euclidean affine spaces

This section develops some results on spheres in Euclidean affine spaces.
-/


open InnerProductGeometry

variable {P : Type _} [MetricSpace P] [NormedAddTorsor V P]

include V

/-- If `P` is a point on the line `AB` and `Q` is equidistant from `A` and `B`, then
`AP * BP = abs (BQ ^ 2 - PQ ^ 2)`. -/
theorem mul_dist_eq_abs_sub_sq_dist {a b p q : P} (hp : ∃ k : ℝ, k ≠ 1 ∧ b -ᵥ p = k • (a -ᵥ p))
    (hq : dist a q = dist b q) : dist a p * dist b p = |dist b q ^ 2 - dist p q ^ 2| :=
  by
  let m : P := midpoint ℝ a b
  obtain ⟨v, h1, h2, h3⟩ := vsub_sub_vsub_cancel_left, v a p m, v p q m, v a q m
  have h : ∀ r, b -ᵥ r = m -ᵥ r + (m -ᵥ a) := fun r => by
    rw [midpoint_vsub_left, ← right_vsub_midpoint, add_comm, vsub_add_vsub_cancel]
  iterate 4 rw [dist_eq_norm_vsub V]
  rw [← h1, ← h2, h, h]
  rw [← h1, h] at hp
  rw [dist_eq_norm_vsub V a q, dist_eq_norm_vsub V b q, ← h3, h] at hq
  exact mul_norm_eq_abs_sub_sq_norm hp hq
#align euclidean_geometry.mul_dist_eq_abs_sub_sq_dist EuclideanGeometry.mul_dist_eq_abs_sub_sq_dist

/-- If `A`, `B`, `C`, `D` are cospherical and `P` is on both lines `AB` and `CD`, then
`AP * BP = CP * DP`. -/
theorem mul_dist_eq_mul_dist_of_cospherical {a b c d p : P} (h : Cospherical ({a, b, c, d} : Set P))
    (hapb : ∃ k₁ : ℝ, k₁ ≠ 1 ∧ b -ᵥ p = k₁ • (a -ᵥ p))
    (hcpd : ∃ k₂ : ℝ, k₂ ≠ 1 ∧ d -ᵥ p = k₂ • (c -ᵥ p)) :
    dist a p * dist b p = dist c p * dist d p :=
  by
  obtain ⟨q, r, h'⟩ := (cospherical_def {a, b, c, d}).mp h
  obtain ⟨ha, hb, hc, hd⟩ := h' a _, h' b _, h' c _, h' d _
  · rw [← hd] at hc
    rw [← hb] at ha
    rw [mul_dist_eq_abs_sub_sq_dist hapb ha, hb, mul_dist_eq_abs_sub_sq_dist hcpd hc, hd]
  all_goals simp
#align
  euclidean_geometry.mul_dist_eq_mul_dist_of_cospherical EuclideanGeometry.mul_dist_eq_mul_dist_of_cospherical

/-- **Intersecting Chords Theorem**. -/
theorem mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi {a b c d p : P}
    (h : Cospherical ({a, b, c, d} : Set P)) (hapb : ∠ a p b = π) (hcpd : ∠ c p d = π) :
    dist a p * dist b p = dist c p * dist d p :=
  by
  obtain ⟨-, k₁, _, hab⟩ := angle_eq_pi_iff.mp hapb
  obtain ⟨-, k₂, _, hcd⟩ := angle_eq_pi_iff.mp hcpd
  exact mul_dist_eq_mul_dist_of_cospherical h ⟨k₁, by linarith, hab⟩ ⟨k₂, by linarith, hcd⟩
#align
  euclidean_geometry.mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi EuclideanGeometry.mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi

/-- **Intersecting Secants Theorem**. -/
theorem mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero {a b c d p : P}
    (h : Cospherical ({a, b, c, d} : Set P)) (hab : a ≠ b) (hcd : c ≠ d) (hapb : ∠ a p b = 0)
    (hcpd : ∠ c p d = 0) : dist a p * dist b p = dist c p * dist d p :=
  by
  obtain ⟨-, k₁, -, hab₁⟩ := angle_eq_zero_iff.mp hapb
  obtain ⟨-, k₂, -, hcd₁⟩ := angle_eq_zero_iff.mp hcpd
  refine' mul_dist_eq_mul_dist_of_cospherical h ⟨k₁, _, hab₁⟩ ⟨k₂, _, hcd₁⟩ <;> by_contra hnot <;>
    simp_all only [not_not, one_smul]
  exacts[hab (vsub_left_cancel hab₁).symm, hcd (vsub_left_cancel hcd₁).symm]
#align
  euclidean_geometry.mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero EuclideanGeometry.mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero

/-- **Ptolemy’s Theorem**. -/
theorem mul_dist_add_mul_dist_eq_mul_dist_of_cospherical {a b c d p : P}
    (h : Cospherical ({a, b, c, d} : Set P)) (hapc : ∠ a p c = π) (hbpd : ∠ b p d = π) :
    dist a b * dist c d + dist b c * dist d a = dist a c * dist b d :=
  by
  have h' : cospherical ({a, c, b, d} : Set P) := by rwa [Set.insert_comm c b {d}]
  have hmul := mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi h' hapc hbpd
  have hbp := left_dist_ne_zero_of_angle_eq_pi hbpd
  have h₁ : dist c d = dist c p / dist b p * dist a b :=
    by
    rw [dist_mul_of_eq_angle_of_dist_mul b p a c p d, dist_comm a b]
    · rw [angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi hbpd hapc, angle_comm]
    all_goals field_simp [mul_comm, hmul]
  have h₂ : dist d a = dist a p / dist b p * dist b c :=
    by
    rw [dist_mul_of_eq_angle_of_dist_mul c p b d p a, dist_comm c b]
    · rwa [angle_comm, angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi]
      rwa [angle_comm]
    all_goals field_simp [mul_comm, hmul]
  have h₃ : dist d p = dist a p * dist c p / dist b p := by field_simp [mul_comm, hmul]
  have h₄ : ∀ x y : ℝ, x * (y * x) = x * x * y := fun x y => by rw [mul_left_comm, mul_comm]
  field_simp [h₁, h₂, dist_eq_add_dist_of_angle_eq_pi hbpd, h₃, hbp, dist_comm a b, h₄, ← sq,
    dist_sq_mul_dist_add_dist_sq_mul_dist b, hapc]
#align
  euclidean_geometry.mul_dist_add_mul_dist_eq_mul_dist_of_cospherical EuclideanGeometry.mul_dist_add_mul_dist_eq_mul_dist_of_cospherical

end EuclideanGeometry

