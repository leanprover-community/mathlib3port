/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Manuel Candales

! This file was ported from Lean 3 source module geometry.euclidean.basic
! leanprover-community/mathlib commit 706d88f2b8fdfeb0b22796433d7a6c1a010af9f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.InnerProductSpace.Projection
import Mathbin.Algebra.QuadraticDiscriminant

/-!
# Euclidean spaces

This file makes some definitions and proves very basic geometrical
results about real inner product spaces and Euclidean affine spaces.
Results about real inner product spaces that involve the norm and
inner product but not angles generally go in
`analysis.normed_space.inner_product`.  Results with longer
proofs or more geometrical content generally go in separate files.

## Main definitions

* `euclidean_geometry.orthogonal_projection` is the orthogonal
  projection of a point onto an affine subspace.

* `euclidean_geometry.reflection` is the reflection of a point in an
  affine subspace.

## Implementation notes

To declare `P` as the type of points in a Euclidean affine space with
`V` as the type of vectors, use `[inner_product_space ℝ V] [metric_space P]
[normed_add_torsor V P]`.  This works better with `out_param` to make
`V` implicit in most cases than having a separate type alias for
Euclidean affine spaces.

Rather than requiring Euclidean affine spaces to be finite-dimensional
(as in the definition on Wikipedia), this is specified only for those
theorems that need it.

## References

* https://en.wikipedia.org/wiki/Euclidean_space

-/


noncomputable section

open BigOperators

open Classical

open RealInnerProductSpace

namespace EuclideanGeometry

/-!
### Geometrical results on Euclidean affine spaces

This section develops some geometrical definitions and results on
Euclidean affine spaces.
-/


variable {V : Type _} {P : Type _} [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

include V

/-- The midpoint of the segment AB is the same distance from A as it is from B. -/
theorem dist_left_midpoint_eq_dist_right_midpoint (p1 p2 : P) :
    dist p1 (midpoint ℝ p1 p2) = dist p2 (midpoint ℝ p1 p2) := by
  rw [dist_left_midpoint p1 p2, dist_right_midpoint p1 p2]
#align
  euclidean_geometry.dist_left_midpoint_eq_dist_right_midpoint EuclideanGeometry.dist_left_midpoint_eq_dist_right_midpoint

/-- The inner product of two vectors given with `weighted_vsub`, in
terms of the pairwise distances. -/
theorem inner_weighted_vsub {ι₁ : Type _} {s₁ : Finset ι₁} {w₁ : ι₁ → ℝ} (p₁ : ι₁ → P)
    (h₁ : (∑ i in s₁, w₁ i) = 0) {ι₂ : Type _} {s₂ : Finset ι₂} {w₂ : ι₂ → ℝ} (p₂ : ι₂ → P)
    (h₂ : (∑ i in s₂, w₂ i) = 0) :
    ⟪s₁.weightedVsub p₁ w₁, s₂.weightedVsub p₂ w₂⟫ =
      (-∑ i₁ in s₁, ∑ i₂ in s₂, w₁ i₁ * w₂ i₂ * (dist (p₁ i₁) (p₂ i₂) * dist (p₁ i₁) (p₂ i₂))) /
        2 :=
  by
  rw [Finset.weighted_vsub_apply, Finset.weighted_vsub_apply,
    inner_sum_smul_sum_smul_of_sum_eq_zero _ h₁ _ h₂]
  simp_rw [vsub_sub_vsub_cancel_right]
  rcongr (i₁ i₂) <;> rw [dist_eq_norm_vsub V (p₁ i₁) (p₂ i₂)]
#align euclidean_geometry.inner_weighted_vsub EuclideanGeometry.inner_weighted_vsub

/-- The distance between two points given with `affine_combination`,
in terms of the pairwise distances between the points in that
combination. -/
theorem dist_affine_combination {ι : Type _} {s : Finset ι} {w₁ w₂ : ι → ℝ} (p : ι → P)
    (h₁ : (∑ i in s, w₁ i) = 1) (h₂ : (∑ i in s, w₂ i) = 1) : by
    have a₁ := s.affine_combination p w₁ <;> have a₂ := s.affine_combination p w₂ <;>
      exact
        dist a₁ a₂ * dist a₁ a₂ =
          (-∑ i₁ in s,
                ∑ i₂ in s,
                  (w₁ - w₂) i₁ * (w₁ - w₂) i₂ * (dist (p i₁) (p i₂) * dist (p i₁) (p i₂))) /
            2 :=
  by
  rw [dist_eq_norm_vsub V (s.affine_combination p w₁) (s.affine_combination p w₂), ←
    inner_self_eq_norm_mul_norm, Finset.affine_combination_vsub]
  have h : (∑ i in s, (w₁ - w₂) i) = 0 := by
    simp_rw [Pi.sub_apply, Finset.sum_sub_distrib, h₁, h₂, sub_self]
  exact inner_weighted_vsub p h p h
#align euclidean_geometry.dist_affine_combination EuclideanGeometry.dist_affine_combination

/-- Suppose that `c₁` is equidistant from `p₁` and `p₂`, and the same
applies to `c₂`.  Then the vector between `c₁` and `c₂` is orthogonal
to that between `p₁` and `p₂`.  (In two dimensions, this says that the
diagonals of a kite are orthogonal.) -/
theorem inner_vsub_vsub_of_dist_eq_of_dist_eq {c₁ c₂ p₁ p₂ : P} (hc₁ : dist p₁ c₁ = dist p₂ c₁)
    (hc₂ : dist p₁ c₂ = dist p₂ c₂) : ⟪c₂ -ᵥ c₁, p₂ -ᵥ p₁⟫ = 0 := by
  have h : ⟪c₂ -ᵥ c₁ + (c₂ -ᵥ c₁), p₂ -ᵥ p₁⟫ = 0 := by
    conv_lhs => 
      congr
      congr
      rw [← vsub_sub_vsub_cancel_right c₂ c₁ p₁]
      skip
      rw [← vsub_sub_vsub_cancel_right c₂ c₁ p₂]
    rw [sub_add_sub_comm, inner_sub_left]
    conv_lhs => 
      congr
      rw [← vsub_sub_vsub_cancel_right p₂ p₁ c₂]
      skip
      rw [← vsub_sub_vsub_cancel_right p₂ p₁ c₁]
    rw [dist_comm p₁, dist_comm p₂, dist_eq_norm_vsub V _ p₁, dist_eq_norm_vsub V _ p₂, ←
      real_inner_add_sub_eq_zero_iff] at hc₁ hc₂
    simp_rw [← neg_vsub_eq_vsub_rev c₁, ← neg_vsub_eq_vsub_rev c₂, sub_neg_eq_add, neg_add_eq_sub,
      hc₁, hc₂, sub_zero]
  simpa [inner_add_left, ← mul_two, (by norm_num : (2 : ℝ) ≠ 0)] using h
#align
  euclidean_geometry.inner_vsub_vsub_of_dist_eq_of_dist_eq EuclideanGeometry.inner_vsub_vsub_of_dist_eq_of_dist_eq

/-- The squared distance between points on a line (expressed as a
multiple of a fixed vector added to a point) and another point,
expressed as a quadratic. -/
theorem dist_smul_vadd_sq (r : ℝ) (v : V) (p₁ p₂ : P) :
    dist (r • v +ᵥ p₁) p₂ * dist (r • v +ᵥ p₁) p₂ =
      ⟪v, v⟫ * r * r + 2 * ⟪v, p₁ -ᵥ p₂⟫ * r + ⟪p₁ -ᵥ p₂, p₁ -ᵥ p₂⟫ :=
  by
  rw [dist_eq_norm_vsub V _ p₂, ← real_inner_self_eq_norm_mul_norm, vadd_vsub_assoc,
    real_inner_add_add_self, real_inner_smul_left, real_inner_smul_left, real_inner_smul_right]
  ring
#align euclidean_geometry.dist_smul_vadd_sq EuclideanGeometry.dist_smul_vadd_sq

/-- The condition for two points on a line to be equidistant from
another point. -/
theorem dist_smul_vadd_eq_dist {v : V} (p₁ p₂ : P) (hv : v ≠ 0) (r : ℝ) :
    dist (r • v +ᵥ p₁) p₂ = dist p₁ p₂ ↔ r = 0 ∨ r = -2 * ⟪v, p₁ -ᵥ p₂⟫ / ⟪v, v⟫ := by
  conv_lhs =>
    rw [← mul_self_inj_of_nonneg dist_nonneg dist_nonneg, dist_smul_vadd_sq, ← sub_eq_zero,
      add_sub_assoc, dist_eq_norm_vsub V p₁ p₂, ← real_inner_self_eq_norm_mul_norm, sub_self]
  have hvi : ⟪v, v⟫ ≠ 0 := by simpa using hv
  have hd : discrim ⟪v, v⟫ (2 * ⟪v, p₁ -ᵥ p₂⟫) 0 = 2 * ⟪v, p₁ -ᵥ p₂⟫ * (2 * ⟪v, p₁ -ᵥ p₂⟫) := by
    rw [discrim]
    ring
  rw [quadratic_eq_zero_iff hvi hd, add_left_neg, zero_div, neg_mul_eq_neg_mul, ←
    mul_sub_right_distrib, sub_eq_add_neg, ← mul_two, mul_assoc, mul_div_assoc, mul_div_mul_left,
    mul_div_assoc]
  norm_num
#align euclidean_geometry.dist_smul_vadd_eq_dist EuclideanGeometry.dist_smul_vadd_eq_dist

open AffineSubspace FiniteDimensional

/-- Distances `r₁` `r₂` of `p` from two different points `c₁` `c₂` determine at
most two points `p₁` `p₂` in a two-dimensional subspace containing those points
(two circles intersect in at most two points). -/
theorem eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two {s : AffineSubspace ℝ P}
    [FiniteDimensional ℝ s.direction] (hd : finrank ℝ s.direction = 2) {c₁ c₂ p₁ p₂ p : P}
    (hc₁s : c₁ ∈ s) (hc₂s : c₂ ∈ s) (hp₁s : p₁ ∈ s) (hp₂s : p₂ ∈ s) (hps : p ∈ s) {r₁ r₂ : ℝ}
    (hc : c₁ ≠ c₂) (hp : p₁ ≠ p₂) (hp₁c₁ : dist p₁ c₁ = r₁) (hp₂c₁ : dist p₂ c₁ = r₁)
    (hpc₁ : dist p c₁ = r₁) (hp₁c₂ : dist p₁ c₂ = r₂) (hp₂c₂ : dist p₂ c₂ = r₂)
    (hpc₂ : dist p c₂ = r₂) : p = p₁ ∨ p = p₂ := by
  have ho : ⟪c₂ -ᵥ c₁, p₂ -ᵥ p₁⟫ = 0 :=
    inner_vsub_vsub_of_dist_eq_of_dist_eq (hp₁c₁.trans hp₂c₁.symm) (hp₁c₂.trans hp₂c₂.symm)
  have hop : ⟪c₂ -ᵥ c₁, p -ᵥ p₁⟫ = 0 :=
    inner_vsub_vsub_of_dist_eq_of_dist_eq (hp₁c₁.trans hpc₁.symm) (hp₁c₂.trans hpc₂.symm)
  let b : Fin 2 → V := ![c₂ -ᵥ c₁, p₂ -ᵥ p₁]
  have hb : LinearIndependent ℝ b := by
    refine' linear_independent_of_ne_zero_of_inner_eq_zero _ _
    · intro i
      fin_cases i <;> simp [b, hc.symm, hp.symm]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> try exact False.elim (hij rfl)
      · exact ho
      · rw [real_inner_comm]
        exact ho
  have hbs : Submodule.span ℝ (Set.range b) = s.direction := by
    refine' eq_of_le_of_finrank_eq _ _
    · rw [Submodule.span_le, Set.range_subset_iff]
      intro i
      fin_cases i
      · exact vsub_mem_direction hc₂s hc₁s
      · exact vsub_mem_direction hp₂s hp₁s
    · rw [finrank_span_eq_card hb, Fintype.card_fin, hd]
  have hv : ∀ v ∈ s.direction, ∃ t₁ t₂ : ℝ, v = t₁ • (c₂ -ᵥ c₁) + t₂ • (p₂ -ᵥ p₁) := by
    intro v hv
    have hr : Set.range b = {c₂ -ᵥ c₁, p₂ -ᵥ p₁} := by
      have hu : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
      rw [← Fintype.coe_image_univ, hu]
      simp
      rfl
    rw [← hbs, hr, Submodule.mem_span_insert] at hv
    rcases hv with ⟨t₁, v', hv', hv⟩
    rw [Submodule.mem_span_singleton] at hv'
    rcases hv' with ⟨t₂, rfl⟩
    exact ⟨t₁, t₂, hv⟩
  rcases hv (p -ᵥ p₁) (vsub_mem_direction hps hp₁s) with ⟨t₁, t₂, hpt⟩
  simp only [hpt, inner_add_right, inner_smul_right, ho, mul_zero, add_zero, mul_eq_zero,
    inner_self_eq_zero, vsub_eq_zero_iff_eq, hc.symm, or_false_iff] at hop
  rw [hop, zero_smul, zero_add, ← eq_vadd_iff_vsub_eq] at hpt
  subst hpt
  have hp' : (p₂ -ᵥ p₁ : V) ≠ 0 := by simp [hp.symm]
  have hp₂ : dist ((1 : ℝ) • (p₂ -ᵥ p₁) +ᵥ p₁) c₁ = r₁ := by simp [hp₂c₁]
  rw [← hp₁c₁, dist_smul_vadd_eq_dist _ _ hp'] at hpc₁ hp₂
  simp only [one_ne_zero, false_or_iff] at hp₂
  rw [hp₂.symm] at hpc₁
  cases hpc₁ <;> simp [hpc₁]
#align
  euclidean_geometry.eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two

/-- Distances `r₁` `r₂` of `p` from two different points `c₁` `c₂` determine at
most two points `p₁` `p₂` in two-dimensional space (two circles intersect in at
most two points). -/
theorem eq_of_dist_eq_of_dist_eq_of_finrank_eq_two [FiniteDimensional ℝ V] (hd : finrank ℝ V = 2)
    {c₁ c₂ p₁ p₂ p : P} {r₁ r₂ : ℝ} (hc : c₁ ≠ c₂) (hp : p₁ ≠ p₂) (hp₁c₁ : dist p₁ c₁ = r₁)
    (hp₂c₁ : dist p₂ c₁ = r₁) (hpc₁ : dist p c₁ = r₁) (hp₁c₂ : dist p₁ c₂ = r₂)
    (hp₂c₂ : dist p₂ c₂ = r₂) (hpc₂ : dist p c₂ = r₂) : p = p₁ ∨ p = p₂ :=
  haveI hd' : finrank ℝ (⊤ : AffineSubspace ℝ P).direction = 2 := by
    rw [direction_top, finrank_top]
    exact hd
  eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two hd' (mem_top ℝ V _) (mem_top ℝ V _)
    (mem_top ℝ V _) (mem_top ℝ V _) (mem_top ℝ V _) hc hp hp₁c₁ hp₂c₁ hpc₁ hp₁c₂ hp₂c₂ hpc₂
#align
  euclidean_geometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two

variable {V}

/-- The orthogonal projection of a point onto a nonempty affine
subspace, whose direction is complete, as an unbundled function.  This
definition is only intended for use in setting up the bundled version
`orthogonal_projection` and should not be used once that is
defined. -/
def orthogonalProjectionFn (s : AffineSubspace ℝ P) [Nonempty s] [CompleteSpace s.direction]
    (p : P) : P :=
  Classical.choose <|
    inter_eq_singleton_of_nonempty_of_is_compl (nonempty_subtype.mp ‹_›)
      (mk'_nonempty p s.directionᗮ)
      (by 
        rw [direction_mk' p s.directionᗮ]
        exact Submodule.is_compl_orthogonal_of_complete_space)
#align euclidean_geometry.orthogonal_projection_fn EuclideanGeometry.orthogonalProjectionFn

/-- The intersection of the subspace and the orthogonal subspace
through the given point is the `orthogonal_projection_fn` of that
point onto the subspace.  This lemma is only intended for use in
setting up the bundled version and should not be used once that is
defined. -/
theorem inter_eq_singleton_orthogonal_projection_fn {s : AffineSubspace ℝ P} [Nonempty s]
    [CompleteSpace s.direction] (p : P) :
    (s : Set P) ∩ mk' p s.directionᗮ = {orthogonalProjectionFn s p} :=
  Classical.choose_spec <|
    inter_eq_singleton_of_nonempty_of_is_compl (nonempty_subtype.mp ‹_›)
      (mk'_nonempty p s.directionᗮ)
      (by 
        rw [direction_mk' p s.directionᗮ]
        exact Submodule.is_compl_orthogonal_of_complete_space)
#align
  euclidean_geometry.inter_eq_singleton_orthogonal_projection_fn EuclideanGeometry.inter_eq_singleton_orthogonal_projection_fn

/-- The `orthogonal_projection_fn` lies in the given subspace.  This
lemma is only intended for use in setting up the bundled version and
should not be used once that is defined. -/
theorem orthogonal_projection_fn_mem {s : AffineSubspace ℝ P} [Nonempty s]
    [CompleteSpace s.direction] (p : P) : orthogonalProjectionFn s p ∈ s := by
  rw [← mem_coe, ← Set.singleton_subset_iff, ← inter_eq_singleton_orthogonal_projection_fn]
  exact Set.inter_subset_left _ _
#align
  euclidean_geometry.orthogonal_projection_fn_mem EuclideanGeometry.orthogonal_projection_fn_mem

/-- The `orthogonal_projection_fn` lies in the orthogonal
subspace.  This lemma is only intended for use in setting up the
bundled version and should not be used once that is defined. -/
theorem orthogonal_projection_fn_mem_orthogonal {s : AffineSubspace ℝ P} [Nonempty s]
    [CompleteSpace s.direction] (p : P) : orthogonalProjectionFn s p ∈ mk' p s.directionᗮ := by
  rw [← mem_coe, ← Set.singleton_subset_iff, ← inter_eq_singleton_orthogonal_projection_fn]
  exact Set.inter_subset_right _ _
#align
  euclidean_geometry.orthogonal_projection_fn_mem_orthogonal EuclideanGeometry.orthogonal_projection_fn_mem_orthogonal

/-- Subtracting `p` from its `orthogonal_projection_fn` produces a
result in the orthogonal direction.  This lemma is only intended for
use in setting up the bundled version and should not be used once that
is defined. -/
theorem orthogonal_projection_fn_vsub_mem_direction_orthogonal {s : AffineSubspace ℝ P} [Nonempty s]
    [CompleteSpace s.direction] (p : P) : orthogonalProjectionFn s p -ᵥ p ∈ s.directionᗮ :=
  direction_mk' p s.directionᗮ ▸
    vsub_mem_direction (orthogonal_projection_fn_mem_orthogonal p) (self_mem_mk' _ _)
#align
  euclidean_geometry.orthogonal_projection_fn_vsub_mem_direction_orthogonal EuclideanGeometry.orthogonal_projection_fn_vsub_mem_direction_orthogonal

attribute [local instance] AffineSubspace.toAddTorsor

/-- The orthogonal projection of a point onto a nonempty affine
subspace, whose direction is complete. The corresponding linear map
(mapping a vector to the difference between the projections of two
points whose difference is that vector) is the `orthogonal_projection`
for real inner product spaces, onto the direction of the affine
subspace being projected onto. -/
def orthogonalProjection (s : AffineSubspace ℝ P) [Nonempty s] [CompleteSpace s.direction] :
    P →ᵃ[ℝ]
      s where 
  toFun p := ⟨orthogonalProjectionFn s p, orthogonal_projection_fn_mem p⟩
  linear := orthogonalProjection s.direction
  map_vadd' p v := by
    have hs : ((orthogonalProjection s.direction) v : V) +ᵥ orthogonalProjectionFn s p ∈ s :=
      vadd_mem_of_mem_direction (orthogonalProjection s.direction v).2
        (orthogonal_projection_fn_mem p)
    have ho :
      ((orthogonalProjection s.direction) v : V) +ᵥ orthogonalProjectionFn s p ∈
        mk' (v +ᵥ p) s.directionᗮ :=
      by
      rw [← vsub_right_mem_direction_iff_mem (self_mem_mk' _ _) _, direction_mk',
        vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_comm, add_sub_assoc]
      refine' Submodule.add_mem _ (orthogonal_projection_fn_vsub_mem_direction_orthogonal p) _
      rw [Submodule.mem_orthogonal']
      intro w hw
      rw [← neg_sub, inner_neg_left, orthogonal_projection_inner_eq_zero _ w hw, neg_zero]
    have hm :
      ((orthogonalProjection s.direction) v : V) +ᵥ orthogonalProjectionFn s p ∈
        ({orthogonalProjectionFn s (v +ᵥ p)} : Set P) :=
      by 
      rw [← inter_eq_singleton_orthogonal_projection_fn (v +ᵥ p)]
      exact Set.mem_inter hs ho
    rw [Set.mem_singleton_iff] at hm
    ext
    exact hm.symm
#align euclidean_geometry.orthogonal_projection EuclideanGeometry.orthogonalProjection

@[simp]
theorem orthogonal_projection_fn_eq {s : AffineSubspace ℝ P} [Nonempty s]
    [CompleteSpace s.direction] (p : P) : orthogonalProjectionFn s p = orthogonalProjection s p :=
  rfl
#align euclidean_geometry.orthogonal_projection_fn_eq EuclideanGeometry.orthogonal_projection_fn_eq

/-- The linear map corresponding to `orthogonal_projection`. -/
@[simp]
theorem orthogonal_projection_linear {s : AffineSubspace ℝ P} [Nonempty s]
    [CompleteSpace s.direction] :
    (orthogonalProjection s).linear = orthogonalProjection s.direction :=
  rfl
#align
  euclidean_geometry.orthogonal_projection_linear EuclideanGeometry.orthogonal_projection_linear

/-- The intersection of the subspace and the orthogonal subspace
through the given point is the `orthogonal_projection` of that point
onto the subspace. -/
theorem inter_eq_singleton_orthogonal_projection {s : AffineSubspace ℝ P} [Nonempty s]
    [CompleteSpace s.direction] (p : P) :
    (s : Set P) ∩ mk' p s.directionᗮ = {orthogonalProjection s p} := by
  rw [← orthogonal_projection_fn_eq]
  exact inter_eq_singleton_orthogonal_projection_fn p
#align
  euclidean_geometry.inter_eq_singleton_orthogonal_projection EuclideanGeometry.inter_eq_singleton_orthogonal_projection

/-- The `orthogonal_projection` lies in the given subspace. -/
theorem orthogonal_projection_mem {s : AffineSubspace ℝ P} [Nonempty s] [CompleteSpace s.direction]
    (p : P) : ↑(orthogonalProjection s p) ∈ s :=
  (orthogonalProjection s p).2
#align euclidean_geometry.orthogonal_projection_mem EuclideanGeometry.orthogonal_projection_mem

/-- The `orthogonal_projection` lies in the orthogonal subspace. -/
theorem orthogonal_projection_mem_orthogonal (s : AffineSubspace ℝ P) [Nonempty s]
    [CompleteSpace s.direction] (p : P) : ↑(orthogonalProjection s p) ∈ mk' p s.directionᗮ :=
  orthogonal_projection_fn_mem_orthogonal p
#align
  euclidean_geometry.orthogonal_projection_mem_orthogonal EuclideanGeometry.orthogonal_projection_mem_orthogonal

/-- Subtracting a point in the given subspace from the
`orthogonal_projection` produces a result in the direction of the
given subspace. -/
theorem orthogonal_projection_vsub_mem_direction {s : AffineSubspace ℝ P} [Nonempty s]
    [CompleteSpace s.direction] {p1 : P} (p2 : P) (hp1 : p1 ∈ s) :
    ↑(orthogonalProjection s p2 -ᵥ ⟨p1, hp1⟩ : s.direction) ∈ s.direction :=
  (orthogonalProjection s p2 -ᵥ ⟨p1, hp1⟩ : s.direction).2
#align
  euclidean_geometry.orthogonal_projection_vsub_mem_direction EuclideanGeometry.orthogonal_projection_vsub_mem_direction

/-- Subtracting the `orthogonal_projection` from a point in the given
subspace produces a result in the direction of the given subspace. -/
theorem vsub_orthogonal_projection_mem_direction {s : AffineSubspace ℝ P} [Nonempty s]
    [CompleteSpace s.direction] {p1 : P} (p2 : P) (hp1 : p1 ∈ s) :
    ↑((⟨p1, hp1⟩ : s) -ᵥ orthogonalProjection s p2 : s.direction) ∈ s.direction :=
  ((⟨p1, hp1⟩ : s) -ᵥ orthogonalProjection s p2 : s.direction).2
#align
  euclidean_geometry.vsub_orthogonal_projection_mem_direction EuclideanGeometry.vsub_orthogonal_projection_mem_direction

/-- A point equals its orthogonal projection if and only if it lies in
the subspace. -/
theorem orthogonal_projection_eq_self_iff {s : AffineSubspace ℝ P} [Nonempty s]
    [CompleteSpace s.direction] {p : P} : ↑(orthogonalProjection s p) = p ↔ p ∈ s := by
  constructor
  · exact fun h => h ▸ orthogonal_projection_mem p
  · intro h
    have hp : p ∈ (s : Set P) ∩ mk' p s.directionᗮ := ⟨h, self_mem_mk' p _⟩
    rw [inter_eq_singleton_orthogonal_projection p] at hp
    symm
    exact hp
#align
  euclidean_geometry.orthogonal_projection_eq_self_iff EuclideanGeometry.orthogonal_projection_eq_self_iff

@[simp]
theorem orthogonal_projection_mem_subspace_eq_self {s : AffineSubspace ℝ P} [Nonempty s]
    [CompleteSpace s.direction] (p : s) : orthogonalProjection s p = p := by
  ext
  rw [orthogonal_projection_eq_self_iff]
  exact p.2
#align
  euclidean_geometry.orthogonal_projection_mem_subspace_eq_self EuclideanGeometry.orthogonal_projection_mem_subspace_eq_self

/-- Orthogonal projection is idempotent. -/
@[simp]
theorem orthogonal_projection_orthogonal_projection (s : AffineSubspace ℝ P) [Nonempty s]
    [CompleteSpace s.direction] (p : P) :
    orthogonalProjection s (orthogonalProjection s p) = orthogonalProjection s p := by
  ext
  rw [orthogonal_projection_eq_self_iff]
  exact orthogonal_projection_mem p
#align
  euclidean_geometry.orthogonal_projection_orthogonal_projection EuclideanGeometry.orthogonal_projection_orthogonal_projection

theorem eq_orthogonal_projection_of_eq_subspace {s s' : AffineSubspace ℝ P} [Nonempty s]
    [Nonempty s'] [CompleteSpace s.direction] [CompleteSpace s'.direction] (h : s = s') (p : P) :
    (orthogonalProjection s p : P) = (orthogonalProjection s' p : P) := by
  change orthogonalProjectionFn s p = orthogonalProjectionFn s' p
  congr
  exact h
#align
  euclidean_geometry.eq_orthogonal_projection_of_eq_subspace EuclideanGeometry.eq_orthogonal_projection_of_eq_subspace

/-- The distance to a point's orthogonal projection is 0 iff it lies in the subspace. -/
theorem dist_orthogonal_projection_eq_zero_iff {s : AffineSubspace ℝ P} [Nonempty s]
    [CompleteSpace s.direction] {p : P} : dist p (orthogonalProjection s p) = 0 ↔ p ∈ s := by
  rw [dist_comm, dist_eq_zero, orthogonal_projection_eq_self_iff]
#align
  euclidean_geometry.dist_orthogonal_projection_eq_zero_iff EuclideanGeometry.dist_orthogonal_projection_eq_zero_iff

/-- The distance between a point and its orthogonal projection is
nonzero if it does not lie in the subspace. -/
theorem dist_orthogonal_projection_ne_zero_of_not_mem {s : AffineSubspace ℝ P} [Nonempty s]
    [CompleteSpace s.direction] {p : P} (hp : p ∉ s) : dist p (orthogonalProjection s p) ≠ 0 :=
  mt dist_orthogonal_projection_eq_zero_iff.mp hp
#align
  euclidean_geometry.dist_orthogonal_projection_ne_zero_of_not_mem EuclideanGeometry.dist_orthogonal_projection_ne_zero_of_not_mem

/-- Subtracting `p` from its `orthogonal_projection` produces a result
in the orthogonal direction. -/
theorem orthogonal_projection_vsub_mem_direction_orthogonal (s : AffineSubspace ℝ P) [Nonempty s]
    [CompleteSpace s.direction] (p : P) : (orthogonalProjection s p : P) -ᵥ p ∈ s.directionᗮ :=
  orthogonal_projection_fn_vsub_mem_direction_orthogonal p
#align
  euclidean_geometry.orthogonal_projection_vsub_mem_direction_orthogonal EuclideanGeometry.orthogonal_projection_vsub_mem_direction_orthogonal

/-- Subtracting the `orthogonal_projection` from `p` produces a result
in the orthogonal direction. -/
theorem vsub_orthogonal_projection_mem_direction_orthogonal (s : AffineSubspace ℝ P) [Nonempty s]
    [CompleteSpace s.direction] (p : P) : p -ᵥ orthogonalProjection s p ∈ s.directionᗮ :=
  direction_mk' p s.directionᗮ ▸
    vsub_mem_direction (self_mem_mk' _ _) (orthogonal_projection_mem_orthogonal s p)
#align
  euclidean_geometry.vsub_orthogonal_projection_mem_direction_orthogonal EuclideanGeometry.vsub_orthogonal_projection_mem_direction_orthogonal

/-- Subtracting the `orthogonal_projection` from `p` produces a result in the kernel of the linear
part of the orthogonal projection. -/
theorem orthogonal_projection_vsub_orthogonal_projection (s : AffineSubspace ℝ P) [Nonempty s]
    [CompleteSpace s.direction] (p : P) :
    orthogonalProjection s.direction (p -ᵥ orthogonalProjection s p) = 0 := by
  apply orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero
  intro c hc
  rw [← neg_vsub_eq_vsub_rev, inner_neg_right,
    orthogonal_projection_vsub_mem_direction_orthogonal s p c hc, neg_zero]
#align
  euclidean_geometry.orthogonal_projection_vsub_orthogonal_projection EuclideanGeometry.orthogonal_projection_vsub_orthogonal_projection

/-- Adding a vector to a point in the given subspace, then taking the
orthogonal projection, produces the original point if the vector was
in the orthogonal direction. -/
theorem orthogonal_projection_vadd_eq_self {s : AffineSubspace ℝ P} [Nonempty s]
    [CompleteSpace s.direction] {p : P} (hp : p ∈ s) {v : V} (hv : v ∈ s.directionᗮ) :
    orthogonalProjection s (v +ᵥ p) = ⟨p, hp⟩ := by
  have h := vsub_orthogonal_projection_mem_direction_orthogonal s (v +ᵥ p)
  rw [vadd_vsub_assoc, Submodule.add_mem_iff_right _ hv] at h
  refine' (eq_of_vsub_eq_zero _).symm
  ext
  refine' Submodule.disjoint_def.1 s.direction.orthogonal_disjoint _ _ h
  exact (_ : s.direction).2
#align
  euclidean_geometry.orthogonal_projection_vadd_eq_self EuclideanGeometry.orthogonal_projection_vadd_eq_self

/-- Adding a vector to a point in the given subspace, then taking the
orthogonal projection, produces the original point if the vector is a
multiple of the result of subtracting a point's orthogonal projection
from that point. -/
theorem orthogonal_projection_vadd_smul_vsub_orthogonal_projection {s : AffineSubspace ℝ P}
    [Nonempty s] [CompleteSpace s.direction] {p1 : P} (p2 : P) (r : ℝ) (hp : p1 ∈ s) :
    orthogonalProjection s (r • (p2 -ᵥ orthogonalProjection s p2 : V) +ᵥ p1) = ⟨p1, hp⟩ :=
  orthogonal_projection_vadd_eq_self hp
    (Submodule.smul_mem _ _ (vsub_orthogonal_projection_mem_direction_orthogonal s _))
#align
  euclidean_geometry.orthogonal_projection_vadd_smul_vsub_orthogonal_projection EuclideanGeometry.orthogonal_projection_vadd_smul_vsub_orthogonal_projection

/-- The square of the distance from a point in `s` to `p2` equals the
sum of the squares of the distances of the two points to the
`orthogonal_projection`. -/
theorem dist_sq_eq_dist_orthogonal_projection_sq_add_dist_orthogonal_projection_sq
    {s : AffineSubspace ℝ P} [Nonempty s] [CompleteSpace s.direction] {p1 : P} (p2 : P)
    (hp1 : p1 ∈ s) :
    dist p1 p2 * dist p1 p2 =
      dist p1 (orthogonalProjection s p2) * dist p1 (orthogonalProjection s p2) +
        dist p2 (orthogonalProjection s p2) * dist p2 (orthogonalProjection s p2) :=
  by
  rw [dist_comm p2 _, dist_eq_norm_vsub V p1 _, dist_eq_norm_vsub V p1 _, dist_eq_norm_vsub V _ p2,
    ← vsub_add_vsub_cancel p1 (orthogonalProjection s p2) p2,
    norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]
  exact
    Submodule.inner_right_of_mem_orthogonal (vsub_orthogonal_projection_mem_direction p2 hp1)
      (orthogonal_projection_vsub_mem_direction_orthogonal s p2)
#align
  euclidean_geometry.dist_sq_eq_dist_orthogonal_projection_sq_add_dist_orthogonal_projection_sq EuclideanGeometry.dist_sq_eq_dist_orthogonal_projection_sq_add_dist_orthogonal_projection_sq

/-- The square of the distance between two points constructed by
adding multiples of the same orthogonal vector to points in the same
subspace. -/
theorem dist_sq_smul_orthogonal_vadd_smul_orthogonal_vadd {s : AffineSubspace ℝ P} {p1 p2 : P}
    (hp1 : p1 ∈ s) (hp2 : p2 ∈ s) (r1 r2 : ℝ) {v : V} (hv : v ∈ s.directionᗮ) :
    dist (r1 • v +ᵥ p1) (r2 • v +ᵥ p2) * dist (r1 • v +ᵥ p1) (r2 • v +ᵥ p2) =
      dist p1 p2 * dist p1 p2 + (r1 - r2) * (r1 - r2) * (‖v‖ * ‖v‖) :=
  calc
    dist (r1 • v +ᵥ p1) (r2 • v +ᵥ p2) * dist (r1 • v +ᵥ p1) (r2 • v +ᵥ p2) =
        ‖p1 -ᵥ p2 + (r1 - r2) • v‖ * ‖p1 -ᵥ p2 + (r1 - r2) • v‖ :=
      by
      rw [dist_eq_norm_vsub V (r1 • v +ᵥ p1), vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, sub_smul,
        add_comm, add_sub_assoc]
    _ = ‖p1 -ᵥ p2‖ * ‖p1 -ᵥ p2‖ + ‖(r1 - r2) • v‖ * ‖(r1 - r2) • v‖ :=
      norm_add_sq_eq_norm_sq_add_norm_sq_real
        (Submodule.inner_right_of_mem_orthogonal (vsub_mem_direction hp1 hp2)
          (Submodule.smul_mem _ _ hv))
    _ = ‖(p1 -ᵥ p2 : V)‖ * ‖(p1 -ᵥ p2 : V)‖ + |r1 - r2| * |r1 - r2| * ‖v‖ * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      ring
    _ = dist p1 p2 * dist p1 p2 + (r1 - r2) * (r1 - r2) * (‖v‖ * ‖v‖) := by
      rw [dist_eq_norm_vsub V p1, abs_mul_abs_self, mul_assoc]
    
#align
  euclidean_geometry.dist_sq_smul_orthogonal_vadd_smul_orthogonal_vadd EuclideanGeometry.dist_sq_smul_orthogonal_vadd_smul_orthogonal_vadd

/-- Reflection in an affine subspace, which is expected to be nonempty
and complete.  The word "reflection" is sometimes understood to mean
specifically reflection in a codimension-one subspace, and sometimes
more generally to cover operations such as reflection in a point.  The
definition here, of reflection in an affine subspace, is a more
general sense of the word that includes both those common cases. -/
def reflection (s : AffineSubspace ℝ P) [Nonempty s] [CompleteSpace s.direction] : P ≃ᵃⁱ[ℝ] P :=
  AffineIsometryEquiv.mk' (fun p => ↑(orthogonalProjection s p) -ᵥ p +ᵥ orthogonalProjection s p)
    (reflection s.direction) (↑(Classical.arbitrary s))
    (by 
      intro p
      let v := p -ᵥ ↑(Classical.arbitrary s)
      let a : V := _root_.orthogonal_projection s.direction v
      let b : P := ↑(Classical.arbitrary s)
      have key : a +ᵥ b -ᵥ (v +ᵥ b) +ᵥ (a +ᵥ b) = a + a - v +ᵥ (b -ᵥ b +ᵥ b) := by
        rw [← add_vadd, vsub_vadd_eq_vsub_sub, vsub_vadd, vadd_vsub]
        congr 1
        abel
      have : p = v +ᵥ ↑(Classical.arbitrary s) := (vsub_vadd p ↑(Classical.arbitrary s)).symm
      simpa only [coe_vadd, reflection_apply, AffineMap.map_vadd, orthogonal_projection_linear,
        orthogonal_projection_mem_subspace_eq_self, vadd_vsub, ContinuousLinearMap.coe_coe,
        ContinuousLinearEquiv.coe_coe, this] using key)
#align euclidean_geometry.reflection EuclideanGeometry.reflection

/-- The result of reflecting. -/
theorem reflection_apply (s : AffineSubspace ℝ P) [Nonempty s] [CompleteSpace s.direction] (p : P) :
    reflection s p = ↑(orthogonalProjection s p) -ᵥ p +ᵥ orthogonalProjection s p :=
  rfl
#align euclidean_geometry.reflection_apply EuclideanGeometry.reflection_apply

theorem eq_reflection_of_eq_subspace {s s' : AffineSubspace ℝ P} [Nonempty s] [Nonempty s']
    [CompleteSpace s.direction] [CompleteSpace s'.direction] (h : s = s') (p : P) :
    (reflection s p : P) = (reflection s' p : P) := by subst h
#align
  euclidean_geometry.eq_reflection_of_eq_subspace EuclideanGeometry.eq_reflection_of_eq_subspace

/-- Reflecting twice in the same subspace. -/
@[simp]
theorem reflection_reflection (s : AffineSubspace ℝ P) [Nonempty s] [CompleteSpace s.direction]
    (p : P) : reflection s (reflection s p) = p := by
  have :
    ∀ a : s,
      ∀ b : V,
        (_root_.orthogonal_projection s.direction) b = 0 →
          reflection s (reflection s (b +ᵥ a)) = b +ᵥ a :=
    by 
    intro a b h
    have : (a : P) -ᵥ (b +ᵥ a) = -b := by rw [vsub_vadd_eq_vsub_sub, vsub_self, zero_sub]
    simp [reflection, h, this]
  rw [← vsub_vadd p (orthogonalProjection s p)]
  exact this (orthogonalProjection s p) _ (orthogonal_projection_vsub_orthogonal_projection s p)
#align euclidean_geometry.reflection_reflection EuclideanGeometry.reflection_reflection

/-- Reflection is its own inverse. -/
@[simp]
theorem reflection_symm (s : AffineSubspace ℝ P) [Nonempty s] [CompleteSpace s.direction] :
    (reflection s).symm = reflection s := by 
  ext
  rw [← (reflection s).Injective.eq_iff]
  simp
#align euclidean_geometry.reflection_symm EuclideanGeometry.reflection_symm

/-- Reflection is involutive. -/
theorem reflection_involutive (s : AffineSubspace ℝ P) [Nonempty s] [CompleteSpace s.direction] :
    Function.Involutive (reflection s) :=
  reflection_reflection s
#align euclidean_geometry.reflection_involutive EuclideanGeometry.reflection_involutive

/-- A point is its own reflection if and only if it is in the
subspace. -/
theorem reflection_eq_self_iff {s : AffineSubspace ℝ P} [Nonempty s] [CompleteSpace s.direction]
    (p : P) : reflection s p = p ↔ p ∈ s := by
  rw [← orthogonal_projection_eq_self_iff, reflection_apply]
  constructor
  · intro h
    rw [← @vsub_eq_zero_iff_eq V, vadd_vsub_assoc, ← two_smul ℝ (↑(orthogonalProjection s p) -ᵥ p),
      smul_eq_zero] at h
    norm_num at h
    exact h
  · intro h
    simp [h]
#align euclidean_geometry.reflection_eq_self_iff EuclideanGeometry.reflection_eq_self_iff

/-- Reflecting a point in two subspaces produces the same result if
and only if the point has the same orthogonal projection in each of
those subspaces. -/
theorem reflection_eq_iff_orthogonal_projection_eq (s₁ s₂ : AffineSubspace ℝ P) [Nonempty s₁]
    [Nonempty s₂] [CompleteSpace s₁.direction] [CompleteSpace s₂.direction] (p : P) :
    reflection s₁ p = reflection s₂ p ↔
      (orthogonalProjection s₁ p : P) = orthogonalProjection s₂ p :=
  by 
  rw [reflection_apply, reflection_apply]
  constructor
  · intro h
    rw [← @vsub_eq_zero_iff_eq V, vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_comm, add_sub_assoc,
      vsub_sub_vsub_cancel_right, ←
      two_smul ℝ ((orthogonalProjection s₁ p : P) -ᵥ orthogonalProjection s₂ p), smul_eq_zero] at h
    norm_num at h
    exact h
  · intro h
    rw [h]
#align
  euclidean_geometry.reflection_eq_iff_orthogonal_projection_eq EuclideanGeometry.reflection_eq_iff_orthogonal_projection_eq

/-- The distance between `p₁` and the reflection of `p₂` equals that
between the reflection of `p₁` and `p₂`. -/
theorem dist_reflection (s : AffineSubspace ℝ P) [Nonempty s] [CompleteSpace s.direction]
    (p₁ p₂ : P) : dist p₁ (reflection s p₂) = dist (reflection s p₁) p₂ := by
  conv_lhs => rw [← reflection_reflection s p₁]
  exact (reflection s).dist_map _ _
#align euclidean_geometry.dist_reflection EuclideanGeometry.dist_reflection

/-- A point in the subspace is equidistant from another point and its
reflection. -/
theorem dist_reflection_eq_of_mem (s : AffineSubspace ℝ P) [Nonempty s] [CompleteSpace s.direction]
    {p₁ : P} (hp₁ : p₁ ∈ s) (p₂ : P) : dist p₁ (reflection s p₂) = dist p₁ p₂ := by
  rw [← reflection_eq_self_iff p₁] at hp₁
  convert (reflection s).dist_map p₁ p₂
  rw [hp₁]
#align euclidean_geometry.dist_reflection_eq_of_mem EuclideanGeometry.dist_reflection_eq_of_mem

/-- The reflection of a point in a subspace is contained in any larger
subspace containing both the point and the subspace reflected in. -/
theorem reflection_mem_of_le_of_mem {s₁ s₂ : AffineSubspace ℝ P} [Nonempty s₁]
    [CompleteSpace s₁.direction] (hle : s₁ ≤ s₂) {p : P} (hp : p ∈ s₂) : reflection s₁ p ∈ s₂ := by
  rw [reflection_apply]
  have ho : ↑(orthogonalProjection s₁ p) ∈ s₂ := hle (orthogonal_projection_mem p)
  exact vadd_mem_of_mem_direction (vsub_mem_direction ho hp) ho
#align euclidean_geometry.reflection_mem_of_le_of_mem EuclideanGeometry.reflection_mem_of_le_of_mem

/-- Reflecting an orthogonal vector plus a point in the subspace
produces the negation of that vector plus the point. -/
theorem reflection_orthogonal_vadd {s : AffineSubspace ℝ P} [Nonempty s] [CompleteSpace s.direction]
    {p : P} (hp : p ∈ s) {v : V} (hv : v ∈ s.directionᗮ) : reflection s (v +ᵥ p) = -v +ᵥ p := by
  rw [reflection_apply, orthogonal_projection_vadd_eq_self hp hv, vsub_vadd_eq_vsub_sub]
  simp
#align euclidean_geometry.reflection_orthogonal_vadd EuclideanGeometry.reflection_orthogonal_vadd

/-- Reflecting a vector plus a point in the subspace produces the
negation of that vector plus the point if the vector is a multiple of
the result of subtracting a point's orthogonal projection from that
point. -/
theorem reflection_vadd_smul_vsub_orthogonal_projection {s : AffineSubspace ℝ P} [Nonempty s]
    [CompleteSpace s.direction] {p₁ : P} (p₂ : P) (r : ℝ) (hp₁ : p₁ ∈ s) :
    reflection s (r • (p₂ -ᵥ orthogonalProjection s p₂) +ᵥ p₁) =
      -(r • (p₂ -ᵥ orthogonalProjection s p₂)) +ᵥ p₁ :=
  reflection_orthogonal_vadd hp₁
    (Submodule.smul_mem _ _ (vsub_orthogonal_projection_mem_direction_orthogonal s _))
#align
  euclidean_geometry.reflection_vadd_smul_vsub_orthogonal_projection EuclideanGeometry.reflection_vadd_smul_vsub_orthogonal_projection

omit V

variable (P)

/-- A `sphere P` bundles a `center` and `radius`. This definition does not require the radius to
be positive; that should be given as a hypothesis to lemmas that require it. -/
@[ext]
structure Sphere where
  center : P
  radius : ℝ
#align euclidean_geometry.sphere EuclideanGeometry.Sphere

variable {P}

instance [Nonempty P] : Nonempty (Sphere P) :=
  ⟨⟨Classical.arbitrary P, 0⟩⟩

instance : Coe (Sphere P) (Set P) :=
  ⟨fun s => Metric.sphere s.center s.radius⟩

instance : Membership P (Sphere P) :=
  ⟨fun p s => p ∈ (s : Set P)⟩

theorem Sphere.mk_center (c : P) (r : ℝ) : (⟨c, r⟩ : Sphere P).center = c :=
  rfl
#align euclidean_geometry.sphere.mk_center EuclideanGeometry.Sphere.mk_center

theorem Sphere.mk_radius (c : P) (r : ℝ) : (⟨c, r⟩ : Sphere P).radius = r :=
  rfl
#align euclidean_geometry.sphere.mk_radius EuclideanGeometry.Sphere.mk_radius

@[simp]
theorem Sphere.mk_center_radius (s : Sphere P) : (⟨s.center, s.radius⟩ : Sphere P) = s := by
  ext <;> rfl
#align euclidean_geometry.sphere.mk_center_radius EuclideanGeometry.Sphere.mk_center_radius

theorem Sphere.coe_def (s : Sphere P) : (s : Set P) = Metric.sphere s.center s.radius :=
  rfl
#align euclidean_geometry.sphere.coe_def EuclideanGeometry.Sphere.coe_def

@[simp]
theorem Sphere.coe_mk (c : P) (r : ℝ) : ↑(⟨c, r⟩ : Sphere P) = Metric.sphere c r :=
  rfl
#align euclidean_geometry.sphere.coe_mk EuclideanGeometry.Sphere.coe_mk

@[simp]
theorem Sphere.mem_coe {p : P} {s : Sphere P} : p ∈ (s : Set P) ↔ p ∈ s :=
  Iff.rfl
#align euclidean_geometry.sphere.mem_coe EuclideanGeometry.Sphere.mem_coe

theorem mem_sphere {p : P} {s : Sphere P} : p ∈ s ↔ dist p s.center = s.radius :=
  Iff.rfl
#align euclidean_geometry.mem_sphere EuclideanGeometry.mem_sphere

theorem mem_sphere' {p : P} {s : Sphere P} : p ∈ s ↔ dist s.center p = s.radius :=
  Metric.mem_sphere'
#align euclidean_geometry.mem_sphere' EuclideanGeometry.mem_sphere'

theorem subset_sphere {ps : Set P} {s : Sphere P} : ps ⊆ s ↔ ∀ p ∈ ps, p ∈ s :=
  Iff.rfl
#align euclidean_geometry.subset_sphere EuclideanGeometry.subset_sphere

theorem dist_of_mem_subset_sphere {p : P} {ps : Set P} {s : Sphere P} (hp : p ∈ ps)
    (hps : ps ⊆ (s : Set P)) : dist p s.center = s.radius :=
  mem_sphere.1 (Sphere.mem_coe.1 (Set.mem_of_mem_of_subset hp hps))
#align euclidean_geometry.dist_of_mem_subset_sphere EuclideanGeometry.dist_of_mem_subset_sphere

theorem dist_of_mem_subset_mk_sphere {p c : P} {ps : Set P} {r : ℝ} (hp : p ∈ ps)
    (hps : ps ⊆ ↑(⟨c, r⟩ : Sphere P)) : dist p c = r :=
  dist_of_mem_subset_sphere hp hps
#align
  euclidean_geometry.dist_of_mem_subset_mk_sphere EuclideanGeometry.dist_of_mem_subset_mk_sphere

theorem Sphere.ne_iff {s₁ s₂ : Sphere P} :
    s₁ ≠ s₂ ↔ s₁.center ≠ s₂.center ∨ s₁.radius ≠ s₂.radius := by
  rw [← not_and_or, ← sphere.ext_iff]
#align euclidean_geometry.sphere.ne_iff EuclideanGeometry.Sphere.ne_iff

theorem Sphere.center_eq_iff_eq_of_mem {s₁ s₂ : Sphere P} {p : P} (hs₁ : p ∈ s₁) (hs₂ : p ∈ s₂) :
    s₁.center = s₂.center ↔ s₁ = s₂ := by
  refine' ⟨fun h => sphere.ext _ _ h _, fun h => h ▸ rfl⟩
  rw [mem_sphere] at hs₁ hs₂
  rw [← hs₁, ← hs₂, h]
#align
  euclidean_geometry.sphere.center_eq_iff_eq_of_mem EuclideanGeometry.Sphere.center_eq_iff_eq_of_mem

theorem Sphere.center_ne_iff_ne_of_mem {s₁ s₂ : Sphere P} {p : P} (hs₁ : p ∈ s₁) (hs₂ : p ∈ s₂) :
    s₁.center ≠ s₂.center ↔ s₁ ≠ s₂ :=
  (Sphere.center_eq_iff_eq_of_mem hs₁ hs₂).Not
#align
  euclidean_geometry.sphere.center_ne_iff_ne_of_mem EuclideanGeometry.Sphere.center_ne_iff_ne_of_mem

theorem dist_center_eq_dist_center_of_mem_sphere {p₁ p₂ : P} {s : Sphere P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) : dist p₁ s.center = dist p₂ s.center := by
  rw [mem_sphere.1 hp₁, mem_sphere.1 hp₂]
#align
  euclidean_geometry.dist_center_eq_dist_center_of_mem_sphere EuclideanGeometry.dist_center_eq_dist_center_of_mem_sphere

theorem dist_center_eq_dist_center_of_mem_sphere' {p₁ p₂ : P} {s : Sphere P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) : dist s.center p₁ = dist s.center p₂ := by
  rw [mem_sphere'.1 hp₁, mem_sphere'.1 hp₂]
#align
  euclidean_geometry.dist_center_eq_dist_center_of_mem_sphere' EuclideanGeometry.dist_center_eq_dist_center_of_mem_sphere'

/-- A set of points is cospherical if they are equidistant from some
point.  In two dimensions, this is the same thing as being
concyclic. -/
def Cospherical (ps : Set P) : Prop :=
  ∃ (center : P)(radius : ℝ), ∀ p ∈ ps, dist p center = radius
#align euclidean_geometry.cospherical EuclideanGeometry.Cospherical

/-- The definition of `cospherical`. -/
theorem cospherical_def (ps : Set P) :
    Cospherical ps ↔ ∃ (center : P)(radius : ℝ), ∀ p ∈ ps, dist p center = radius :=
  Iff.rfl
#align euclidean_geometry.cospherical_def EuclideanGeometry.cospherical_def

/-- A set of points is cospherical if and only if they lie in some sphere. -/
theorem cospherical_iff_exists_sphere {ps : Set P} :
    Cospherical ps ↔ ∃ s : Sphere P, ps ⊆ (s : Set P) := by
  refine' ⟨fun h => _, fun h => _⟩
  · rcases h with ⟨c, r, h⟩
    exact ⟨⟨c, r⟩, h⟩
  · rcases h with ⟨s, h⟩
    exact ⟨s.center, s.radius, h⟩
#align
  euclidean_geometry.cospherical_iff_exists_sphere EuclideanGeometry.cospherical_iff_exists_sphere

/-- The set of points in a sphere is cospherical. -/
theorem Sphere.cospherical (s : Sphere P) : Cospherical (s : Set P) :=
  cospherical_iff_exists_sphere.2 ⟨s, Set.Subset.rfl⟩
#align euclidean_geometry.sphere.cospherical EuclideanGeometry.Sphere.cospherical

/-- A subset of a cospherical set is cospherical. -/
theorem Cospherical.subset {ps₁ ps₂ : Set P} (hs : ps₁ ⊆ ps₂) (hc : Cospherical ps₂) :
    Cospherical ps₁ := by 
  rcases hc with ⟨c, r, hcr⟩
  exact ⟨c, r, fun p hp => hcr p (hs hp)⟩
#align euclidean_geometry.cospherical.subset EuclideanGeometry.Cospherical.subset

include V

/-- The empty set is cospherical. -/
theorem cosphericalEmpty : Cospherical (∅ : Set P) := by
  use add_torsor.nonempty.some
  simp
#align euclidean_geometry.cospherical_empty EuclideanGeometry.cosphericalEmpty

omit V

/-- A single point is cospherical. -/
theorem cosphericalSingleton (p : P) : Cospherical ({p} : Set P) := by
  use p
  simp
#align euclidean_geometry.cospherical_singleton EuclideanGeometry.cosphericalSingleton

include V

/-- Two points are cospherical. -/
theorem cosphericalPair (p₁ p₂ : P) : Cospherical ({p₁, p₂} : Set P) := by
  use (2⁻¹ : ℝ) • (p₂ -ᵥ p₁) +ᵥ p₁, (2⁻¹ : ℝ) * dist p₂ p₁
  intro p
  rw [Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro ⟨_ | _⟩
  · rw [dist_eq_norm_vsub V p₁, vsub_vadd_eq_vsub_sub, vsub_self, zero_sub, norm_neg, norm_smul,
      dist_eq_norm_vsub V p₂]
    simp
  · rw [H, dist_eq_norm_vsub V p₂, vsub_vadd_eq_vsub_sub, dist_eq_norm_vsub V p₂]
    conv_lhs => 
      congr
      congr
      rw [← one_smul ℝ (p₂ -ᵥ p₁ : V)]
    rw [← sub_smul, norm_smul]
    norm_num
#align euclidean_geometry.cospherical_pair EuclideanGeometry.cosphericalPair

/-- Any three points in a cospherical set are affinely independent. -/
theorem Cospherical.affine_independent {s : Set P} (hs : Cospherical s) {p : Fin 3 → P}
    (hps : Set.range p ⊆ s) (hpi : Function.Injective p) : AffineIndependent ℝ p := by
  rw [affine_independent_iff_not_collinear]
  intro hc
  rw [collinear_iff_of_mem (Set.mem_range_self (0 : Fin 3))] at hc
  rcases hc with ⟨v, hv⟩
  rw [Set.forall_range_iff] at hv
  have hv0 : v ≠ 0 := by 
    intro h
    have he : p 1 = p 0 := by simpa [h] using hv 1
    exact (by decide : (1 : Fin 3) ≠ 0) (hpi he)
  rcases hs with ⟨c, r, hs⟩
  have hs' := fun i => hs (p i) (Set.mem_of_mem_of_subset (Set.mem_range_self _) hps)
  choose f hf using hv
  have hsd : ∀ i, dist (f i • v +ᵥ p 0) c = r := by
    intro i
    rw [← hf]
    exact hs' i
  have hf0 : f 0 = 0 := by 
    have hf0' := hf 0
    rw [eq_comm, ← @vsub_eq_zero_iff_eq V, vadd_vsub, smul_eq_zero] at hf0'
    simpa [hv0] using hf0'
  have hfi : Function.Injective f := by 
    intro i j h
    have hi := hf i
    rw [h, ← hf j] at hi
    exact hpi hi
  simp_rw [← hsd 0, hf0, zero_smul, zero_vadd, dist_smul_vadd_eq_dist (p 0) c hv0] at hsd
  have hfn0 : ∀ i, i ≠ 0 → f i ≠ 0 := fun i => (hfi.ne_iff' hf0).2
  have hfn0' : ∀ i, i ≠ 0 → f i = -2 * ⟪v, p 0 -ᵥ c⟫ / ⟪v, v⟫ := by
    intro i hi
    have hsdi := hsd i
    simpa [hfn0, hi] using hsdi
  have hf12 : f 1 = f 2 := by rw [hfn0' 1 (by decide), hfn0' 2 (by decide)]
  exact (by decide : (1 : Fin 3) ≠ 2) (hfi hf12)
#align
  euclidean_geometry.cospherical.affine_independent EuclideanGeometry.Cospherical.affine_independent

/-- Any three points in a cospherical set are affinely independent. -/
theorem Cospherical.affine_independent_of_mem_of_ne {s : Set P} (hs : Cospherical s) {p₁ p₂ p₃ : P}
    (h₁ : p₁ ∈ s) (h₂ : p₂ ∈ s) (h₃ : p₃ ∈ s) (h₁₂ : p₁ ≠ p₂) (h₁₃ : p₁ ≠ p₃) (h₂₃ : p₂ ≠ p₃) :
    AffineIndependent ℝ ![p₁, p₂, p₃] := by
  refine' hs.affine_independent _ _
  · simp [h₁, h₂, h₃, Set.insert_subset]
  · erw [Fin.cons_injective_iff, Fin.cons_injective_iff]
    simp [h₁₂, h₁₃, h₂₃, Function.Injective]
#align
  euclidean_geometry.cospherical.affine_independent_of_mem_of_ne EuclideanGeometry.Cospherical.affine_independent_of_mem_of_ne

/-- The three points of a cospherical set are affinely independent. -/
theorem Cospherical.affine_independent_of_ne {p₁ p₂ p₃ : P}
    (hs : Cospherical ({p₁, p₂, p₃} : Set P)) (h₁₂ : p₁ ≠ p₂) (h₁₃ : p₁ ≠ p₃) (h₂₃ : p₂ ≠ p₃) :
    AffineIndependent ℝ ![p₁, p₂, p₃] :=
  hs.affine_independent_of_mem_of_ne (Set.mem_insert _ _)
    (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) h₁₂ h₁₃ h₂₃
#align
  euclidean_geometry.cospherical.affine_independent_of_ne EuclideanGeometry.Cospherical.affine_independent_of_ne

/-- Suppose that `p₁` and `p₂` lie in spheres `s₁` and `s₂`.  Then the vector between the centers
of those spheres is orthogonal to that between `p₁` and `p₂`; this is a version of
`inner_vsub_vsub_of_dist_eq_of_dist_eq` for bundled spheres.  (In two dimensions, this says that
the diagonals of a kite are orthogonal.) -/
theorem inner_vsub_vsub_of_mem_sphere_of_mem_sphere {p₁ p₂ : P} {s₁ s₂ : Sphere P} (hp₁s₁ : p₁ ∈ s₁)
    (hp₂s₁ : p₂ ∈ s₁) (hp₁s₂ : p₁ ∈ s₂) (hp₂s₂ : p₂ ∈ s₂) :
    ⟪s₂.center -ᵥ s₁.center, p₂ -ᵥ p₁⟫ = 0 :=
  inner_vsub_vsub_of_dist_eq_of_dist_eq (dist_center_eq_dist_center_of_mem_sphere hp₁s₁ hp₂s₁)
    (dist_center_eq_dist_center_of_mem_sphere hp₁s₂ hp₂s₂)
#align
  euclidean_geometry.inner_vsub_vsub_of_mem_sphere_of_mem_sphere EuclideanGeometry.inner_vsub_vsub_of_mem_sphere_of_mem_sphere

/-- Two spheres intersect in at most two points in a two-dimensional subspace containing their
centers; this is a version of `eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two` for bundled
spheres. -/
theorem eq_of_mem_sphere_of_mem_sphere_of_mem_of_finrank_eq_two {s : AffineSubspace ℝ P}
    [FiniteDimensional ℝ s.direction] (hd : finrank ℝ s.direction = 2) {s₁ s₂ : Sphere P}
    {p₁ p₂ p : P} (hs₁ : s₁.center ∈ s) (hs₂ : s₂.center ∈ s) (hp₁s : p₁ ∈ s) (hp₂s : p₂ ∈ s)
    (hps : p ∈ s) (hs : s₁ ≠ s₂) (hp : p₁ ≠ p₂) (hp₁s₁ : p₁ ∈ s₁) (hp₂s₁ : p₂ ∈ s₁) (hps₁ : p ∈ s₁)
    (hp₁s₂ : p₁ ∈ s₂) (hp₂s₂ : p₂ ∈ s₂) (hps₂ : p ∈ s₂) : p = p₁ ∨ p = p₂ :=
  eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two hd hs₁ hs₂ hp₁s hp₂s hps
    ((Sphere.center_ne_iff_ne_of_mem hps₁ hps₂).2 hs) hp hp₁s₁ hp₂s₁ hps₁ hp₁s₂ hp₂s₂ hps₂
#align
  euclidean_geometry.eq_of_mem_sphere_of_mem_sphere_of_mem_of_finrank_eq_two EuclideanGeometry.eq_of_mem_sphere_of_mem_sphere_of_mem_of_finrank_eq_two

/-- Two spheres intersect in at most two points in two-dimensional space; this is a version of
`eq_of_dist_eq_of_dist_eq_of_finrank_eq_two` for bundled spheres. -/
theorem eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two [FiniteDimensional ℝ V]
    (hd : finrank ℝ V = 2) {s₁ s₂ : Sphere P} {p₁ p₂ p : P} (hs : s₁ ≠ s₂) (hp : p₁ ≠ p₂)
    (hp₁s₁ : p₁ ∈ s₁) (hp₂s₁ : p₂ ∈ s₁) (hps₁ : p ∈ s₁) (hp₁s₂ : p₁ ∈ s₂) (hp₂s₂ : p₂ ∈ s₂)
    (hps₂ : p ∈ s₂) : p = p₁ ∨ p = p₂ :=
  eq_of_dist_eq_of_dist_eq_of_finrank_eq_two hd ((Sphere.center_ne_iff_ne_of_mem hps₁ hps₂).2 hs) hp
    hp₁s₁ hp₂s₁ hps₁ hp₁s₂ hp₂s₂ hps₂
#align
  euclidean_geometry.eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two EuclideanGeometry.eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two

/-- A set of points is concyclic if it is cospherical and coplanar. (Most results are stated
directly in terms of `cospherical` instead of using `concyclic`.) -/
structure Concyclic (ps : Set P) : Prop where
  Cospherical : Cospherical ps
  Coplanar : Coplanar ℝ ps
#align euclidean_geometry.concyclic EuclideanGeometry.Concyclic

/-- A subset of a concyclic set is concyclic. -/
theorem Concyclic.subset {ps₁ ps₂ : Set P} (hs : ps₁ ⊆ ps₂) (h : Concyclic ps₂) : Concyclic ps₁ :=
  ⟨h.1.Subset hs, h.2.Subset hs⟩
#align euclidean_geometry.concyclic.subset EuclideanGeometry.Concyclic.subset

/-- The empty set is concyclic. -/
theorem concyclicEmpty : Concyclic (∅ : Set P) :=
  ⟨cosphericalEmpty, coplanar_empty ℝ P⟩
#align euclidean_geometry.concyclic_empty EuclideanGeometry.concyclicEmpty

/-- A single point is concyclic. -/
theorem concyclicSingleton (p : P) : Concyclic ({p} : Set P) :=
  ⟨cosphericalSingleton p, coplanar_singleton ℝ p⟩
#align euclidean_geometry.concyclic_singleton EuclideanGeometry.concyclicSingleton

/-- Two points are concyclic. -/
theorem concyclicPair (p₁ p₂ : P) : Concyclic ({p₁, p₂} : Set P) :=
  ⟨cosphericalPair p₁ p₂, coplanar_pair ℝ p₁ p₂⟩
#align euclidean_geometry.concyclic_pair EuclideanGeometry.concyclicPair

end EuclideanGeometry

