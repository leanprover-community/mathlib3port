/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathbin.Analysis.NormedSpace.FiniteDimension
import Mathbin.Analysis.Calculus.AffineMap
import Mathbin.Analysis.Convex.Combination
import Mathbin.LinearAlgebra.AffineSpace.Basis

/-!
# Bases in normed affine spaces.

This file contains results about bases in normed affine spaces.

## Main definitions:

 * `continuous_barycentric_coord`
 * `is_open_map_barycentric_coord`
 * `affine_basis.interior_convex_hull`
 * `exists_subset_affine_independent_span_eq_top_of_open`
 * `interior_convex_hull_nonempty_iff_affine_span_eq_top`
-/


section Barycentric

variable {ι 𝕜 E P : Type _} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable [MetricSpace P] [NormedAddTorsor E P]

include E

theorem is_open_map_barycentric_coord [Nontrivial ι] (b : AffineBasis ι 𝕜 P) (i : ι) : IsOpenMap (b.Coord i) :=
  AffineMap.is_open_map_linear_iff.mp <|
    (b.Coord i).linear.is_open_map_of_finite_dimensional <|
      (b.Coord i).surjective_iff_linear_surjective.mpr (b.surjective_coord i)
#align is_open_map_barycentric_coord is_open_map_barycentric_coord

variable [FiniteDimensional 𝕜 E] (b : AffineBasis ι 𝕜 P)

@[continuity]
theorem continuous_barycentric_coord (i : ι) : Continuous (b.Coord i) :=
  (b.Coord i).continuous_of_finite_dimensional
#align continuous_barycentric_coord continuous_barycentric_coord

theorem smoothBarycentricCoord (b : AffineBasis ι 𝕜 E) (i : ι) : ContDiff 𝕜 ⊤ (b.Coord i) :=
  (⟨b.Coord i, continuous_barycentric_coord b i⟩ : E →A[𝕜] 𝕜).ContDiff
#align smooth_barycentric_coord smoothBarycentricCoord

end Barycentric

open Set

/-- Given a finite-dimensional normed real vector space, the interior of the convex hull of an
affine basis is the set of points whose barycentric coordinates are strictly positive with respect
to this basis.

TODO Restate this result for affine spaces (instead of vector spaces) once the definition of
convexity is generalised to this setting. -/
theorem AffineBasis.interior_convex_hull {ι E : Type _} [Finite ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : AffineBasis ι ℝ E) : interior (convexHull ℝ (range b.points)) = { x | ∀ i, 0 < b.Coord i x } := by
  cases subsingleton_or_nontrivial ι
  · -- The zero-dimensional case.
    have : range b.points = univ := AffineSubspace.eq_univ_of_subsingleton_span_eq_top (subsingleton_range _) b.tot
    simp [this]
    
  · -- The positive-dimensional case.
    haveI : FiniteDimensional ℝ E := b.finite_dimensional
    have : convexHull ℝ (range b.points) = ⋂ i, b.coord i ⁻¹' Ici 0 := by
      rw [convex_hull_affine_basis_eq_nonneg_barycentric b, set_of_forall]
      rfl
    ext
    simp only [this, interior_Inter, ←
      IsOpenMap.preimage_interior_eq_interior_preimage (is_open_map_barycentric_coord b _)
        (continuous_barycentric_coord b _),
      interior_Ici, mem_Inter, mem_set_of_eq, mem_Ioi, mem_preimage]
    
#align affine_basis.interior_convex_hull AffineBasis.interior_convex_hull

variable {V P : Type _} [NormedAddCommGroup V] [NormedSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

include V

open AffineMap

/- ./././Mathport/Syntax/Translate/Basic.lean:611:2: warning: expanding binder collection (y «expr ∉ » s) -/
/-- Given a set `s` of affine-independent points belonging to an open set `u`, we may extend `s` to
an affine basis, all of whose elements belong to `u`. -/
theorem IsOpen.exists_between_affine_independent_span_eq_top {s u : Set P} (hu : IsOpen u) (hsu : s ⊆ u)
    (hne : s.Nonempty) (h : AffineIndependent ℝ (coe : s → P)) :
    ∃ t : Set P, s ⊆ t ∧ t ⊆ u ∧ AffineIndependent ℝ (coe : t → P) ∧ affineSpan ℝ t = ⊤ := by
  obtain ⟨q, hq⟩ := hne
  obtain ⟨ε, ε0, hεu⟩ := metric.nhds_basis_closed_ball.mem_iff.1 (hu.mem_nhds <| hsu hq)
  obtain ⟨t, ht₁, ht₂, ht₃⟩ := exists_subset_affine_independent_affine_span_eq_top h
  let f : P → P := fun y => line_map q y (ε / dist y q)
  have hf : ∀ y, f y ∈ u := by
    refine' fun y => hεu _
    simp only [f]
    rw [Metric.mem_closed_ball, line_map_apply, dist_vadd_left, norm_smul, Real.norm_eq_abs, dist_eq_norm_vsub V y q,
      abs_div, abs_of_pos ε0, abs_of_nonneg (norm_nonneg _), div_mul_comm]
    exact mul_le_of_le_one_left ε0.le (div_self_le_one _)
  have hεyq : ∀ (y) (_ : y ∉ s), ε / dist y q ≠ 0 := fun y hy =>
    div_ne_zero ε0.ne' (dist_ne_zero.2 (ne_of_mem_of_not_mem hq hy).symm)
  classical
  let w : t → ℝˣ := fun p => if hp : (p : P) ∈ s then 1 else Units.mk0 _ (hεyq (↑p) hp)
  refine' ⟨Set.range fun p : t => line_map q p (w p : ℝ), _, _, _, _⟩
  · intro p hp
    use ⟨p, ht₁ hp⟩
    simp [w, hp]
    
  · rintro y ⟨⟨p, hp⟩, rfl⟩
    by_cases hps : p ∈ s <;>
      simp only [w, hps, line_map_apply_one, Units.coe_mk0, dif_neg, dif_pos, not_false_iff, Units.coe_one,
          Subtype.coe_mk] <;>
        [exact hsu hps, exact hf p]
    
  · exact (ht₂.units_line_map ⟨q, ht₁ hq⟩ w).range
    
  · rw [affine_span_eq_affine_span_line_map_units (ht₁ hq) w, ht₃]
    
#align is_open.exists_between_affine_independent_span_eq_top IsOpen.exists_between_affine_independent_span_eq_top

/- ./././Mathport/Syntax/Translate/Basic.lean:611:2: warning: expanding binder collection (s «expr ⊆ » u) -/
theorem IsOpen.exists_subset_affine_independent_span_eq_top {u : Set P} (hu : IsOpen u) (hne : u.Nonempty) :
    ∃ (s : _)(_ : s ⊆ u), AffineIndependent ℝ (coe : s → P) ∧ affineSpan ℝ s = ⊤ := by
  rcases hne with ⟨x, hx⟩
  rcases hu.exists_between_affine_independent_span_eq_top (singleton_subset_iff.mpr hx) (singleton_nonempty _)
      (affine_independent_of_subsingleton _ _) with
    ⟨s, -, hsu, hs⟩
  exact ⟨s, hsu, hs⟩
#align is_open.exists_subset_affine_independent_span_eq_top IsOpen.exists_subset_affine_independent_span_eq_top

/-- The affine span of a nonempty open set is `⊤`. -/
theorem IsOpen.affine_span_eq_top {u : Set P} (hu : IsOpen u) (hne : u.Nonempty) : affineSpan ℝ u = ⊤ :=
  let ⟨s, hsu, hs, hs'⟩ := hu.exists_subset_affine_independent_span_eq_top hne
  top_unique <| hs' ▸ affine_span_mono _ hsu
#align is_open.affine_span_eq_top IsOpen.affine_span_eq_top

theorem affine_span_eq_top_of_nonempty_interior {s : Set V} (hs : (interior <| convexHull ℝ s).Nonempty) :
    affineSpan ℝ s = ⊤ :=
  top_unique <|
    is_open_interior.affine_span_eq_top hs ▸ (affine_span_mono _ interior_subset).trans_eq (affine_span_convex_hull _)
#align affine_span_eq_top_of_nonempty_interior affine_span_eq_top_of_nonempty_interior

theorem AffineBasis.centroid_mem_interior_convex_hull {ι} [Fintype ι] (b : AffineBasis ι ℝ V) :
    Finset.univ.centroid ℝ b.points ∈ interior (convexHull ℝ (range b.points)) := by
  haveI := b.nonempty
  simp only [b.interior_convex_hull, mem_set_of_eq, b.coord_apply_centroid (Finset.mem_univ _), inv_pos, Nat.cast_pos,
    Finset.card_pos, Finset.univ_nonempty, forall_true_iff]
#align affine_basis.centroid_mem_interior_convex_hull AffineBasis.centroid_mem_interior_convex_hull

theorem interior_convex_hull_nonempty_iff_affine_span_eq_top [FiniteDimensional ℝ V] {s : Set V} :
    (interior (convexHull ℝ s)).Nonempty ↔ affineSpan ℝ s = ⊤ := by
  refine' ⟨affine_span_eq_top_of_nonempty_interior, fun h => _⟩
  obtain ⟨t, hts, b, hb⟩ := AffineBasis.exists_affine_subbasis h
  suffices (interior (convexHull ℝ (range b.points))).Nonempty by
    rw [hb, Subtype.range_coe_subtype, set_of_mem_eq] at this
    refine' this.mono _
    mono*
  lift t to Finset V using b.finite_set
  exact ⟨_, b.centroid_mem_interior_convex_hull⟩
#align interior_convex_hull_nonempty_iff_affine_span_eq_top interior_convex_hull_nonempty_iff_affine_span_eq_top

theorem Convex.interior_nonempty_iff_affine_span_eq_top [FiniteDimensional ℝ V] {s : Set V} (hs : Convex ℝ s) :
    (interior s).Nonempty ↔ affineSpan ℝ s = ⊤ := by
  rw [← interior_convex_hull_nonempty_iff_affine_span_eq_top, hs.convex_hull_eq]
#align convex.interior_nonempty_iff_affine_span_eq_top Convex.interior_nonempty_iff_affine_span_eq_top

