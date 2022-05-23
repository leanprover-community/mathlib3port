/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathbin.Analysis.NormedSpace.Banach
import Mathbin.Analysis.NormedSpace.FiniteDimension
import Mathbin.Analysis.Calculus.AffineMap
import Mathbin.Analysis.Convex.Combination
import Mathbin.LinearAlgebra.AffineSpace.Basis
import Mathbin.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Bases in normed affine spaces.

This file contains results about bases in normed affine spaces.

## Main definitions:

 * `continuous_barycentric_coord`
 * `is_open_map_barycentric_coord`
 * `interior_convex_hull_aff_basis`
 * `exists_subset_affine_independent_span_eq_top_of_open`
 * `interior_convex_hull_nonempty_iff_aff_span_eq_top`
-/


section Barycentric

variable {ι 𝕜 E P : Type _} [NondiscreteNormedField 𝕜] [CompleteSpace 𝕜]

variable [NormedGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

variable [MetricSpace P] [NormedAddTorsor E P]

variable (b : AffineBasis ι 𝕜 P)

@[continuity]
theorem continuous_barycentric_coord (i : ι) : Continuous (b.Coord i) :=
  (b.Coord i).continuous_of_finite_dimensional

attribute [local instance] FiniteDimensional.complete

theorem is_open_map_barycentric_coord [Nontrivial ι] (i : ι) : IsOpenMap (b.Coord i) :=
  (b.Coord i).IsOpenMap (continuous_barycentric_coord b i) (b.surjective_coord i)

theorem smooth_barycentric_coord (b : AffineBasis ι 𝕜 E) (i : ι) : ContDiff 𝕜 ⊤ (b.Coord i) :=
  (⟨b.Coord i, continuous_barycentric_coord b i⟩ : E →A[𝕜] 𝕜).ContDiff

end Barycentric

open Set

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: classical ... #[[]]
/-- Given a finite-dimensional normed real vector space, the interior of the convex hull of an
affine basis is the set of points whose barycentric coordinates are strictly positive with respect
to this basis.

TODO Restate this result for affine spaces (instead of vector spaces) once the definition of
convexity is generalised to this setting. -/
theorem interior_convex_hull_aff_basis {ι E : Type _} [Fintype ι] [NormedGroup E] [NormedSpace ℝ E]
    (b : AffineBasis ι ℝ E) : Interior (convexHull ℝ (Range b.points)) = { x | ∀ i, 0 < b.Coord i x } := by
  cases subsingleton_or_nontrivial ι
  · -- The zero-dimensional case.
    suffices range b.points = univ by
      simp [this]
    refine' AffineSubspace.eq_univ_of_subsingleton_span_eq_top _ b.tot
    rw [← image_univ]
    exact subsingleton.image subsingleton_of_subsingleton b.points
    
  · -- The positive-dimensional case.
    have : FiniteDimensional ℝ E := by
      classical
      obtain ⟨i⟩ := (inferInstance : Nonempty ι)
      exact FiniteDimensional.of_fintype_basis (b.basis_of i)
    have : convexHull ℝ (range b.points) = ⋂ i, b.coord i ⁻¹' Ici 0 := by
      rw [convex_hull_affine_basis_eq_nonneg_barycentric b]
      ext
      simp
    ext
    simp only [this, interior_Inter_of_fintype, ←
      IsOpenMap.preimage_interior_eq_interior_preimage (is_open_map_barycentric_coord b _)
        (continuous_barycentric_coord b _),
      interior_Ici, mem_Inter, mem_set_of_eq, mem_Ioi, mem_preimage]
    

variable {V P : Type _} [NormedGroup V] [NormedSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

include V

open AffineMap

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (y «expr ∉ » s)
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: classical ... #[[]]
/-- Given a set `s` of affine-independent points belonging to an open set `u`, we may extend `s` to
an affine basis, all of whose elements belong to `u`. -/
theorem exists_subset_affine_independent_span_eq_top_of_open {s u : Set P} (hu : IsOpen u) (hsu : s ⊆ u)
    (hne : s.Nonempty) (h : AffineIndependent ℝ (coe : s → P)) :
    ∃ t : Set P, s ⊆ t ∧ t ⊆ u ∧ AffineIndependent ℝ (coe : t → P) ∧ affineSpan ℝ t = ⊤ := by
  obtain ⟨q, hq⟩ := hne
  obtain ⟨ε, hε, hεu⟩ := metric.is_open_iff.mp hu q (hsu hq)
  obtain ⟨t, ht₁, ht₂, ht₃⟩ := exists_subset_affine_independent_affine_span_eq_top h
  let f : P → P := fun y => line_map q y (ε / 2 / dist y q)
  have hf : ∀ y, f y ∈ u := by
    intro y
    apply hεu
    simp only [Metric.mem_ball, f, line_map_apply, dist_vadd_left, norm_smul, Real.norm_eq_abs, dist_eq_norm_vsub V y q]
    cases' eq_or_ne ∥y -ᵥ q∥ 0 with hyq hyq
    · rwa [hyq, mul_zero]
      
    rw [← norm_pos_iff, norm_norm] at hyq
    calc abs (ε / 2 / ∥y -ᵥ q∥) * ∥y -ᵥ q∥ = ε / 2 / ∥y -ᵥ q∥ * ∥y -ᵥ q∥ := by
        rw [abs_div, abs_of_pos (half_pos hε), abs_of_pos hyq]_ = ε / 2 := div_mul_cancel _ (ne_of_gtₓ hyq)_ < ε :=
        half_lt_self hε
  have hεyq : ∀ y _ : y ∉ s, ε / 2 / dist y q ≠ 0 := by
    simp only [Ne.def, div_eq_zero_iff, or_falseₓ, dist_eq_zero, bit0_eq_zero, one_ne_zero, not_or_distrib,
      ne_of_gtₓ hε, true_andₓ, not_false_iff]
    exact fun y h1 h2 => h1 (h2.symm ▸ hq)
  classical
  let w : t → ℝˣ := fun p => if hp : (p : P) ∈ s then 1 else Units.mk0 _ (hεyq (↑p) hp)
  refine' ⟨Set.Range fun p : t => line_map q p (w p : ℝ), _, _, _, _⟩
  · intro p hp
    use ⟨p, ht₁ hp⟩
    simp [w, hp]
    
  · intro y hy
    simp only [Set.mem_range, SetCoe.exists, Subtype.coe_mk] at hy
    obtain ⟨p, hp, hyq⟩ := hy
    by_cases' hps : p ∈ s <;>
      simp only [w, hps, line_map_apply_one, Units.coe_mk0, dif_neg, dif_pos, not_false_iff, Units.coe_one,
          Subtype.coe_mk] at hyq <;>
        rw [← hyq] <;> [exact hsu hps, exact hf p]
    
  · exact (ht₂.units_line_map ⟨q, ht₁ hq⟩ w).range
    
  · rw [affine_span_eq_affine_span_line_map_units (ht₁ hq) w, ht₃]
    

theorem interior_convex_hull_nonempty_iff_aff_span_eq_top [FiniteDimensional ℝ V] {s : Set V} :
    (Interior (convexHull ℝ s)).Nonempty ↔ affineSpan ℝ s = ⊤ := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨u, hu₁, hu₂, hu₃⟩ := mem_interior.mp hx
    let t : Set V := {x}
    obtain ⟨b, hb₁, hb₂, hb₃, hb₄⟩ :=
      exists_subset_affine_independent_span_eq_top_of_open hu₂ (singleton_subset_iff.mpr hu₃) (singleton_nonempty x)
        (affine_independent_of_subsingleton ℝ (coe : t → V))
    rw [eq_top_iff, ← hb₄, ← affine_span_convex_hull s]
    mono
    exact hb₂.trans hu₁
    
  · intro h
    obtain ⟨t, hts, h_tot, h_ind⟩ := exists_affine_independent ℝ V s
    suffices (Interior (convexHull ℝ (range (coe : t → V)))).Nonempty by
      rw [Subtype.range_coe_subtype, set_of_mem_eq] at this
      apply nonempty.mono _ this
      mono*
    have : Fintype t := fintypeOfFinDimAffineIndependent ℝ h_ind
    use Finset.centroid ℝ (Finset.univ : Finset t) (coe : t → V)
    rw [h, ← @set_of_mem_eq V t, ← Subtype.range_coe_subtype] at h_tot
    let b : AffineBasis t ℝ V := ⟨coe, h_ind, h_tot⟩
    rw [interior_convex_hull_aff_basis b]
    have htne : (Finset.univ : Finset t).Nonempty := by
      simpa [Finset.univ_nonempty_iff] using AffineSubspace.nonempty_of_affine_span_eq_top ℝ V V h_tot
    simp [Finset.centroid_def,
      b.coord_apply_combination_of_mem (Finset.mem_univ _)
        (Finset.sum_centroid_weights_eq_one_of_nonempty ℝ (Finset.univ : Finset t) htne),
      Finset.centroid_weights_apply, Nat.cast_pos, inv_pos, finset.card_pos.mpr htne]
    

theorem Convex.interior_nonempty_iff_affine_span_eq_top [FiniteDimensional ℝ V] {s : Set V} (hs : Convex ℝ s) :
    (Interior s).Nonempty ↔ affineSpan ℝ s = ⊤ := by
  rw [← interior_convex_hull_nonempty_iff_aff_span_eq_top, hs.convex_hull_eq]

