import Mathbin.Analysis.NormedSpace.Banach 
import Mathbin.Analysis.NormedSpace.FiniteDimension 
import Mathbin.Analysis.Convex.Combination 
import Mathbin.LinearAlgebra.AffineSpace.BarycentricCoords 
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

variable{ι 𝕜 E P : Type _}[NondiscreteNormedField 𝕜][CompleteSpace 𝕜]

variable[NormedGroup E][NormedSpace 𝕜 E][FiniteDimensional 𝕜 E]

variable[MetricSpace P][NormedAddTorsor E P]

variable{p : ι → P}(h_ind : AffineIndependent 𝕜 p)(h_tot : affineSpan 𝕜 (Set.Range p) = ⊤)

@[continuity]
theorem continuous_barycentric_coord (i : ι) : Continuous (barycentricCoord h_ind h_tot i) :=
  AffineMap.continuous_of_finite_dimensional _

attribute [local instance] FiniteDimensional.complete

theorem is_open_map_barycentric_coord [Nontrivial ι] (i : ι) : IsOpenMap (barycentricCoord h_ind h_tot i) :=
  open_mapping_affine (continuous_barycentric_coord h_ind h_tot i) (surjective_barycentric_coord h_ind h_tot i)

end Barycentric

open Set

/-- Given a finite-dimensional normed real vector space, the interior of the convex hull of an
affine basis is the set of points whose barycentric coordinates are strictly positive with respect
to this basis.

TODO Restate this result for affine spaces (instead of vector spaces) once the definition of
convexity is generalised to this setting. -/
theorem interior_convex_hull_aff_basis {ι E : Type _} [Fintype ι] [NormedGroup E] [NormedSpace ℝ E] {p : ι → E}
  (h_ind : AffineIndependent ℝ p) (h_tot : affineSpan ℝ (range p) = ⊤) :
  Interior (convexHull ℝ (range p)) = { x | ∀ i, 0 < barycentricCoord h_ind h_tot i x } :=
  by 
    cases' subsingleton_or_nontrivial ι with h h
    ·
      haveI  := h 
      suffices  : range p = univ
      ·
        simp [this]
      refine' AffineSubspace.eq_univ_of_subsingleton_span_eq_top _ h_tot 
      rw [←image_univ]
      exact subsingleton.image subsingleton_of_subsingleton p
    ·
      haveI  : FiniteDimensional ℝ E
      ·
        classical 
        obtain ⟨i⟩ := (inferInstance : Nonempty ι)
        have b := basisOfAffIndSpanEqTop h_ind h_tot i 
        exact FiniteDimensional.of_fintype_basis b 
      have  : convexHull ℝ (range p) = ⋂i, barycentricCoord h_ind h_tot i ⁻¹' Ici 0
      ·
        rw [convex_hull_affine_basis_eq_nonneg_barycentric h_ind h_tot]
        ext 
        simp 
      ext 
      simp only [this, interior_Inter_of_fintype,
        ←IsOpenMap.preimage_interior_eq_interior_preimage (continuous_barycentric_coord h_ind h_tot _)
          (is_open_map_barycentric_coord h_ind h_tot _),
        interior_Ici, mem_Inter, mem_set_of_eq, mem_Ioi, mem_preimage]

variable{V P : Type _}[NormedGroup V][NormedSpace ℝ V][MetricSpace P][NormedAddTorsor V P]

include V

open AffineMap

/-- Given a set `s` of affine-independent points belonging to an open set `u`, we may extend `s` to
an affine basis, all of whose elements belong to `u`. -/
theorem exists_subset_affine_independent_span_eq_top_of_open {s u : Set P} (hu : IsOpen u) (hsu : s ⊆ u)
  (hne : s.nonempty) (h : AffineIndependent ℝ (coeₓ : s → P)) :
  ∃ t : Set P, s ⊆ t ∧ t ⊆ u ∧ AffineIndependent ℝ (coeₓ : t → P) ∧ affineSpan ℝ t = ⊤ :=
  by 
    obtain ⟨q, hq⟩ := hne 
    obtain ⟨ε, hε, hεu⟩ := metric.is_open_iff.mp hu q (hsu hq)
    obtain ⟨t, ht₁, ht₂, ht₃⟩ := exists_subset_affine_independent_affine_span_eq_top h 
    let f : P → P := fun y => line_map q y (ε / 2 / dist y q)
    have hf : ∀ y, f y ∈ u
    ·
      intro y 
      apply hεu 
      simp only [Metric.mem_ball, f, line_map_apply, dist_vadd_left, norm_smul, Real.norm_eq_abs,
        dist_eq_norm_vsub V y q]
      cases' eq_or_ne ∥y -ᵥ q∥ 0 with hyq hyq
      ·
        rwa [hyq, mul_zero]
      rw [←norm_pos_iff, norm_norm] at hyq 
      calc (abs (ε / 2 / ∥y -ᵥ q∥)*∥y -ᵥ q∥) = (ε / 2 / ∥y -ᵥ q∥)*∥y -ᵥ q∥ :=
        by 
          rw [abs_div, abs_of_pos (half_pos hε), abs_of_pos hyq]_ = ε / 2 :=
        div_mul_cancel _ (ne_of_gtₓ hyq)_ < ε := half_lt_self hε 
    have hεyq : ∀ y _ : y ∉ s, ε / 2 / dist y q ≠ 0
    ·
      simp only [Ne.def, div_eq_zero_iff, or_falseₓ, dist_eq_zero, bit0_eq_zero, one_ne_zero, not_or_distrib,
        ne_of_gtₓ hε, true_andₓ, not_false_iff]
      finish 
    classical 
    let w : t → Units ℝ := fun p => if hp : (p : P) ∈ s then 1 else Units.mk0 _ (hεyq («expr↑ » p) hp)
    refine' ⟨Set.Range fun p : t => line_map q p (w p : ℝ), _, _, _, _⟩
    ·
      intro p hp 
      use ⟨p, ht₁ hp⟩
      simp [w, hp]
    ·
      intro y hy 
      simp only [Set.mem_range, SetCoe.exists, Subtype.coe_mk] at hy 
      obtain ⟨p, hp, hyq⟩ := hy 
      byCases' hps : p ∈ s <;>
        simp only [w, hps, line_map_apply_one, Units.coe_mk0, dif_neg, dif_pos, not_false_iff, Units.coe_one,
            Subtype.coe_mk] at hyq <;>
          rw [←hyq] <;> [exact hsu hps, exact hf p]
    ·
      exact (ht₂.units_line_map ⟨q, ht₁ hq⟩ w).range
    ·
      rw [affine_span_eq_affine_span_line_map_units (ht₁ hq) w, ht₃]

theorem interior_convex_hull_nonempty_iff_aff_span_eq_top [FiniteDimensional ℝ V] {s : Set V} :
  (Interior (convexHull ℝ s)).Nonempty ↔ affineSpan ℝ s = ⊤ :=
  by 
    split 
    ·
      rintro ⟨x, hx⟩
      obtain ⟨u, hu₁, hu₂, hu₃⟩ := mem_interior.mp hx 
      let t : Set V := {x}
      obtain ⟨b, hb₁, hb₂, hb₃, hb₄⟩ :=
        exists_subset_affine_independent_span_eq_top_of_open hu₂ (singleton_subset_iff.mpr hu₃) (singleton_nonempty x)
          (affine_independent_of_subsingleton ℝ (coeₓ : t → V))
      rw [eq_top_iff, ←hb₄, ←affine_span_convex_hull s]
      mono 
      exact hb₂.trans hu₁
    ·
      intro h 
      obtain ⟨t, hts, h_tot, h_ind⟩ := exists_affine_independent ℝ V s 
      suffices  : (Interior (convexHull ℝ (range (coeₓ : t → V)))).Nonempty
      ·
        rw [Subtype.range_coe_subtype, set_of_mem_eq] at this 
        apply nonempty.mono _ this 
        mono*
      haveI  : Fintype t := fintypeOfFinDimAffineIndependent ℝ h_ind 
      use Finset.centroid ℝ (Finset.univ : Finset t) (coeₓ : t → V)
      rw [h, ←@set_of_mem_eq V t, ←Subtype.range_coe_subtype] at h_tot 
      rw [interior_convex_hull_aff_basis h_ind h_tot]
      have htne : (Finset.univ : Finset t).Nonempty
      ·
        simpa [Finset.univ_nonempty_iff] using AffineSubspace.nonempty_of_affine_span_eq_top ℝ V V h_tot 
      simp [Finset.centroid_def,
        barycentric_coord_apply_combination_of_mem h_ind h_tot (Finset.mem_univ _)
          (Finset.sum_centroid_weights_eq_one_of_nonempty ℝ (Finset.univ : Finset t) htne),
        Finset.centroid_weights_apply, Nat.cast_pos, inv_pos, finset.card_pos.mpr htne]

