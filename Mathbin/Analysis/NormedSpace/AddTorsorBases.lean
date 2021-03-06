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

variable {Ī¹ š E P : Type _} [NondiscreteNormedField š] [CompleteSpace š]

variable [NormedGroup E] [NormedSpace š E] [FiniteDimensional š E]

variable [MetricSpace P] [NormedAddTorsor E P]

variable (b : AffineBasis Ī¹ š P)

@[continuity]
theorem continuous_barycentric_coord (i : Ī¹) : Continuous (b.Coord i) :=
  (b.Coord i).continuous_of_finite_dimensional

attribute [local instance] FiniteDimensional.complete

theorem is_open_map_barycentric_coord [Nontrivial Ī¹] (i : Ī¹) : IsOpenMap (b.Coord i) :=
  (b.Coord i).IsOpenMap (continuous_barycentric_coord b i) (b.surjective_coord i)

theorem smooth_barycentric_coord (b : AffineBasis Ī¹ š E) (i : Ī¹) : ContDiff š ā¤ (b.Coord i) :=
  (āØb.Coord i, continuous_barycentric_coord b iā© : E āA[š] š).ContDiff

end Barycentric

open Set

/-- Given a finite-dimensional normed real vector space, the interior of the convex hull of an
affine basis is the set of points whose barycentric coordinates are strictly positive with respect
to this basis.

TODO Restate this result for affine spaces (instead of vector spaces) once the definition of
convexity is generalised to this setting. -/
theorem interior_convex_hull_aff_basis {Ī¹ E : Type _} [Fintype Ī¹] [NormedGroup E] [NormedSpace ā E]
    (b : AffineBasis Ī¹ ā E) : Interior (convexHull ā (Range b.points)) = { x | ā i, 0 < b.Coord i x } := by
  cases subsingleton_or_nontrivial Ī¹
  Ā· -- The zero-dimensional case.
    suffices range b.points = univ by
      simp [ā this]
    refine' AffineSubspace.eq_univ_of_subsingleton_span_eq_top _ b.tot
    rw [ā image_univ]
    exact subsingleton.image subsingleton_of_subsingleton b.points
    
  Ā· -- The positive-dimensional case.
    have : FiniteDimensional ā E := by
      classical
      obtain āØiā© := (inferInstance : Nonempty Ī¹)
      exact FiniteDimensional.of_fintype_basis (b.basis_of i)
    have : convexHull ā (range b.points) = ā i, b.coord i ā»Ā¹' Ici 0 := by
      rw [convex_hull_affine_basis_eq_nonneg_barycentric b]
      ext
      simp
    ext
    simp only [ā this, ā interior_Inter_of_fintype,
      IsOpenMap.preimage_interior_eq_interior_preimage (is_open_map_barycentric_coord b _)
        (continuous_barycentric_coord b _),
      ā interior_Ici, ā mem_Inter, ā mem_set_of_eq, ā mem_Ioi, ā mem_preimage]
    

variable {V P : Type _} [NormedGroup V] [NormedSpace ā V] [MetricSpace P] [NormedAddTorsor V P]

include V

open AffineMap

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (y Ā«expr ā Ā» s)
/-- Given a set `s` of affine-independent points belonging to an open set `u`, we may extend `s` to
an affine basis, all of whose elements belong to `u`. -/
theorem exists_subset_affine_independent_span_eq_top_of_open {s u : Set P} (hu : IsOpen u) (hsu : s ā u)
    (hne : s.Nonempty) (h : AffineIndependent ā (coe : s ā P)) :
    ā t : Set P, s ā t ā§ t ā u ā§ AffineIndependent ā (coe : t ā P) ā§ affineSpan ā t = ā¤ := by
  obtain āØq, hqā© := hne
  obtain āØĪµ, hĪµ, hĪµuā© := metric.is_open_iff.mp hu q (hsu hq)
  obtain āØt, htā, htā, htāā© := exists_subset_affine_independent_affine_span_eq_top h
  let f : P ā P := fun y => line_map q y (Īµ / 2 / dist y q)
  have hf : ā y, f y ā u := by
    intro y
    apply hĪµu
    simp only [ā Metric.mem_ball, ā f, ā line_map_apply, ā dist_vadd_left, ā norm_smul, ā Real.norm_eq_abs, ā
      dist_eq_norm_vsub V y q]
    cases' eq_or_ne ā„y -įµ„ qā„ 0 with hyq hyq
    Ā· rwa [hyq, mul_zero]
      
    rw [ā norm_pos_iff, norm_norm] at hyq
    calc abs (Īµ / 2 / ā„y -įµ„ qā„) * ā„y -įµ„ qā„ = Īµ / 2 / ā„y -įµ„ qā„ * ā„y -įµ„ qā„ := by
        rw [abs_div, abs_of_pos (half_pos hĪµ), abs_of_pos hyq]_ = Īµ / 2 := div_mul_cancel _ (ne_of_gtā hyq)_ < Īµ :=
        half_lt_self hĪµ
  have hĪµyq : ā (y) (_ : y ā s), Īµ / 2 / dist y q ā  0 := by
    simp only [ā Ne.def, ā div_eq_zero_iff, ā or_falseā, ā dist_eq_zero, ā bit0_eq_zero, ā one_ne_zero, ā
      not_or_distrib, ā ne_of_gtā hĪµ, ā true_andā, ā not_false_iff]
    exact fun y h1 h2 => h1 (h2.symm āø hq)
  classical
  let w : t ā āĖ£ := fun p => if hp : (p : P) ā s then 1 else Units.mk0 _ (hĪµyq (āp) hp)
  refine' āØSet.Range fun p : t => line_map q p (w p : ā), _, _, _, _ā©
  Ā· intro p hp
    use āØp, htā hpā©
    simp [ā w, ā hp]
    
  Ā· intro y hy
    simp only [ā Set.mem_range, ā SetCoe.exists, ā Subtype.coe_mk] at hy
    obtain āØp, hp, hyqā© := hy
    by_cases' hps : p ā s <;>
      simp only [ā w, ā hps, ā line_map_apply_one, ā Units.coe_mk0, ā dif_neg, ā dif_pos, ā not_false_iff, ā
          Units.coe_one, ā Subtype.coe_mk] at hyq <;>
        rw [ā hyq] <;> [exact hsu hps, exact hf p]
    
  Ā· exact (htā.units_line_map āØq, htā hqā© w).range
    
  Ā· rw [affine_span_eq_affine_span_line_map_units (htā hq) w, htā]
    

theorem interior_convex_hull_nonempty_iff_aff_span_eq_top [FiniteDimensional ā V] {s : Set V} :
    (Interior (convexHull ā s)).Nonempty ā affineSpan ā s = ā¤ := by
  constructor
  Ā· rintro āØx, hxā©
    obtain āØu, huā, huā, huāā© := mem_interior.mp hx
    let t : Set V := {x}
    obtain āØb, hbā, hbā, hbā, hbāā© :=
      exists_subset_affine_independent_span_eq_top_of_open huā (singleton_subset_iff.mpr huā) (singleton_nonempty x)
        (affine_independent_of_subsingleton ā (coe : t ā V))
    rw [eq_top_iff, ā hbā, ā affine_span_convex_hull s]
    mono
    exact hbā.trans huā
    
  Ā· intro h
    obtain āØt, hts, h_tot, h_indā© := exists_affine_independent ā V s
    suffices (Interior (convexHull ā (range (coe : t ā V)))).Nonempty by
      rw [Subtype.range_coe_subtype, set_of_mem_eq] at this
      apply nonempty.mono _ this
      mono*
    have : Fintype t := fintypeOfFinDimAffineIndependent ā h_ind
    use Finset.centroid ā (Finset.univ : Finset t) (coe : t ā V)
    rw [h, ā @set_of_mem_eq V t, ā Subtype.range_coe_subtype] at h_tot
    let b : AffineBasis t ā V := āØcoe, h_ind, h_totā©
    rw [interior_convex_hull_aff_basis b]
    have htne : (Finset.univ : Finset t).Nonempty := by
      simpa [ā Finset.univ_nonempty_iff] using AffineSubspace.nonempty_of_affine_span_eq_top ā V V h_tot
    simp [ā Finset.centroid_def, ā
      b.coord_apply_combination_of_mem (Finset.mem_univ _)
        (Finset.sum_centroid_weights_eq_one_of_nonempty ā (Finset.univ : Finset t) htne),
      ā Finset.centroid_weights_apply, ā Nat.cast_pos, ā inv_pos, ā finset.card_pos.mpr htne]
    

theorem Convex.interior_nonempty_iff_affine_span_eq_top [FiniteDimensional ā V] {s : Set V} (hs : Convex ā s) :
    (Interior s).Nonempty ā affineSpan ā s = ā¤ := by
  rw [ā interior_convex_hull_nonempty_iff_aff_span_eq_top, hs.convex_hull_eq]

