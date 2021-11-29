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

variable(b : AffineBasis ι 𝕜 P)

@[continuity]
theorem continuous_barycentric_coord (i : ι) : Continuous (b.coord i) :=
  AffineMap.continuous_of_finite_dimensional _

attribute [local instance] FiniteDimensional.complete

theorem is_open_map_barycentric_coord [Nontrivial ι] (i : ι) : IsOpenMap (b.coord i) :=
  open_mapping_affine (continuous_barycentric_coord b i) (b.surjective_coord i)

end Barycentric

open Set

-- error in Analysis.NormedSpace.AddTorsorBases: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a finite-dimensional normed real vector space, the interior of the convex hull of an
affine basis is the set of points whose barycentric coordinates are strictly positive with respect
to this basis.

TODO Restate this result for affine spaces (instead of vector spaces) once the definition of
convexity is generalised to this setting. -/
theorem interior_convex_hull_aff_basis
{ι E : Type*}
[fintype ι]
[normed_group E]
[normed_space exprℝ() E]
(b : affine_basis ι exprℝ() E) : «expr = »(interior (convex_hull exprℝ() (range b.points)), {x | ∀
 i, «expr < »(0, b.coord i x)}) :=
begin
  cases [expr subsingleton_or_nontrivial ι] ["with", ident h, ident h],
  { haveI [] [] [":=", expr h],
    suffices [] [":", expr «expr = »(range b.points, univ)],
    { simp [] [] [] ["[", expr this, "]"] [] [] },
    refine [expr affine_subspace.eq_univ_of_subsingleton_span_eq_top _ b.tot],
    rw ["<-", expr image_univ] [],
    exact [expr subsingleton.image subsingleton_of_subsingleton b.points] },
  { haveI [] [":", expr finite_dimensional exprℝ() E] [],
    { classical,
      obtain ["⟨", ident i, "⟩", ":=", expr (infer_instance : nonempty ι)],
      exact [expr finite_dimensional.of_fintype_basis (b.basis_of i)] },
    have [] [":", expr «expr = »(convex_hull exprℝ() (range b.points), «expr⋂ , »((i), «expr ⁻¹' »(b.coord i, Ici 0)))] [],
    { rw [expr convex_hull_affine_basis_eq_nonneg_barycentric b] [],
      ext [] [] [],
      simp [] [] [] [] [] [] },
    ext [] [] [],
    simp [] [] ["only"] ["[", expr this, ",", expr interior_Inter_of_fintype, ",", "<-", expr is_open_map.preimage_interior_eq_interior_preimage (continuous_barycentric_coord b _) (is_open_map_barycentric_coord b _), ",", expr interior_Ici, ",", expr mem_Inter, ",", expr mem_set_of_eq, ",", expr mem_Ioi, ",", expr mem_preimage, "]"] [] [] }
end

variable{V P : Type _}[NormedGroup V][NormedSpace ℝ V][MetricSpace P][NormedAddTorsor V P]

include V

open AffineMap

-- error in Analysis.NormedSpace.AddTorsorBases: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Given a set `s` of affine-independent points belonging to an open set `u`, we may extend `s` to
an affine basis, all of whose elements belong to `u`. -/
theorem exists_subset_affine_independent_span_eq_top_of_open
{s u : set P}
(hu : is_open u)
(hsu : «expr ⊆ »(s, u))
(hne : s.nonempty)
(h : affine_independent exprℝ() (coe : s → P)) : «expr∃ , »((t : set P), «expr ∧ »(«expr ⊆ »(s, t), «expr ∧ »(«expr ⊆ »(t, u), «expr ∧ »(affine_independent exprℝ() (coe : t → P), «expr = »(affine_span exprℝ() t, «expr⊤»()))))) :=
begin
  obtain ["⟨", ident q, ",", ident hq, "⟩", ":=", expr hne],
  obtain ["⟨", ident ε, ",", ident hε, ",", ident hεu, "⟩", ":=", expr metric.is_open_iff.mp hu q (hsu hq)],
  obtain ["⟨", ident t, ",", ident ht₁, ",", ident ht₂, ",", ident ht₃, "⟩", ":=", expr exists_subset_affine_independent_affine_span_eq_top h],
  let [ident f] [":", expr P → P] [":=", expr λ y, line_map q y «expr / »(«expr / »(ε, 2), dist y q)],
  have [ident hf] [":", expr ∀ y, «expr ∈ »(f y, u)] [],
  { intros [ident y],
    apply [expr hεu],
    simp [] [] ["only"] ["[", expr metric.mem_ball, ",", expr f, ",", expr line_map_apply, ",", expr dist_vadd_left, ",", expr norm_smul, ",", expr real.norm_eq_abs, ",", expr dist_eq_norm_vsub V y q, "]"] [] [],
    cases [expr eq_or_ne «expr∥ ∥»(«expr -ᵥ »(y, q)) 0] ["with", ident hyq, ident hyq],
    { rwa ["[", expr hyq, ",", expr mul_zero, "]"] [] },
    rw ["[", "<-", expr norm_pos_iff, ",", expr norm_norm, "]"] ["at", ident hyq],
    calc
      «expr = »(«expr * »(abs «expr / »(«expr / »(ε, 2), «expr∥ ∥»(«expr -ᵥ »(y, q))), «expr∥ ∥»(«expr -ᵥ »(y, q))), «expr * »(«expr / »(«expr / »(ε, 2), «expr∥ ∥»(«expr -ᵥ »(y, q))), «expr∥ ∥»(«expr -ᵥ »(y, q)))) : by rw ["[", expr abs_div, ",", expr abs_of_pos (half_pos hε), ",", expr abs_of_pos hyq, "]"] []
      «expr = »(..., «expr / »(ε, 2)) : div_mul_cancel _ (ne_of_gt hyq)
      «expr < »(..., ε) : half_lt_self hε },
  have [ident hεyq] [":", expr ∀ y «expr ∉ » s, «expr ≠ »(«expr / »(«expr / »(ε, 2), dist y q), 0)] [],
  { simp [] [] ["only"] ["[", expr ne.def, ",", expr div_eq_zero_iff, ",", expr or_false, ",", expr dist_eq_zero, ",", expr bit0_eq_zero, ",", expr one_ne_zero, ",", expr not_or_distrib, ",", expr ne_of_gt hε, ",", expr true_and, ",", expr not_false_iff, "]"] [] [],
    finish [] [] },
  classical,
  let [ident w] [":", expr t → units exprℝ()] [":=", expr λ
   p, if hp : «expr ∈ »((p : P), s) then 1 else units.mk0 _ (hεyq «expr↑ »(p) hp)],
  refine [expr ⟨set.range (λ p : t, line_map q p (w p : exprℝ())), _, _, _, _⟩],
  { intros [ident p, ident hp],
    use [expr ⟨p, ht₁ hp⟩],
    simp [] [] [] ["[", expr w, ",", expr hp, "]"] [] [] },
  { intros [ident y, ident hy],
    simp [] [] ["only"] ["[", expr set.mem_range, ",", expr set_coe.exists, ",", expr subtype.coe_mk, "]"] [] ["at", ident hy],
    obtain ["⟨", ident p, ",", ident hp, ",", ident hyq, "⟩", ":=", expr hy],
    by_cases [expr hps, ":", expr «expr ∈ »(p, s)]; simp [] [] ["only"] ["[", expr w, ",", expr hps, ",", expr line_map_apply_one, ",", expr units.coe_mk0, ",", expr dif_neg, ",", expr dif_pos, ",", expr not_false_iff, ",", expr units.coe_one, ",", expr subtype.coe_mk, "]"] [] ["at", ident hyq]; rw ["<-", expr hyq] []; [exact [expr hsu hps], exact [expr hf p]] },
  { exact [expr (ht₂.units_line_map ⟨q, ht₁ hq⟩ w).range] },
  { rw ["[", expr affine_span_eq_affine_span_line_map_units (ht₁ hq) w, ",", expr ht₃, "]"] [] }
end

-- error in Analysis.NormedSpace.AddTorsorBases: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem interior_convex_hull_nonempty_iff_aff_span_eq_top
[finite_dimensional exprℝ() V]
{s : set V} : «expr ↔ »((interior (convex_hull exprℝ() s)).nonempty, «expr = »(affine_span exprℝ() s, «expr⊤»())) :=
begin
  split,
  { rintros ["⟨", ident x, ",", ident hx, "⟩"],
    obtain ["⟨", ident u, ",", ident hu₁, ",", ident hu₂, ",", ident hu₃, "⟩", ":=", expr mem_interior.mp hx],
    let [ident t] [":", expr set V] [":=", expr {x}],
    obtain ["⟨", ident b, ",", ident hb₁, ",", ident hb₂, ",", ident hb₃, ",", ident hb₄, "⟩", ":=", expr exists_subset_affine_independent_span_eq_top_of_open hu₂ (singleton_subset_iff.mpr hu₃) (singleton_nonempty x) (affine_independent_of_subsingleton exprℝ() (coe : t → V))],
    rw ["[", expr eq_top_iff, ",", "<-", expr hb₄, ",", "<-", expr affine_span_convex_hull s, "]"] [],
    mono [] [] [] [],
    exact [expr hb₂.trans hu₁] },
  { intros [ident h],
    obtain ["⟨", ident t, ",", ident hts, ",", ident h_tot, ",", ident h_ind, "⟩", ":=", expr exists_affine_independent exprℝ() V s],
    suffices [] [":", expr (interior (convex_hull exprℝ() (range (coe : t → V)))).nonempty],
    { rw ["[", expr subtype.range_coe_subtype, ",", expr set_of_mem_eq, "]"] ["at", ident this],
      apply [expr nonempty.mono _ this],
      mono ["*"] [] [] [] },
    haveI [] [":", expr fintype t] [":=", expr fintype_of_fin_dim_affine_independent exprℝ() h_ind],
    use [expr finset.centroid exprℝ() (finset.univ : finset t) (coe : t → V)],
    rw ["[", expr h, ",", "<-", expr @set_of_mem_eq V t, ",", "<-", expr subtype.range_coe_subtype, "]"] ["at", ident h_tot],
    let [ident b] [":", expr affine_basis t exprℝ() V] [":=", expr ⟨coe, h_ind, h_tot⟩],
    rw [expr interior_convex_hull_aff_basis b] [],
    have [ident htne] [":", expr (finset.univ : finset t).nonempty] [],
    { simpa [] [] [] ["[", expr finset.univ_nonempty_iff, "]"] [] ["using", expr affine_subspace.nonempty_of_affine_span_eq_top exprℝ() V V h_tot] },
    simp [] [] [] ["[", expr finset.centroid_def, ",", expr b.coord_apply_combination_of_mem (finset.mem_univ _) (finset.sum_centroid_weights_eq_one_of_nonempty exprℝ() (finset.univ : finset t) htne), ",", expr finset.centroid_weights_apply, ",", expr nat.cast_pos, ",", expr inv_pos, ",", expr finset.card_pos.mpr htne, "]"] [] [] }
end

