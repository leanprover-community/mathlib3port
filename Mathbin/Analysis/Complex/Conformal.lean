import Mathbin.Analysis.Complex.Isometry 
import Mathbin.Analysis.NormedSpace.ConformalLinearMap

/-!
# Conformal maps between complex vector spaces

We prove the sufficient and necessary conditions for a real-linear map between complex vector spaces
to be conformal.

## Main results

* `is_conformal_map_complex_linear`: a nonzero complex linear map into an arbitrary complex
                                     normed space is conformal.
* `is_conformal_map_complex_linear_conj`: the composition of a nonzero complex linear map with
                                          `conj` is complex linear.
* `is_conformal_map_iff_is_complex_or_conj_linear`: a real linear map between the complex
                                                            plane is conformal iff it's complex
                                                            linear or the composition of
                                                            some complex linear map and `conj`.

## Warning

Antiholomorphic functions such as the complex conjugate are considered as conformal functions in
this file.
-/


noncomputable theory

open Complex ContinuousLinearMap

open_locale ComplexConjugate

theorem is_conformal_map_conj : IsConformalMap (conj_lie : ℂ →L[ℝ] ℂ) :=
  conj_lie.toLinearIsometry.IsConformalMap

section ConformalIntoComplexNormed

variable{E :
    Type _}[NormedGroup E][NormedSpace ℝ E][NormedSpace ℂ E][IsScalarTower ℝ ℂ E]{z : ℂ}{g : ℂ →L[ℝ] E}{f : ℂ → E}

-- error in Analysis.Complex.Conformal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_conformal_map_complex_linear
{map : «expr →L[ ] »(exprℂ(), exprℂ(), E)}
(nonzero : «expr ≠ »(map, 0)) : is_conformal_map (map.restrict_scalars exprℝ()) :=
begin
  have [ident minor₁] [":", expr «expr ≠ »(«expr∥ ∥»(map 1), 0)] [],
  { simpa [] [] [] ["[", expr ext_ring_iff, "]"] [] ["using", expr nonzero] },
  refine [expr ⟨«expr∥ ∥»(map 1), minor₁, ⟨«expr • »(«expr ⁻¹»(«expr∥ ∥»(map 1)), map), _⟩, _⟩],
  { intros [ident x],
    simp [] [] ["only"] ["[", expr linear_map.smul_apply, "]"] [] [],
    have [] [":", expr «expr = »(x, «expr • »(x, 1))] [":=", expr by rw ["[", expr smul_eq_mul, ",", expr mul_one, "]"] []],
    nth_rewrite [0] ["[", expr this, "]"] [],
    rw ["[", expr _root_.coe_coe map, ",", expr linear_map.coe_coe_is_scalar_tower, "]"] [],
    simp [] [] ["only"] ["[", expr map.coe_coe, ",", expr map.map_smul, ",", expr norm_smul, ",", expr normed_field.norm_inv, ",", expr norm_norm, "]"] [] [],
    field_simp [] ["[", expr minor₁, "]"] [] [] },
  { ext1 [] [],
    rw ["[", "<-", expr linear_isometry.coe_to_linear_map, "]"] [],
    simp [] [] [] ["[", expr minor₁, "]"] [] [] }
end

theorem is_conformal_map_complex_linear_conj {map : ℂ →L[ℂ] E} (nonzero : map ≠ 0) :
  IsConformalMap ((map.restrict_scalars ℝ).comp (conj_cle : ℂ →L[ℝ] ℂ)) :=
  (is_conformal_map_complex_linear nonzero).comp is_conformal_map_conj

end ConformalIntoComplexNormed

section ConformalIntoComplexPlane

open ContinuousLinearMap

variable{f : ℂ → ℂ}{z : ℂ}{g : ℂ →L[ℝ] ℂ}

theorem IsConformalMap.is_complex_or_conj_linear (h : IsConformalMap g) :
  (∃ map : ℂ →L[ℂ] ℂ, map.restrict_scalars ℝ = g) ∨
    ∃ map : ℂ →L[ℂ] ℂ, map.restrict_scalars ℝ = g ∘L «expr↑ » conj_cle :=
  by 
    rcases h with ⟨c, hc, li, hg⟩
    rcases linear_isometry_complex (li.to_linear_isometry_equiv rfl) with ⟨a, ha⟩
    let rot := c • (a : ℂ) • ContinuousLinearMap.id ℂ ℂ 
    cases ha
    ·
      refine' Or.intro_left _ ⟨rot, _⟩
      ext1 
      simp only [coe_restrict_scalars', hg, ←li.coe_to_linear_isometry_equiv, ha, Pi.smul_apply,
        ContinuousLinearMap.smul_apply, rotation_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    ·
      refine' Or.intro_rightₓ _ ⟨rot, _⟩
      ext1 
      rw [ContinuousLinearMap.coe_comp', hg, ←li.coe_to_linear_isometry_equiv, ha]
      simp only [coe_restrict_scalars', Function.comp_app, Pi.smul_apply, LinearIsometryEquiv.coe_trans, conj_lie_apply,
        rotation_apply, ContinuousLinearEquiv.coe_apply, conj_cle_apply]
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, conj_conj]

-- error in Analysis.Complex.Conformal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A real continuous linear map on the complex plane is conformal if and only if the map or its
    conjugate is complex linear, and the map is nonvanishing. -/
theorem is_conformal_map_iff_is_complex_or_conj_linear : «expr ↔ »(is_conformal_map g, «expr ∧ »(«expr ∨ »(«expr∃ , »((map : «expr →L[ ] »(exprℂ(), exprℂ(), exprℂ())), «expr = »(map.restrict_scalars exprℝ(), g)), «expr∃ , »((map : «expr →L[ ] »(exprℂ(), exprℂ(), exprℂ())), «expr = »(map.restrict_scalars exprℝ(), «expr ∘L »(g, «expr↑ »(conj_cle))))), «expr ≠ »(g, 0))) :=
begin
  split,
  { exact [expr λ h, ⟨h.is_complex_or_conj_linear, h.ne_zero⟩] },
  { rintros ["⟨", "⟨", ident map, ",", ident rfl, "⟩", "|", "⟨", ident map, ",", ident hmap, "⟩", ",", ident h₂, "⟩"],
    { refine [expr is_conformal_map_complex_linear _],
      contrapose ["!"] [ident h₂, "with", ident w],
      simp [] [] [] ["[", expr w, "]"] [] [] },
    { have [ident minor₁] [":", expr «expr = »(g, «expr ∘L »(map.restrict_scalars exprℝ(), «expr↑ »(conj_cle)))] [],
      { ext1 [] [],
        simp [] [] [] ["[", expr hmap, "]"] [] [] },
      rw [expr minor₁] ["at", "⊢", ident h₂],
      refine [expr is_conformal_map_complex_linear_conj _],
      contrapose ["!"] [ident h₂, "with", ident w],
      simp [] [] [] ["[", expr w, "]"] [] [] } }
end

end ConformalIntoComplexPlane

