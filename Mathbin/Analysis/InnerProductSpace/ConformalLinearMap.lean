import Mathbin.Analysis.NormedSpace.ConformalLinearMap 
import Mathbin.Analysis.InnerProductSpace.Basic

/-!
# Conformal maps between inner product spaces

In an inner product space, a map is conformal iff it preserves inner products up to a scalar factor.
-/


variable {E F : Type _} [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]

open LinearIsometry ContinuousLinearMap

open_locale RealInnerProductSpace

-- error in Analysis.InnerProductSpace.ConformalLinearMap: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_conformal_map_iff
(f' : «expr →L[ ] »(E, exprℝ(), F)) : «expr ↔ »(is_conformal_map f', «expr∃ , »((c : exprℝ()), «expr ∧ »(«expr < »(0, c), ∀
   u v : E, «expr = »(«expr⟪ , ⟫»(f' u, f' v), «expr * »((c : exprℝ()), «expr⟪ , ⟫»(u, v)))))) :=
begin
  split,
  { rintros ["⟨", ident c₁, ",", ident hc₁, ",", ident li, ",", ident h, "⟩"],
    refine [expr ⟨«expr * »(c₁, c₁), mul_self_pos hc₁, λ u v, _⟩],
    simp [] [] ["only"] ["[", expr h, ",", expr pi.smul_apply, ",", expr inner_map_map, ",", expr real_inner_smul_left, ",", expr real_inner_smul_right, ",", expr mul_assoc, "]"] [] [] },
  { rintros ["⟨", ident c₁, ",", ident hc₁, ",", ident huv, "⟩"],
    let [ident c] [] [":=", expr real.sqrt «expr ⁻¹»(c₁)],
    have [ident hc] [":", expr «expr ≠ »(c, 0)] [":=", expr λ
     w, by { simp [] [] ["only"] ["[", expr c, "]"] [] ["at", ident w]; exact [expr «expr $ »(real.sqrt_ne_zero'.mpr, inv_pos.mpr hc₁) w] }],
    let [ident f₁] [] [":=", expr «expr • »(c, f')],
    have [ident minor] [":", expr «expr = »((f₁ : E → F), «expr • »(c, f'))] [":=", expr rfl],
    have [ident minor'] [":", expr «expr = »((f' : E → F), «expr • »(«expr ⁻¹»(c), f₁))] [":=", expr by ext [] [] []; simp_rw ["[", expr minor, ",", expr pi.smul_apply, "]"] []; rw ["[", expr smul_smul, ",", expr inv_mul_cancel hc, ",", expr one_smul, "]"] []],
    refine [expr ⟨«expr ⁻¹»(c), inv_ne_zero hc, f₁.to_linear_map.isometry_of_inner (λ u v, _), minor'⟩],
    simp_rw ["[", expr to_linear_map_eq_coe, ",", expr continuous_linear_map.coe_coe, ",", expr minor, ",", expr pi.smul_apply, "]"] [],
    rw ["[", expr real_inner_smul_left, ",", expr real_inner_smul_right, ",", expr huv u v, ",", "<-", expr mul_assoc, ",", "<-", expr mul_assoc, ",", expr «expr $ »(real.mul_self_sqrt, «expr $ »(le_of_lt, inv_pos.mpr hc₁)), ",", expr «expr $ »(inv_mul_cancel, ne_of_gt hc₁), ",", expr one_mul, "]"] [] }
end

