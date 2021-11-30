import Mathbin.Data.Complex.IsROrC 
import Mathbin.Analysis.NormedSpace.OperatorNorm

/-!
# Normed spaces over R or C

This file is about results on normed spaces over the fields `ℝ` and `ℂ`.

## Main definitions

None.

## Main theorems

* `continuous_linear_map.op_norm_bound_of_ball_bound`: A bound on the norms of values of a linear
  map in a ball yields a bound on the operator norm.

## Notes

This file exists mainly to avoid importing `is_R_or_C` in the main normed space theory files.
-/


open Metric

@[simp]
theorem IsROrC.norm_coe_norm {𝕜 : Type _} [IsROrC 𝕜] {E : Type _} [NormedGroup E] {z : E} : ∥(∥z∥ : 𝕜)∥ = ∥z∥ :=
  by 
    unfoldCoes 
    simp only [norm_algebra_map_eq, RingHom.to_fun_eq_coe, norm_norm]

variable {𝕜 : Type _} [IsROrC 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E]

-- error in Analysis.NormedSpace.IsROrC: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Lemma to normalize a vector in a normed space `E` over either `ℂ` or `ℝ` to unit length. -/
@[simp]
theorem norm_smul_inv_norm
{x : E}
(hx : «expr ≠ »(x, 0)) : «expr = »(«expr∥ ∥»(«expr • »((«expr ⁻¹»(«expr∥ ∥»(x)) : 𝕜), x)), 1) :=
begin
  have [] [":", expr «expr ≠ »(«expr∥ ∥»(x), 0)] [":=", expr by simp [] [] [] ["[", expr hx, "]"] [] []],
  field_simp [] ["[", expr norm_smul, "]"] [] []
end

-- error in Analysis.NormedSpace.IsROrC: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Lemma to normalize a vector in a normed space `E` over either `ℂ` or `ℝ` to length `r`. -/
theorem norm_smul_inv_norm'
{r : exprℝ()}
(r_nonneg : «expr ≤ »(0, r))
{x : E}
(hx : «expr ≠ »(x, 0)) : «expr = »(«expr∥ ∥»(«expr • »((«expr * »(r, «expr ⁻¹»(«expr∥ ∥»(x))) : 𝕜), x)), r) :=
begin
  have [] [":", expr «expr ≠ »(«expr∥ ∥»(x), 0)] [":=", expr by simp [] [] [] ["[", expr hx, "]"] [] []],
  field_simp [] ["[", expr norm_smul, ",", expr is_R_or_C.norm_of_real, ",", expr is_R_or_C.norm_eq_abs, ",", expr r_nonneg, "]"] [] []
end

-- error in Analysis.NormedSpace.IsROrC: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem linear_map.bound_of_sphere_bound
{r : exprℝ()}
(r_pos : «expr < »(0, r))
(c : exprℝ())
(f : «expr →ₗ[ ] »(E, 𝕜, 𝕜))
(h : ∀ z «expr ∈ » sphere (0 : E) r, «expr ≤ »(«expr∥ ∥»(f z), c))
(z : E) : «expr ≤ »(«expr∥ ∥»(f z), «expr * »(«expr / »(c, r), «expr∥ ∥»(z))) :=
begin
  by_cases [expr z_zero, ":", expr «expr = »(z, 0)],
  { rw [expr z_zero] [],
    simp [] [] ["only"] ["[", expr linear_map.map_zero, ",", expr norm_zero, ",", expr mul_zero, "]"] [] [] },
  set [] [ident z₁] [] [":="] [expr «expr • »((«expr * »(r, «expr ⁻¹»(«expr∥ ∥»(z))) : 𝕜), z)] ["with", ident hz₁],
  have [ident norm_f_z₁] [":", expr «expr ≤ »(«expr∥ ∥»(f z₁), c)] [],
  { apply [expr h],
    rw [expr mem_sphere_zero_iff_norm] [],
    exact [expr norm_smul_inv_norm' r_pos.le z_zero] },
  have [ident r_ne_zero] [":", expr «expr ≠ »((r : 𝕜), 0)] [":=", expr (algebra_map exprℝ() 𝕜).map_ne_zero.mpr r_pos.ne.symm],
  have [ident eq] [":", expr «expr = »(f z, «expr * »(«expr / »(«expr∥ ∥»(z), r), f z₁))] [],
  { rw ["[", expr hz₁, ",", expr linear_map.map_smul, ",", expr smul_eq_mul, "]"] [],
    rw ["[", "<-", expr mul_assoc, ",", "<-", expr mul_assoc, ",", expr div_mul_cancel _ r_ne_zero, ",", expr mul_inv_cancel, ",", expr one_mul, "]"] [],
    simp [] [] ["only"] ["[", expr z_zero, ",", expr is_R_or_C.of_real_eq_zero, ",", expr norm_eq_zero, ",", expr ne.def, ",", expr not_false_iff, "]"] [] [] },
  rw ["[", expr eq, ",", expr normed_field.norm_mul, ",", expr normed_field.norm_div, ",", expr is_R_or_C.norm_coe_norm, ",", expr is_R_or_C.norm_of_nonneg r_pos.le, ",", expr div_mul_eq_mul_div, ",", expr div_mul_eq_mul_div, ",", expr mul_comm, "]"] [],
  apply [expr div_le_div _ _ r_pos rfl.ge],
  { exact [expr mul_nonneg ((norm_nonneg _).trans norm_f_z₁) (norm_nonneg z)] },
  apply [expr mul_le_mul norm_f_z₁ rfl.le (norm_nonneg z) ((norm_nonneg _).trans norm_f_z₁)]
end

theorem LinearMap.bound_of_ball_bound {r : ℝ} (r_pos : 0 < r) (c : ℝ) (f : E →ₗ[𝕜] 𝕜)
  (h : ∀ z _ : z ∈ closed_ball (0 : E) r, ∥f z∥ ≤ c) (z : E) : ∥f z∥ ≤ (c / r)*∥z∥ :=
  f.bound_of_sphere_bound r_pos c (fun z hz => h z hz.le) z

theorem ContinuousLinearMap.op_norm_bound_of_ball_bound {r : ℝ} (r_pos : 0 < r) (c : ℝ) (f : E →L[𝕜] 𝕜)
  (h : ∀ z _ : z ∈ closed_ball (0 : E) r, ∥f z∥ ≤ c) : ∥f∥ ≤ c / r :=
  by 
    apply ContinuousLinearMap.op_norm_le_bound
    ·
      apply div_nonneg _ r_pos.le 
      exact
        (norm_nonneg _).trans
          (h 0
            (by 
              simp only [norm_zero, mem_closed_ball, dist_zero_left, r_pos.le]))
    apply LinearMap.bound_of_ball_bound r_pos 
    exact fun z hz => h z hz

