import Mathbin.Algebra.Algebra.RestrictScalars 
import Mathbin.Data.Complex.IsROrC

/-!
# Extending a continuous `ℝ`-linear map to a continuous `𝕜`-linear map

In this file we provide a way to extend a continuous `ℝ`-linear map to a continuous `𝕜`-linear map
in a way that bounds the norm by the norm of the original map, when `𝕜` is either `ℝ` (the
extension is trivial) or `ℂ`. We formulate the extension uniformly, by assuming `is_R_or_C 𝕜`.

We motivate the form of the extension as follows. Note that `fc : F →ₗ[𝕜] 𝕜` is determined fully by
`Re fc`: for all `x : F`, `fc (I • x) = I * fc x`, so `Im (fc x) = -Re (fc (I • x))`. Therefore,
given an `fr : F →ₗ[ℝ] ℝ`, we define `fc x = fr x - fr (I • x) * I`.

## Main definitions

* `linear_map.extend_to_𝕜`
* `continuous_linear_map.extend_to_𝕜`

## Implementation details

For convenience, the main definitions above operate in terms of `restrict_scalars ℝ 𝕜 F`.
Alternate forms which operate on `[is_scalar_tower ℝ 𝕜 F]` instead are provided with a primed name.

-/


open IsROrC

variable {𝕜 : Type _} [IsROrC 𝕜] {F : Type _} [SemiNormedGroup F] [SemiNormedSpace 𝕜 F]

local notation "abs𝕜" => @IsROrC.abs 𝕜 _

-- error in Analysis.NormedSpace.Extend: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Extend `fr : F →ₗ[ℝ] ℝ` to `F →ₗ[𝕜] 𝕜` in a way that will also be continuous and have its norm
bounded by `∥fr∥` if `fr` is continuous. -/
noncomputable
def linear_map.extend_to_𝕜'
[module exprℝ() F]
[is_scalar_tower exprℝ() 𝕜 F]
(fr : «expr →ₗ[ ] »(F, exprℝ(), exprℝ())) : «expr →ₗ[ ] »(F, 𝕜, 𝕜) :=
begin
  let [ident fc] [":", expr F → 𝕜] [":=", expr λ
   x, «expr - »((fr x : 𝕜), «expr * »((I : 𝕜), fr «expr • »((I : 𝕜), x)))],
  have [ident add] [":", expr ∀ x y : F, «expr = »(fc «expr + »(x, y), «expr + »(fc x, fc y))] [],
  { assume [binders (x y)],
    simp [] [] ["only"] ["[", expr fc, "]"] [] [],
    unfold_coes [],
    simp [] [] ["only"] ["[", expr smul_add, ",", expr ring_hom.map_add, ",", expr ring_hom.to_fun_eq_coe, ",", expr linear_map.to_fun_eq_coe, ",", expr linear_map.map_add, "]"] [] [],
    rw [expr mul_add] [],
    abel [] [] [] },
  have [ident A] [":", expr ∀
   (c : exprℝ())
   (x : F), «expr = »((fr «expr • »((c : 𝕜), x) : 𝕜), «expr * »((c : 𝕜), (fr x : 𝕜)))] [],
  { assume [binders (c x)],
    rw ["[", "<-", expr of_real_mul, "]"] [],
    congr' [1] [],
    rw ["[", expr is_R_or_C.of_real_alg, ",", expr smul_assoc, ",", expr fr.map_smul, ",", expr algebra.id.smul_eq_mul, ",", expr one_smul, "]"] [] },
  have [ident smul_ℝ] [":", expr ∀
   (c : exprℝ())
   (x : F), «expr = »(fc «expr • »((c : 𝕜), x), «expr * »((c : 𝕜), fc x))] [],
  { assume [binders (c x)],
    simp [] [] ["only"] ["[", expr fc, ",", expr A, "]"] [] [],
    rw [expr A c x] [],
    rw ["[", expr smul_smul, ",", expr mul_comm I (c : 𝕜), ",", "<-", expr smul_smul, ",", expr A, ",", expr mul_sub, "]"] [],
    ring [] },
  have [ident smul_I] [":", expr ∀ x : F, «expr = »(fc «expr • »((I : 𝕜), x), «expr * »((I : 𝕜), fc x))] [],
  { assume [binders (x)],
    simp [] [] ["only"] ["[", expr fc, "]"] [] [],
    cases [expr @I_mul_I_ax 𝕜 _] ["with", ident h, ident h],
    { simp [] [] [] ["[", expr h, "]"] [] [] },
    rw ["[", expr mul_sub, ",", "<-", expr mul_assoc, ",", expr smul_smul, ",", expr h, "]"] [],
    simp [] [] ["only"] ["[", expr neg_mul_eq_neg_mul_symm, ",", expr linear_map.map_neg, ",", expr one_mul, ",", expr one_smul, ",", expr mul_neg_eq_neg_mul_symm, ",", expr of_real_neg, ",", expr neg_smul, ",", expr sub_neg_eq_add, ",", expr add_comm, "]"] [] [] },
  have [ident smul_𝕜] [":", expr ∀ (c : 𝕜) (x : F), «expr = »(fc «expr • »(c, x), «expr • »(c, fc x))] [],
  { assume [binders (c x)],
    rw ["[", "<-", expr re_add_im c, ",", expr add_smul, ",", expr add_smul, ",", expr add, ",", expr smul_ℝ, ",", "<-", expr smul_smul, ",", expr smul_ℝ, ",", expr smul_I, ",", "<-", expr mul_assoc, "]"] [],
    refl },
  exact [expr { to_fun := fc, map_add' := add, map_smul' := smul_𝕜 }]
end

theorem LinearMap.extend_to_𝕜'_apply [Module ℝ F] [IsScalarTower ℝ 𝕜 F] (fr : F →ₗ[ℝ] ℝ) (x : F) :
  fr.extend_to_𝕜' x = (fr x : 𝕜) - (I : 𝕜)*fr ((I : 𝕜) • x) :=
  rfl

-- error in Analysis.NormedSpace.Extend: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The norm of the extension is bounded by `∥fr∥`. -/
theorem norm_bound
[semi_normed_space exprℝ() F]
[is_scalar_tower exprℝ() 𝕜 F]
(fr : «expr →L[ ] »(F, exprℝ(), exprℝ()))
(x : F) : «expr ≤ »(«expr∥ ∥»((fr.to_linear_map.extend_to_𝕜' x : 𝕜)), «expr * »(«expr∥ ∥»(fr), «expr∥ ∥»(x))) :=
begin
  let [ident lm] [":", expr «expr →ₗ[ ] »(F, 𝕜, 𝕜)] [":=", expr fr.to_linear_map.extend_to_𝕜'],
  classical,
  by_cases [expr h, ":", expr «expr = »(lm x, 0)],
  { rw ["[", expr h, ",", expr norm_zero, "]"] [],
    apply [expr mul_nonneg]; exact [expr norm_nonneg _] },
  let [ident fx] [] [":=", expr «expr ⁻¹»(lm x)],
  let [ident t] [] [":=", expr «expr / »(fx, (exprabs𝕜() fx : 𝕜))],
  have [ident ht] [":", expr «expr = »(exprabs𝕜() t, 1)] [],
  by field_simp [] ["[", expr abs_of_real, ",", expr of_real_inv, ",", expr is_R_or_C.abs_inv, ",", expr is_R_or_C.abs_div, ",", expr is_R_or_C.abs_abs, ",", expr h, "]"] [] [],
  have [ident h1] [":", expr «expr = »((fr «expr • »(t, x) : 𝕜), lm «expr • »(t, x))] [],
  { apply [expr ext],
    { simp [] [] ["only"] ["[", expr lm, ",", expr of_real_re, ",", expr linear_map.extend_to_𝕜'_apply, ",", expr mul_re, ",", expr I_re, ",", expr of_real_im, ",", expr zero_mul, ",", expr add_monoid_hom.map_sub, ",", expr sub_zero, ",", expr mul_zero, "]"] [] [],
      refl },
    { symmetry,
      calc
        «expr = »(im (lm «expr • »(t, x)), im «expr * »(t, lm x)) : by rw ["[", expr lm.map_smul, ",", expr smul_eq_mul, "]"] []
        «expr = »(..., im «expr * »(«expr / »(«expr ⁻¹»(lm x), exprabs𝕜() «expr ⁻¹»(lm x)), lm x)) : rfl
        «expr = »(..., im «expr / »(1, (exprabs𝕜() «expr ⁻¹»(lm x) : 𝕜))) : by rw ["[", expr div_mul_eq_mul_div, ",", expr inv_mul_cancel h, "]"] []
        «expr = »(..., 0) : by rw ["[", "<-", expr of_real_one, ",", "<-", expr of_real_div, ",", expr of_real_im, "]"] []
        «expr = »(..., im (fr «expr • »(t, x) : 𝕜)) : by rw ["[", expr of_real_im, "]"] [] } },
  calc
    «expr = »(«expr∥ ∥»(lm x), «expr * »(exprabs𝕜() t, «expr∥ ∥»(lm x))) : by rw ["[", expr ht, ",", expr one_mul, "]"] []
    «expr = »(..., «expr∥ ∥»(«expr * »(t, lm x))) : by rw ["[", "<-", expr norm_eq_abs, ",", expr normed_field.norm_mul, "]"] []
    «expr = »(..., «expr∥ ∥»(lm «expr • »(t, x))) : by rw ["[", "<-", expr smul_eq_mul, ",", expr lm.map_smul, "]"] []
    «expr = »(..., «expr∥ ∥»((fr «expr • »(t, x) : 𝕜))) : by rw [expr h1] []
    «expr = »(..., «expr∥ ∥»(fr «expr • »(t, x))) : by rw ["[", expr norm_eq_abs, ",", expr abs_of_real, ",", expr norm_eq_abs, ",", expr abs_to_real, "]"] []
    «expr ≤ »(..., «expr * »(«expr∥ ∥»(fr), «expr∥ ∥»(«expr • »(t, x)))) : continuous_linear_map.le_op_norm _ _
    «expr = »(..., «expr * »(«expr∥ ∥»(fr), «expr * »(«expr∥ ∥»(t), «expr∥ ∥»(x)))) : by rw [expr norm_smul] []
    «expr ≤ »(..., «expr * »(«expr∥ ∥»(fr), «expr∥ ∥»(x))) : by rw ["[", expr norm_eq_abs, ",", expr ht, ",", expr one_mul, "]"] []
end

/-- Extend `fr : F →L[ℝ] ℝ` to `F →L[𝕜] 𝕜`. -/
noncomputable def ContinuousLinearMap.extendTo𝕜' [SemiNormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] (fr : F →L[ℝ] ℝ) :
  F →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous _ ∥fr∥ (norm_bound _)

theorem ContinuousLinearMap.extend_to_𝕜'_apply [SemiNormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] (fr : F →L[ℝ] ℝ) (x : F) :
  fr.extend_to_𝕜' x = (fr x : 𝕜) - (I : 𝕜)*fr ((I : 𝕜) • x) :=
  rfl

/-- Extend `fr : restrict_scalars ℝ 𝕜 F →ₗ[ℝ] ℝ` to `F →ₗ[𝕜] 𝕜`. -/
noncomputable def LinearMap.extendTo𝕜 (fr : RestrictScalars ℝ 𝕜 F →ₗ[ℝ] ℝ) : F →ₗ[𝕜] 𝕜 :=
  fr.extend_to_𝕜'

theorem LinearMap.extend_to_𝕜_apply (fr : RestrictScalars ℝ 𝕜 F →ₗ[ℝ] ℝ) (x : F) :
  fr.extend_to_𝕜 x = (fr x : 𝕜) - (I : 𝕜)*fr ((I : 𝕜) • x) :=
  rfl

/-- Extend `fr : restrict_scalars ℝ 𝕜 F →L[ℝ] ℝ` to `F →L[𝕜] 𝕜`. -/
noncomputable def ContinuousLinearMap.extendTo𝕜 (fr : RestrictScalars ℝ 𝕜 F →L[ℝ] ℝ) : F →L[𝕜] 𝕜 :=
  fr.extend_to_𝕜'

theorem ContinuousLinearMap.extend_to_𝕜_apply (fr : RestrictScalars ℝ 𝕜 F →L[ℝ] ℝ) (x : F) :
  fr.extend_to_𝕜 x = (fr x : 𝕜) - (I : 𝕜)*fr ((I : 𝕜) • x) :=
  rfl

