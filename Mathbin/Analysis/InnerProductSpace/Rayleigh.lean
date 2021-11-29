import Mathbin.Analysis.InnerProductSpace.Calculus 
import Mathbin.Analysis.InnerProductSpace.Dual 
import Mathbin.Analysis.Calculus.LagrangeMultipliers 
import Mathbin.LinearAlgebra.Eigenspace

/-!
# The Rayleigh quotient

The Rayleigh quotient of a self-adjoint operator `T` on an inner product space `E` is the function
`λ x, ⟪T x, x⟫ / ∥x∥ ^ 2`.

The main results of this file are `is_self_adjoint.has_eigenvector_of_is_max_on` and
`is_self_adjoint.has_eigenvector_of_is_min_on`, which state that if `E` is complete, and if the
Rayleigh quotient attains its global maximum/minimum over some sphere at the point `x₀`, then `x₀`
is an eigenvector of `T`, and the `supr`/`infi` of `λ x, ⟪T x, x⟫ / ∥x∥ ^ 2` is the corresponding
eigenvalue.

The corollaries `is_self_adjoint.has_eigenvalue_supr_of_finite_dimensional` and
`is_self_adjoint.has_eigenvalue_supr_of_finite_dimensional` state that if `E` is finite-dimensional
and nontrivial, then `T` has some (nonzero) eigenvectors with eigenvalue the `supr`/`infi` of
`λ x, ⟪T x, x⟫ / ∥x∥ ^ 2`.

## TODO

A slightly more elaborate corollary is that if `E` is complete and `T` is a compact operator, then
`T` has some (nonzero) eigenvector with eigenvalue either `⨆ x, ⟪T x, x⟫ / ∥x∥ ^ 2` or
`⨅ x, ⟪T x, x⟫ / ∥x∥ ^ 2` (not necessarily both).

-/


variable {𝕜 : Type _} [IsROrC 𝕜]

variable {E : Type _} [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

open_locale Nnreal

open Module.End Metric

namespace ContinuousLinearMap

variable (T : E →L[𝕜] E)

local notation "rayleigh_quotient" => fun x : E => T.re_apply_inner_self x / (∥(x : E)∥^2)

-- error in Analysis.InnerProductSpace.Rayleigh: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem rayleigh_smul
(x : E)
{c : 𝕜}
(hc : «expr ≠ »(c, 0)) : «expr = »(exprrayleigh_quotient() «expr • »(c, x), exprrayleigh_quotient() x) :=
begin
  by_cases [expr hx, ":", expr «expr = »(x, 0)],
  { simp [] [] [] ["[", expr hx, "]"] [] [] },
  have [] [":", expr «expr ≠ »(«expr∥ ∥»(c), 0)] [":=", expr by simp [] [] [] ["[", expr hc, "]"] [] []],
  have [] [":", expr «expr ≠ »(«expr∥ ∥»(x), 0)] [":=", expr by simp [] [] [] ["[", expr hx, "]"] [] []],
  field_simp [] ["[", expr norm_smul, ",", expr T.re_apply_inner_self_smul, "]"] [] [],
  ring []
end

-- error in Analysis.InnerProductSpace.Rayleigh: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem image_rayleigh_eq_image_rayleigh_sphere
{r : exprℝ()}
(hr : «expr < »(0, r)) : «expr = »(«expr '' »(exprrayleigh_quotient(), «expr ᶜ»({0})), «expr '' »(exprrayleigh_quotient(), sphere 0 r)) :=
begin
  ext [] [ident a] [],
  split,
  { rintros ["⟨", ident x, ",", "(", ident hx, ":", expr «expr ≠ »(x, 0), ")", ",", ident hxT, "⟩"],
    have [] [":", expr «expr ≠ »(«expr∥ ∥»(x), 0)] [":=", expr by simp [] [] [] ["[", expr hx, "]"] [] []],
    let [ident c] [":", expr 𝕜] [":=", expr «expr * »(«expr↑ »(«expr ⁻¹»(«expr∥ ∥»(x))), r)],
    have [] [":", expr «expr ≠ »(c, 0)] [":=", expr by simp [] [] [] ["[", expr c, ",", expr hx, ",", expr hr.ne', "]"] [] []],
    refine [expr ⟨«expr • »(c, x), _, _⟩],
    { field_simp [] ["[", expr norm_smul, ",", expr is_R_or_C.norm_eq_abs, ",", expr abs_of_nonneg hr.le, "]"] [] [] },
    { rw [expr T.rayleigh_smul x this] [],
      exact [expr hxT] } },
  { rintros ["⟨", ident x, ",", ident hx, ",", ident hxT, "⟩"],
    exact [expr ⟨x, nonzero_of_mem_sphere hr ⟨x, hx⟩, hxT⟩] }
end

theorem supr_rayleigh_eq_supr_rayleigh_sphere {r : ℝ} (hr : 0 < r) :
  (⨆x : { x : E // x ≠ 0 }, rayleigh_quotient x) = ⨆x : sphere (0 : E) r, rayleigh_quotient x :=
  show (⨆x : «expr ᶜ» ({0} : Set E), rayleigh_quotient x) = _ by 
    simp only [@csupr_set _ _ _ _ rayleigh_quotient, T.image_rayleigh_eq_image_rayleigh_sphere hr]

theorem infi_rayleigh_eq_infi_rayleigh_sphere {r : ℝ} (hr : 0 < r) :
  (⨅x : { x : E // x ≠ 0 }, rayleigh_quotient x) = ⨅x : sphere (0 : E) r, rayleigh_quotient x :=
  show (⨅x : «expr ᶜ» ({0} : Set E), rayleigh_quotient x) = _ by 
    simp only [@cinfi_set _ _ _ _ rayleigh_quotient, T.image_rayleigh_eq_image_rayleigh_sphere hr]

end ContinuousLinearMap

namespace IsSelfAdjoint

section Real

variable {F : Type _} [InnerProductSpace ℝ F]

theorem has_strict_fderiv_at_re_apply_inner_self {T : F →L[ℝ] F} (hT : IsSelfAdjoint (T : F →ₗ[ℝ] F)) (x₀ : F) :
  HasStrictFderivAt T.re_apply_inner_self (bit0 (innerRight (T x₀))) x₀ :=
  by 
    convert T.has_strict_fderiv_at.inner (has_strict_fderiv_at_id x₀)
    ext y 
    simp [bit0, hT.apply_clm x₀ y, real_inner_comm x₀]

variable [CompleteSpace F] {T : F →L[ℝ] F}

local notation "rayleigh_quotient" => fun x : F => T.re_apply_inner_self x / (∥(x : F)∥^2)

-- error in Analysis.InnerProductSpace.Rayleigh: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem linearly_dependent_of_is_local_extr_on
(hT : is_self_adjoint (T : «expr →ₗ[ ] »(F, exprℝ(), F)))
{x₀ : F}
(hextr : is_local_extr_on T.re_apply_inner_self (sphere (0 : F) «expr∥ ∥»(x₀)) x₀) : «expr∃ , »((a
  b : exprℝ()), «expr ∧ »(«expr ≠ »((a, b), 0), «expr = »(«expr + »(«expr • »(a, x₀), «expr • »(b, T x₀)), 0))) :=
begin
  have [ident H] [":", expr is_local_extr_on T.re_apply_inner_self {x : F | «expr = »(«expr ^ »(«expr∥ ∥»(x), 2), «expr ^ »(«expr∥ ∥»(x₀), 2))} x₀] [],
  { convert [] [expr hextr] [],
    ext [] [ident x] [],
    simp [] [] [] ["[", expr dist_eq_norm, "]"] [] [] },
  obtain ["⟨", ident a, ",", ident b, ",", ident h₁, ",", ident h₂, "⟩", ":=", expr is_local_extr_on.exists_multipliers_of_has_strict_fderiv_at_1d H (has_strict_fderiv_at_norm_sq x₀) (hT.has_strict_fderiv_at_re_apply_inner_self x₀)],
  refine [expr ⟨a, b, h₁, _⟩],
  apply [expr (inner_product_space.to_dual_map exprℝ() F).injective],
  simp [] [] ["only"] ["[", expr linear_isometry.map_add, ",", expr linear_isometry.map_smul, ",", expr linear_isometry.map_zero, "]"] [] [],
  change [expr «expr = »(«expr + »(«expr • »(a, inner_right x₀), «expr • »(b, inner_right (T x₀))), 0)] [] [],
  apply [expr smul_right_injective «expr →L[ ] »(F, exprℝ(), exprℝ()) (two_ne_zero : «expr ≠ »((2 : exprℝ()), 0))],
  simpa [] [] ["only"] ["[", expr bit0, ",", expr add_smul, ",", expr smul_add, ",", expr one_smul, ",", expr add_zero, "]"] [] ["using", expr h₂]
end

-- error in Analysis.InnerProductSpace.Rayleigh: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eq_smul_self_of_is_local_extr_on_real
(hT : is_self_adjoint (T : «expr →ₗ[ ] »(F, exprℝ(), F)))
{x₀ : F}
(hextr : is_local_extr_on T.re_apply_inner_self (sphere (0 : F) «expr∥ ∥»(x₀)) x₀) : «expr = »(T x₀, «expr • »(exprrayleigh_quotient() x₀, x₀)) :=
begin
  obtain ["⟨", ident a, ",", ident b, ",", ident h₁, ",", ident h₂, "⟩", ":=", expr hT.linearly_dependent_of_is_local_extr_on hextr],
  by_cases [expr hx₀, ":", expr «expr = »(x₀, 0)],
  { simp [] [] [] ["[", expr hx₀, "]"] [] [] },
  by_cases [expr hb, ":", expr «expr = »(b, 0)],
  { have [] [":", expr «expr ≠ »(a, 0)] [":=", expr by simpa [] [] [] ["[", expr hb, "]"] [] ["using", expr h₁]],
    refine [expr absurd _ hx₀],
    apply [expr smul_right_injective F this],
    simpa [] [] [] ["[", expr hb, "]"] [] ["using", expr h₂] },
  let [ident c] [":", expr exprℝ()] [":=", expr «expr * »(«expr- »(«expr ⁻¹»(b)), a)],
  have [ident hc] [":", expr «expr = »(T x₀, «expr • »(c, x₀))] [],
  { have [] [":", expr «expr = »(«expr * »(b, «expr * »(«expr ⁻¹»(b), a)), a)] [":=", expr by field_simp [] ["[", expr mul_comm, "]"] [] []],
    apply [expr smul_right_injective F hb],
    simp [] [] [] ["[", expr c, ",", "<-", expr neg_eq_of_add_eq_zero h₂, ",", "<-", expr mul_smul, ",", expr this, "]"] [] [] },
  convert [] [expr hc] [],
  have [] [":", expr «expr ≠ »(«expr∥ ∥»(x₀), 0)] [":=", expr by simp [] [] [] ["[", expr hx₀, "]"] [] []],
  field_simp [] [] [] [],
  simpa [] [] [] ["[", expr inner_smul_left, ",", expr real_inner_self_eq_norm_mul_norm, ",", expr sq, "]"] [] ["using", expr congr_arg (λ
    x, «expr⟪ , ⟫_ℝ»(x, x₀)) hc]
end

end Real

section CompleteSpace

variable [CompleteSpace E] {T : E →L[𝕜] E}

local notation "rayleigh_quotient" => fun x : E => T.re_apply_inner_self x / (∥(x : E)∥^2)

-- error in Analysis.InnerProductSpace.Rayleigh: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eq_smul_self_of_is_local_extr_on
(hT : is_self_adjoint (T : «expr →ₗ[ ] »(E, 𝕜, E)))
{x₀ : E}
(hextr : is_local_extr_on T.re_apply_inner_self (sphere (0 : E) «expr∥ ∥»(x₀)) x₀) : «expr = »(T x₀, «expr • »((«expr↑ »(exprrayleigh_quotient() x₀) : 𝕜), x₀)) :=
begin
  letI [] [] [":=", expr inner_product_space.is_R_or_C_to_real 𝕜 E],
  letI [] [":", expr is_scalar_tower exprℝ() 𝕜 E] [":=", expr restrict_scalars.is_scalar_tower _ _ _],
  let [ident S] [":", expr «expr →L[ ] »(E, exprℝ(), E)] [":=", expr @continuous_linear_map.restrict_scalars 𝕜 E E _ _ _ _ _ _ _ exprℝ() _ _ _ _ T],
  have [ident hSA] [":", expr is_self_adjoint (S : «expr →ₗ[ ] »(E, exprℝ(), E))] [":=", expr λ
   x y, by { have [] [] [":=", expr hT x y],
     simp [] [] ["only"] ["[", expr continuous_linear_map.coe_coe, "]"] [] ["at", ident this],
     simp [] [] ["only"] ["[", expr real_inner_eq_re_inner, ",", expr this, ",", expr continuous_linear_map.coe_restrict_scalars, ",", expr continuous_linear_map.coe_coe, ",", expr linear_map.coe_restrict_scalars_eq_coe, "]"] [] [] }],
  exact [expr eq_smul_self_of_is_local_extr_on_real hSA hextr]
end

/-- For a self-adjoint operator `T`, a local extremum of the Rayleigh quotient of `T` on a sphere
centred at the origin is an eigenvector of `T`. -/
theorem has_eigenvector_of_is_local_extr_on (hT : IsSelfAdjoint (T : E →ₗ[𝕜] E)) {x₀ : E} (hx₀ : x₀ ≠ 0)
  (hextr : IsLocalExtrOn T.re_apply_inner_self (sphere (0 : E) ∥x₀∥) x₀) :
  has_eigenvector (T : E →ₗ[𝕜] E) («expr↑ » (rayleigh_quotient x₀)) x₀ :=
  by 
    refine' ⟨_, hx₀⟩
    rw [Module.End.mem_eigenspace_iff]
    exact hT.eq_smul_self_of_is_local_extr_on hextr

-- error in Analysis.InnerProductSpace.Rayleigh: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- For a self-adjoint operator `T`, a maximum of the Rayleigh quotient of `T` on a sphere centred
at the origin is an eigenvector of `T`, with eigenvalue the global supremum of the Rayleigh
quotient. -/
theorem has_eigenvector_of_is_max_on
(hT : is_self_adjoint (T : «expr →ₗ[ ] »(E, 𝕜, E)))
{x₀ : E}
(hx₀ : «expr ≠ »(x₀, 0))
(hextr : is_max_on T.re_apply_inner_self (sphere (0 : E) «expr∥ ∥»(x₀)) x₀) : has_eigenvector (T : «expr →ₗ[ ] »(E, 𝕜, E)) «expr↑ »(«expr⨆ , »((x : {x : E // «expr ≠ »(x, 0)}), exprrayleigh_quotient() x)) x₀ :=
begin
  convert [] [expr hT.has_eigenvector_of_is_local_extr_on hx₀ (or.inr hextr.localize)] [],
  have [ident hx₀'] [":", expr «expr < »(0, «expr∥ ∥»(x₀))] [":=", expr by simp [] [] [] ["[", expr hx₀, "]"] [] []],
  have [ident hx₀''] [":", expr «expr ∈ »(x₀, sphere (0 : E) «expr∥ ∥»(x₀))] [":=", expr by simp [] [] [] [] [] []],
  rw [expr T.supr_rayleigh_eq_supr_rayleigh_sphere hx₀'] [],
  refine [expr is_max_on.supr_eq hx₀'' _],
  intros [ident x, ident hx],
  dsimp [] [] [] [],
  have [] [":", expr «expr = »(«expr∥ ∥»(x), «expr∥ ∥»(x₀))] [":=", expr by simpa [] [] [] [] [] ["using", expr hx]],
  rw [expr this] [],
  exact [expr div_le_div_of_le (sq_nonneg «expr∥ ∥»(x₀)) (hextr hx)]
end

-- error in Analysis.InnerProductSpace.Rayleigh: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- For a self-adjoint operator `T`, a minimum of the Rayleigh quotient of `T` on a sphere centred
at the origin is an eigenvector of `T`, with eigenvalue the global infimum of the Rayleigh
quotient. -/
theorem has_eigenvector_of_is_min_on
(hT : is_self_adjoint (T : «expr →ₗ[ ] »(E, 𝕜, E)))
{x₀ : E}
(hx₀ : «expr ≠ »(x₀, 0))
(hextr : is_min_on T.re_apply_inner_self (sphere (0 : E) «expr∥ ∥»(x₀)) x₀) : has_eigenvector (T : «expr →ₗ[ ] »(E, 𝕜, E)) «expr↑ »(«expr⨅ , »((x : {x : E // «expr ≠ »(x, 0)}), exprrayleigh_quotient() x)) x₀ :=
begin
  convert [] [expr hT.has_eigenvector_of_is_local_extr_on hx₀ (or.inl hextr.localize)] [],
  have [ident hx₀'] [":", expr «expr < »(0, «expr∥ ∥»(x₀))] [":=", expr by simp [] [] [] ["[", expr hx₀, "]"] [] []],
  have [ident hx₀''] [":", expr «expr ∈ »(x₀, sphere (0 : E) «expr∥ ∥»(x₀))] [":=", expr by simp [] [] [] [] [] []],
  rw [expr T.infi_rayleigh_eq_infi_rayleigh_sphere hx₀'] [],
  refine [expr is_min_on.infi_eq hx₀'' _],
  intros [ident x, ident hx],
  dsimp [] [] [] [],
  have [] [":", expr «expr = »(«expr∥ ∥»(x), «expr∥ ∥»(x₀))] [":=", expr by simpa [] [] [] [] [] ["using", expr hx]],
  rw [expr this] [],
  exact [expr div_le_div_of_le (sq_nonneg «expr∥ ∥»(x₀)) (hextr hx)]
end

end CompleteSpace

section FiniteDimensional

variable [FiniteDimensional 𝕜 E] [_i : Nontrivial E] {T : E →ₗ[𝕜] E}

include _i

-- error in Analysis.InnerProductSpace.Rayleigh: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The supremum of the Rayleigh quotient of a self-adjoint operator `T` on a nontrivial
finite-dimensional vector space is an eigenvalue for that operator. -/
theorem has_eigenvalue_supr_of_finite_dimensional
(hT : is_self_adjoint T) : has_eigenvalue T «expr↑ »(«expr⨆ , »((x : {x : E // «expr ≠ »(x, 0)}), «expr / »(is_R_or_C.re «expr⟪ , ⟫»(T x, x), «expr ^ »(«expr∥ ∥»((x : E)), 2)))) :=
begin
  let [ident T'] [":", expr «expr →L[ ] »(E, 𝕜, E)] [":=", expr T.to_continuous_linear_map],
  have [ident hT'] [":", expr is_self_adjoint (T' : «expr →ₗ[ ] »(E, 𝕜, E))] [":=", expr hT],
  obtain ["⟨", ident x, ",", ident hx, "⟩", ":", expr «expr∃ , »((x : E), «expr ≠ »(x, 0)), ":=", expr exists_ne 0],
  have [ident H₁] [":", expr is_compact (sphere (0 : E) «expr∥ ∥»(x))] [":=", expr is_compact_sphere _ _],
  have [ident H₂] [":", expr (sphere (0 : E) «expr∥ ∥»(x)).nonempty] [":=", expr ⟨x, by simp [] [] [] [] [] []⟩],
  obtain ["⟨", ident x₀, ",", ident hx₀', ",", ident hTx₀, "⟩", ":=", expr H₁.exists_forall_ge H₂ T'.re_apply_inner_self_continuous.continuous_on],
  have [ident hx₀] [":", expr «expr = »(«expr∥ ∥»(x₀), «expr∥ ∥»(x))] [":=", expr by simpa [] [] [] [] [] ["using", expr hx₀']],
  have [] [":", expr is_max_on T'.re_apply_inner_self (sphere 0 «expr∥ ∥»(x₀)) x₀] [],
  { simpa [] [] ["only"] ["[", "<-", expr hx₀, "]"] [] ["using", expr hTx₀] },
  have [ident hx₀_ne] [":", expr «expr ≠ »(x₀, 0)] [],
  { have [] [":", expr «expr ≠ »(«expr∥ ∥»(x₀), 0)] [":=", expr by simp [] [] ["only"] ["[", expr hx₀, ",", expr norm_eq_zero, ",", expr hx, ",", expr ne.def, ",", expr not_false_iff, "]"] [] []],
    simpa [] [] [] ["[", "<-", expr norm_eq_zero, ",", expr ne.def, "]"] [] [] },
  exact [expr has_eigenvalue_of_has_eigenvector (hT'.has_eigenvector_of_is_max_on hx₀_ne this)]
end

-- error in Analysis.InnerProductSpace.Rayleigh: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The infimum of the Rayleigh quotient of a self-adjoint operator `T` on a nontrivial
finite-dimensional vector space is an eigenvalue for that operator. -/
theorem has_eigenvalue_infi_of_finite_dimensional
(hT : is_self_adjoint T) : has_eigenvalue T «expr↑ »(«expr⨅ , »((x : {x : E // «expr ≠ »(x, 0)}), «expr / »(is_R_or_C.re «expr⟪ , ⟫»(T x, x), «expr ^ »(«expr∥ ∥»((x : E)), 2)))) :=
begin
  let [ident T'] [":", expr «expr →L[ ] »(E, 𝕜, E)] [":=", expr T.to_continuous_linear_map],
  have [ident hT'] [":", expr is_self_adjoint (T' : «expr →ₗ[ ] »(E, 𝕜, E))] [":=", expr hT],
  obtain ["⟨", ident x, ",", ident hx, "⟩", ":", expr «expr∃ , »((x : E), «expr ≠ »(x, 0)), ":=", expr exists_ne 0],
  have [ident H₁] [":", expr is_compact (sphere (0 : E) «expr∥ ∥»(x))] [":=", expr is_compact_sphere _ _],
  have [ident H₂] [":", expr (sphere (0 : E) «expr∥ ∥»(x)).nonempty] [":=", expr ⟨x, by simp [] [] [] [] [] []⟩],
  obtain ["⟨", ident x₀, ",", ident hx₀', ",", ident hTx₀, "⟩", ":=", expr H₁.exists_forall_le H₂ T'.re_apply_inner_self_continuous.continuous_on],
  have [ident hx₀] [":", expr «expr = »(«expr∥ ∥»(x₀), «expr∥ ∥»(x))] [":=", expr by simpa [] [] [] [] [] ["using", expr hx₀']],
  have [] [":", expr is_min_on T'.re_apply_inner_self (sphere 0 «expr∥ ∥»(x₀)) x₀] [],
  { simpa [] [] ["only"] ["[", "<-", expr hx₀, "]"] [] ["using", expr hTx₀] },
  have [ident hx₀_ne] [":", expr «expr ≠ »(x₀, 0)] [],
  { have [] [":", expr «expr ≠ »(«expr∥ ∥»(x₀), 0)] [":=", expr by simp [] [] ["only"] ["[", expr hx₀, ",", expr norm_eq_zero, ",", expr hx, ",", expr ne.def, ",", expr not_false_iff, "]"] [] []],
    simpa [] [] [] ["[", "<-", expr norm_eq_zero, ",", expr ne.def, "]"] [] [] },
  exact [expr has_eigenvalue_of_has_eigenvector (hT'.has_eigenvector_of_is_min_on hx₀_ne this)]
end

omit _i

theorem subsingleton_of_no_eigenvalue_finite_dimensional (hT : IsSelfAdjoint T)
  (hT' : ∀ μ : 𝕜, Module.End.eigenspace (T : E →ₗ[𝕜] E) μ = ⊥) : Subsingleton E :=
  (subsingleton_or_nontrivial E).resolve_right
    fun h =>
      by 
        exact absurd (hT' _) hT.has_eigenvalue_supr_of_finite_dimensional

end FiniteDimensional

end IsSelfAdjoint

