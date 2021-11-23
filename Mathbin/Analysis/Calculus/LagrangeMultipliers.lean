import Mathbin.Analysis.Calculus.Inverse 
import Mathbin.LinearAlgebra.Dual

/-!
# Lagrange multipliers

In this file we formalize the
[Lagrange multipliers](https://en.wikipedia.org/wiki/Lagrange_multiplier) method of solving
conditional extremum problems: if a function `φ` has a local extremum at `x₀` on the set
`f ⁻¹' {f x₀}`, `f x = (f₀ x, ..., fₙ₋₁ x)`, then the differentials of `fₖ` and `φ` are linearly
dependent. First we formulate a geometric version of this theorem which does not rely on the
target space being `ℝⁿ`, then restate it in terms of coordinates.

## TODO

Formalize Karush-Kuhn-Tucker theorem

## Tags

lagrange multiplier, local extremum

-/


open Filter Set

open_locale TopologicalSpace Filter BigOperators

variable{E F :
    Type
      _}[NormedGroup
      E][NormedSpace ℝ
      E][CompleteSpace
      E][NormedGroup F][NormedSpace ℝ F][CompleteSpace F]{f : E → F}{φ : E → ℝ}{x₀ : E}{f' : E →L[ℝ] F}{φ' : E →L[ℝ] ℝ}

-- error in Analysis.Calculus.LagrangeMultipliers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Lagrange multipliers theorem: if `φ : E → ℝ` has a local extremum on the set `{x | f x = f x₀}`
at `x₀`, both `f : E → F` and `φ` are strictly differentiable at `x₀`, and the codomain of `f` is
a complete space, then the linear map `x ↦ (f' x, φ' x)` is not surjective. -/
theorem is_local_extr_on.range_ne_top_of_has_strict_fderiv_at
(hextr : is_local_extr_on φ {x | «expr = »(f x, f x₀)} x₀)
(hf' : has_strict_fderiv_at f f' x₀)
(hφ' : has_strict_fderiv_at φ φ' x₀) : «expr ≠ »((f'.prod φ').range, «expr⊤»()) :=
begin
  intro [ident htop],
  set [] [ident fφ] [] [":="] [expr λ x, (f x, φ x)] [],
  have [ident A] [":", expr «expr = »(map φ «expr𝓝[ ] »(«expr ⁻¹' »(f, {f x₀}), x₀), expr𝓝() (φ x₀))] [],
  { change [expr «expr = »(map «expr ∘ »(prod.snd, fφ) «expr𝓝[ ] »(«expr ⁻¹' »(fφ, {p | «expr = »(p.1, f x₀)}), x₀), expr𝓝() (φ x₀))] [] [],
    rw ["[", "<-", expr map_map, ",", expr nhds_within, ",", expr map_inf_principal_preimage, ",", expr (hf'.prod hφ').map_nhds_eq_of_surj htop, "]"] [],
    exact [expr map_snd_nhds_within _] },
  exact [expr hextr.not_nhds_le_map A.ge]
end

/-- Lagrange multipliers theorem: if `φ : E → ℝ` has a local extremum on the set `{x | f x = f x₀}`
at `x₀`, both `f : E → F` and `φ` are strictly differentiable at `x₀`, and the codomain of `f` is
a complete space, then there exist `Λ : dual ℝ F` and `Λ₀ : ℝ` such that `(Λ, Λ₀) ≠ 0` and
`Λ (f' x) + Λ₀ • φ' x = 0` for all `x`. -/
theorem IsLocalExtrOn.exists_linear_map_of_has_strict_fderiv_at (hextr : IsLocalExtrOn φ { x | f x = f x₀ } x₀)
  (hf' : HasStrictFderivAt f f' x₀) (hφ' : HasStrictFderivAt φ φ' x₀) :
  ∃ (Λ : Module.Dual ℝ F)(Λ₀ : ℝ), (Λ, Λ₀) ≠ 0 ∧ ∀ x, (Λ (f' x)+Λ₀ • φ' x) = 0 :=
  by 
    rcases
      Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2$ hextr.range_ne_top_of_has_strict_fderiv_at hf' hφ') with
      ⟨Λ', h0, hΛ'⟩
    set e : ((F →ₗ[ℝ] ℝ) × ℝ) ≃ₗ[ℝ] F × ℝ →ₗ[ℝ] ℝ :=
      ((LinearEquiv.refl ℝ (F →ₗ[ℝ] ℝ)).Prod (LinearMap.ringLmapEquivSelf ℝ ℝ ℝ).symm).trans (LinearMap.coprodEquiv ℝ)
    rcases e.surjective Λ' with ⟨⟨Λ, Λ₀⟩, rfl⟩
    refine' ⟨Λ, Λ₀, e.map_ne_zero_iff.1 h0, fun x => _⟩
    convert LinearMap.congr_fun (LinearMap.range_le_ker_iff.1 hΛ') x using 1
    simp only [LinearMap.coprod_equiv_apply, LinearEquiv.refl_apply, LinearMap.ring_lmap_equiv_self_symm_apply,
      LinearMap.comp_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.prod_apply, LinearEquiv.trans_apply,
      LinearEquiv.prod_apply, LinearMap.coprod_apply, LinearMap.smul_right_apply, LinearMap.one_apply, smul_eq_mul,
      mul_commₓ]

-- error in Analysis.Calculus.LagrangeMultipliers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Lagrange multipliers theorem: if `φ : E → ℝ` has a local extremum on the set `{x | f x = f x₀}`
at `x₀`, and both `f : E → ℝ` and `φ` are strictly differentiable at `x₀`, then there exist
`a b : ℝ` such that `(a, b) ≠ 0` and `a • f' + b • φ' = 0`. -/
theorem is_local_extr_on.exists_multipliers_of_has_strict_fderiv_at_1d
{f : E → exprℝ()}
{f' : «expr →L[ ] »(E, exprℝ(), exprℝ())}
(hextr : is_local_extr_on φ {x | «expr = »(f x, f x₀)} x₀)
(hf' : has_strict_fderiv_at f f' x₀)
(hφ' : has_strict_fderiv_at φ φ' x₀) : «expr∃ , »((a
  b : exprℝ()), «expr ∧ »(«expr ≠ »((a, b), 0), «expr = »(«expr + »(«expr • »(a, f'), «expr • »(b, φ')), 0))) :=
begin
  obtain ["⟨", ident Λ, ",", ident Λ₀, ",", ident hΛ, ",", ident hfΛ, "⟩", ":=", expr hextr.exists_linear_map_of_has_strict_fderiv_at hf' hφ'],
  refine [expr ⟨Λ 1, Λ₀, _, _⟩],
  { contrapose ["!"] [ident hΛ],
    simp [] [] ["only"] ["[", expr prod.mk_eq_zero, "]"] [] ["at", "⊢", ident hΛ],
    refine [expr ⟨linear_map.ext (λ x, _), hΛ.2⟩],
    simpa [] [] [] ["[", expr hΛ.1, "]"] [] ["using", expr Λ.map_smul x 1] },
  { ext [] [ident x] [],
    have [ident H₁] [":", expr «expr = »(Λ (f' x), «expr * »(f' x, Λ 1))] [],
    { simpa [] [] ["only"] ["[", expr mul_one, ",", expr algebra.id.smul_eq_mul, "]"] [] ["using", expr Λ.map_smul (f' x) 1] },
    have [ident H₂] [":", expr «expr = »(«expr + »(«expr * »(f' x, Λ 1), «expr * »(Λ₀, φ' x)), 0)] [],
    { simpa [] [] ["only"] ["[", expr algebra.id.smul_eq_mul, ",", expr H₁, "]"] [] ["using", expr hfΛ x] },
    simpa [] [] [] ["[", expr mul_comm, "]"] [] ["using", expr H₂] }
end

-- error in Analysis.Calculus.LagrangeMultipliers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Lagrange multipliers theorem, 1d version. Let `f : ι → E → ℝ` be a finite family of functions.
Suppose that `φ : E → ℝ` has a local extremum on the set `{x | ∀ i, f i x = f i x₀}` at `x₀`.
Suppose that all functions `f i` as well as `φ` are strictly differentiable at `x₀`.
Then the derivatives `f' i : E → L[ℝ] ℝ` and `φ' : E →L[ℝ] ℝ` are linearly dependent:
there exist `Λ : ι → ℝ` and `Λ₀ : ℝ`, `(Λ, Λ₀) ≠ 0`, such that `∑ i, Λ i • f' i + Λ₀ • φ' = 0`.

See also `is_local_extr_on.linear_dependent_of_has_strict_fderiv_at` for a version that
states `¬linear_independent ℝ _` instead of existence of `Λ` and `Λ₀`. -/
theorem is_local_extr_on.exists_multipliers_of_has_strict_fderiv_at
{ι : Type*}
[fintype ι]
{f : ι → E → exprℝ()}
{f' : ι → «expr →L[ ] »(E, exprℝ(), exprℝ())}
(hextr : is_local_extr_on φ {x | ∀ i, «expr = »(f i x, f i x₀)} x₀)
(hf' : ∀ i, has_strict_fderiv_at (f i) (f' i) x₀)
(hφ' : has_strict_fderiv_at φ φ' x₀) : «expr∃ , »((Λ : ι → exprℝ())
 (Λ₀ : exprℝ()), «expr ∧ »(«expr ≠ »((Λ, Λ₀), 0), «expr = »(«expr + »(«expr∑ , »((i), «expr • »(Λ i, f' i)), «expr • »(Λ₀, φ')), 0))) :=
begin
  letI [] [] [":=", expr classical.dec_eq ι],
  replace [ident hextr] [":", expr is_local_extr_on φ {x | «expr = »(λ i, f i x, λ i, f i x₀)} x₀] [],
  by simpa [] [] ["only"] ["[", expr function.funext_iff, "]"] [] ["using", expr hextr],
  rcases [expr hextr.exists_linear_map_of_has_strict_fderiv_at (has_strict_fderiv_at_pi.2 (λ
     i, hf' i)) hφ', "with", "⟨", ident Λ, ",", ident Λ₀, ",", ident h0, ",", ident hsum, "⟩"],
  rcases [expr (linear_equiv.pi_ring exprℝ() exprℝ() ι exprℝ()).symm.surjective Λ, "with", "⟨", ident Λ, ",", ident rfl, "⟩"],
  refine [expr ⟨Λ, Λ₀, _, _⟩],
  { simpa [] [] ["only"] ["[", expr ne.def, ",", expr prod.ext_iff, ",", expr linear_equiv.map_eq_zero_iff, ",", expr prod.fst_zero, "]"] [] ["using", expr h0] },
  { ext [] [ident x] [],
    simpa [] [] [] ["[", expr mul_comm, "]"] [] ["using", expr hsum x] }
end

/-- Lagrange multipliers theorem. Let `f : ι → E → ℝ` be a finite family of functions.
Suppose that `φ : E → ℝ` has a local extremum on the set `{x | ∀ i, f i x = f i x₀}` at `x₀`.
Suppose that all functions `f i` as well as `φ` are strictly differentiable at `x₀`.
Then the derivatives `f' i : E → L[ℝ] ℝ` and `φ' : E →L[ℝ] ℝ` are linearly dependent.

See also `is_local_extr_on.exists_multipliers_of_has_strict_fderiv_at` for a version that
that states existence of Lagrange multipliers `Λ` and `Λ₀` instead of using
`¬linear_independent ℝ _` -/
theorem IsLocalExtrOn.linear_dependent_of_has_strict_fderiv_at {ι : Type _} [Fintype ι] {f : ι → E → ℝ}
  {f' : ι → E →L[ℝ] ℝ} (hextr : IsLocalExtrOn φ { x | ∀ i, f i x = f i x₀ } x₀)
  (hf' : ∀ i, HasStrictFderivAt (f i) (f' i) x₀) (hφ' : HasStrictFderivAt φ φ' x₀) :
  ¬LinearIndependent ℝ (fun i => Option.elim i φ' f' : Option ι → E →L[ℝ] ℝ) :=
  by 
    rw [Fintype.linear_independent_iff]
    pushNeg 
    rcases hextr.exists_multipliers_of_has_strict_fderiv_at hf' hφ' with ⟨Λ, Λ₀, hΛ, hΛf⟩
    refine' ⟨fun i => Option.elim i Λ₀ Λ, _, _⟩
    ·
      simpa [add_commₓ] using hΛf
    ·
      simpa [Function.funext_iffₓ, not_and_distrib, or_comm, Option.exists] using hΛ

