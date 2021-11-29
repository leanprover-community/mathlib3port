import Mathbin.Analysis.InnerProductSpace.Rayleigh 
import Mathbin.Analysis.InnerProductSpace.PiL2

/-! # Spectral theory of self-adjoint operators

This file covers the spectral theory of self-adjoint operators on an inner product space.

The first part of the file covers general properties, true without any condition on boundedness or
compactness of the operator or finite-dimensionality of the underlying space, notably:
* `is_self_adjoint.conj_eigenvalue_eq_self`: the eigenvalues are real
* `is_self_adjoint.orthogonal_family_eigenspaces`: the eigenspaces are orthogonal
* `is_self_adjoint.orthogonal_supr_eigenspaces`: the restriction of the operator to the mutual
  orthogonal complement of the eigenspaces has, itself, no eigenvectors

The second part of the file covers properties of self-adjoint operators in finite dimension.
Letting `T` be a self-adjoint operator on a finite-dimensional inner product space `T`,
* The definition `is_self_adjoint.diagonalization` provides a linear isometry equivalence `E` to
  the direct sum of the eigenspaces of `T`.  The theorem
  `is_self_adjoint.diagonalization_apply_self_apply` states that, when `T` is transferred via this
  equivalence to an operator on the direct sum, it acts diagonally.
* The definition `is_self_adjoint.eigenvector_basis` provides an orthonormal basis for `E`
  consisting of eigenvectors of `T`, with `is_self_adjoint.eigenvalues` giving the corresponding
  list of eigenvalues, as real numbers.  The definition `is_self_adjoint.diagonalization_basis`
  gives the associated linear isometry equivalence from `E` to Euclidean space, and the theorem
  `is_self_adjoint.diagonalization_basis_apply_self_apply` states that, when `T` is transferred via
  this equivalence to an operator on Euclidean space, it acts diagonally.
These are forms of the *diagonalization theorem* for self-adjoint operators on finite-dimensional
inner product spaces.

## TODO

Spectral theory for compact self-adjoint operators, bounded self-adjoint operators.

## Tags

self-adjoint operator, spectral theorem, diagonalization theorem

-/


variable{𝕜 : Type _}[IsROrC 𝕜][dec_𝕜 : DecidableEq 𝕜]

variable{E : Type _}[InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 E _ x y

attribute [local instance] fact_one_le_two_real

open_locale BigOperators ComplexConjugate

open Module.End

namespace IsSelfAdjoint

variable{T : E →ₗ[𝕜] E}(hT : IsSelfAdjoint T)

include hT

-- error in Analysis.InnerProductSpace.Spectrum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A self-adjoint operator preserves orthogonal complements of its eigenspaces. -/
theorem invariant_orthogonal_eigenspace
(μ : 𝕜)
(v : E)
(hv : «expr ∈ »(v, «expr ᗮ»(eigenspace T μ))) : «expr ∈ »(T v, «expr ᗮ»(eigenspace T μ)) :=
begin
  intros [ident w, ident hw],
  have [] [":", expr «expr = »(T w, «expr • »((μ : 𝕜), w))] [":=", expr by rwa [expr mem_eigenspace_iff] ["at", ident hw]],
  simp [] [] [] ["[", "<-", expr hT w, ",", expr this, ",", expr inner_smul_left, ",", expr hv w hw, "]"] [] []
end

/-- The eigenvalues of a self-adjoint operator are real. -/
theorem conj_eigenvalue_eq_self {μ : 𝕜} (hμ : has_eigenvalue T μ) : conj μ = μ :=
  by 
    obtain ⟨v, hv₁, hv₂⟩ := hμ.exists_has_eigenvector 
    rw [mem_eigenspace_iff] at hv₁ 
    simpa [hv₂, inner_smul_left, inner_smul_right, hv₁] using hT v v

-- error in Analysis.InnerProductSpace.Spectrum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The eigenspaces of a self-adjoint operator are mutually orthogonal. -/
theorem orthogonal_family_eigenspaces : orthogonal_family 𝕜 (eigenspace T) :=
begin
  intros [ident μ, ident ν, ident hμν, ident v, ident hv, ident w, ident hw],
  by_cases [expr hv', ":", expr «expr = »(v, 0)],
  { simp [] [] [] ["[", expr hv', "]"] [] [] },
  have [ident H] [] [":=", expr hT.conj_eigenvalue_eq_self (has_eigenvalue_of_has_eigenvector ⟨hv, hv'⟩)],
  rw [expr mem_eigenspace_iff] ["at", ident hv, ident hw],
  refine [expr or.resolve_left _ hμν.symm],
  simpa [] [] [] ["[", expr inner_smul_left, ",", expr inner_smul_right, ",", expr hv, ",", expr hw, ",", expr H, "]"] [] ["using", expr (hT v w).symm]
end

-- error in Analysis.InnerProductSpace.Spectrum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem orthogonal_family_eigenspaces' : orthogonal_family 𝕜 (λ μ : eigenvalues T, eigenspace T μ) :=
hT.orthogonal_family_eigenspaces.comp subtype.coe_injective

/-- The mutual orthogonal complement of the eigenspaces of a self-adjoint operator on an inner
product space is an invariant subspace of the operator. -/
theorem orthogonal_supr_eigenspaces_invariant ⦃v : E⦄ (hv : v ∈ (⨆μ, eigenspace T μ)ᗮ) : T v ∈ (⨆μ, eigenspace T μ)ᗮ :=
  by 
    rw [←Submodule.infi_orthogonal] at hv⊢
    exact T.infi_invariant hT.invariant_orthogonal_eigenspace v hv

-- error in Analysis.InnerProductSpace.Spectrum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The mutual orthogonal complement of the eigenspaces of a self-adjoint operator on an inner
product space has no eigenvalues. -/
theorem orthogonal_supr_eigenspaces
(μ : 𝕜) : «expr = »(eigenspace (T.restrict hT.orthogonal_supr_eigenspaces_invariant) μ, «expr⊥»()) :=
begin
  set [] [ident p] [":", expr submodule 𝕜 E] [":="] [expr «expr ᗮ»(«expr⨆ , »((μ), eigenspace T μ))] [],
  refine [expr eigenspace_restrict_eq_bot hT.orthogonal_supr_eigenspaces_invariant _],
  have [ident H₂] [":", expr «expr ≤ »(p, «expr ᗮ»(eigenspace T μ))] [":=", expr submodule.orthogonal_le (le_supr _ _)],
  exact [expr (eigenspace T μ).orthogonal_disjoint.mono_right H₂]
end

/-! ### Finite-dimensional theory -/


variable[FiniteDimensional 𝕜 E]

-- error in Analysis.InnerProductSpace.Spectrum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The mutual orthogonal complement of the eigenspaces of a self-adjoint operator on a
finite-dimensional inner product space is trivial. -/
theorem orthogonal_supr_eigenspaces_eq_bot : «expr = »(«expr ᗮ»(«expr⨆ , »((μ), eigenspace T μ)), «expr⊥»()) :=
begin
  have [ident hT'] [":", expr is_self_adjoint _] [":=", expr hT.restrict_invariant hT.orthogonal_supr_eigenspaces_invariant],
  haveI [] [] [":=", expr hT'.subsingleton_of_no_eigenvalue_finite_dimensional hT.orthogonal_supr_eigenspaces],
  exact [expr submodule.eq_bot_of_subsingleton _]
end

theorem orthogonal_supr_eigenspaces_eq_bot' : (⨆μ : eigenvalues T, eigenspace T μ)ᗮ = ⊥ :=
  show (⨆μ : { μ // eigenspace T μ ≠ ⊥ }, eigenspace T μ)ᗮ = ⊥by 
    rw [supr_ne_bot_subtype, hT.orthogonal_supr_eigenspaces_eq_bot]

include dec_𝕜

-- error in Analysis.InnerProductSpace.Spectrum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The eigenspaces of a self-adjoint operator on a finite-dimensional inner product space `E` give
an internal direct sum decomposition of `E`. -/
theorem direct_sum_submodule_is_internal : direct_sum.submodule_is_internal (λ μ : eigenvalues T, eigenspace T μ) :=
hT.orthogonal_family_eigenspaces'.submodule_is_internal_iff.mpr hT.orthogonal_supr_eigenspaces_eq_bot'

section Version1

-- error in Analysis.InnerProductSpace.Spectrum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Isometry from an inner product space `E` to the direct sum of the eigenspaces of some
self-adjoint operator `T` on `E`. -/
noncomputable
def diagonalization : «expr ≃ₗᵢ[ ] »(E, 𝕜, pi_Lp 2 (λ μ : eigenvalues T, eigenspace T μ)) :=
hT.direct_sum_submodule_is_internal.isometry_L2_of_orthogonal_family hT.orthogonal_family_eigenspaces'

-- error in Analysis.InnerProductSpace.Spectrum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[simp]
theorem diagonalization_symm_apply
(w : pi_Lp 2 (λ μ : eigenvalues T, eigenspace T μ)) : «expr = »(hT.diagonalization.symm w, «expr∑ , »((μ), w μ)) :=
hT.direct_sum_submodule_is_internal.isometry_L2_of_orthogonal_family_symm_apply hT.orthogonal_family_eigenspaces' w

-- error in Analysis.InnerProductSpace.Spectrum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- *Diagonalization theorem*, *spectral theorem*; version 1: A self-adjoint operator `T` on a
finite-dimensional inner product space `E` acts diagonally on the decomposition of `E` into the
direct sum of the eigenspaces of `T`. -/
theorem diagonalization_apply_self_apply
(v : E)
(μ : eigenvalues T) : «expr = »(hT.diagonalization (T v) μ, «expr • »((μ : 𝕜), hT.diagonalization v μ)) :=
begin
  suffices [] [":", expr ∀
   w : pi_Lp 2 (λ
    μ : eigenvalues T, eigenspace T μ), «expr = »(T (hT.diagonalization.symm w), hT.diagonalization.symm (λ
     μ, «expr • »((μ : 𝕜), w μ)))],
  { simpa [] [] [] ["[", expr linear_isometry_equiv.symm_apply_apply, ",", "-", ident is_self_adjoint.diagonalization_symm_apply, "]"] [] ["using", expr congr_arg (λ
      w, hT.diagonalization w μ) (this (hT.diagonalization v))] },
  intros [ident w],
  have [ident hwT] [":", expr ∀ μ : eigenvalues T, «expr = »(T (w μ), «expr • »((μ : 𝕜), w μ))] [],
  { intros [ident μ],
    simpa [] [] [] ["[", expr mem_eigenspace_iff, "]"] [] ["using", expr (w μ).prop] },
  simp [] [] [] ["[", expr hwT, "]"] [] []
end

end Version1

section Version2

variable{n : ℕ}(hn : FiniteDimensional.finrank 𝕜 E = n)

/-- A choice of orthonormal basis of eigenvectors for self-adjoint operator `T` on a
finite-dimensional inner product space `E`.

TODO Postcompose with a permutation so that these eigenvectors are listed in increasing order of
eigenvalue. -/
noncomputable def eigenvector_basis : Basis (Finₓ n) 𝕜 E :=
  hT.direct_sum_submodule_is_internal.subordinate_orthonormal_basis hn

theorem eigenvector_basis_orthonormal : Orthonormal 𝕜 (hT.eigenvector_basis hn) :=
  hT.direct_sum_submodule_is_internal.subordinate_orthonormal_basis_orthonormal hn hT.orthogonal_family_eigenspaces'

/-- The sequence of real eigenvalues associated to the standard orthonormal basis of eigenvectors
for a self-adjoint operator `T` on `E`.

TODO Postcompose with a permutation so that these eigenvalues are listed in increasing order. -/
noncomputable def eigenvalues (i : Finₓ n) : ℝ :=
  @IsROrC.re 𝕜 _$ hT.direct_sum_submodule_is_internal.subordinate_orthonormal_basis_index hn i

-- error in Analysis.InnerProductSpace.Spectrum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_eigenvector_eigenvector_basis
(i : fin n) : has_eigenvector T (hT.eigenvalues hn i) (hT.eigenvector_basis hn i) :=
begin
  let [ident v] [":", expr E] [":=", expr hT.eigenvector_basis hn i],
  let [ident μ] [":", expr 𝕜] [":=", expr hT.direct_sum_submodule_is_internal.subordinate_orthonormal_basis_index hn i],
  change [expr has_eigenvector T (is_R_or_C.re μ) v] [] [],
  have [ident key] [":", expr has_eigenvector T μ v] [],
  { have [ident H₁] [":", expr «expr ∈ »(v, eigenspace T μ)] [],
    { exact [expr hT.direct_sum_submodule_is_internal.subordinate_orthonormal_basis_subordinate hn i] },
    have [ident H₂] [":", expr «expr ≠ »(v, 0)] [":=", expr (hT.eigenvector_basis_orthonormal hn).ne_zero i],
    exact [expr ⟨H₁, H₂⟩] },
  have [ident re_μ] [":", expr «expr = »(«expr↑ »(is_R_or_C.re μ), μ)] [],
  { rw ["<-", expr is_R_or_C.eq_conj_iff_re] [],
    exact [expr hT.conj_eigenvalue_eq_self (has_eigenvalue_of_has_eigenvector key)] },
  simpa [] [] [] ["[", expr re_μ, "]"] [] ["using", expr key]
end

attribute [irreducible] eigenvector_basis eigenvalues

@[simp]
theorem apply_eigenvector_basis (i : Finₓ n) :
  T (hT.eigenvector_basis hn i) = (hT.eigenvalues hn i : 𝕜) • hT.eigenvector_basis hn i :=
  mem_eigenspace_iff.mp (hT.has_eigenvector_eigenvector_basis hn i).1

/-- An isometry from an inner product space `E` to Euclidean space, induced by a choice of
orthonormal basis of eigenvectors for a self-adjoint operator `T` on `E`. -/
noncomputable def diagonalization_basis : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Finₓ n) :=
  (hT.eigenvector_basis hn).isometryEuclideanOfOrthonormal (hT.eigenvector_basis_orthonormal hn)

@[simp]
theorem diagonalization_basis_symm_apply (w : EuclideanSpace 𝕜 (Finₓ n)) :
  (hT.diagonalization_basis hn).symm w = ∑i, w i • hT.eigenvector_basis hn i :=
  by 
    simp [diagonalization_basis]

/-- *Diagonalization theorem*, *spectral theorem*; version 2: A self-adjoint operator `T` on a
finite-dimensional inner product space `E` acts diagonally on the identification of `E` with
Euclidean space induced by an orthonormal basis of eigenvectors of `T`. -/
theorem diagonalization_basis_apply_self_apply (v : E) (i : Finₓ n) :
  hT.diagonalization_basis hn (T v) i = hT.eigenvalues hn i*hT.diagonalization_basis hn v i :=
  by 
    suffices  :
      ∀ (w : EuclideanSpace 𝕜 (Finₓ n)),
        T ((hT.diagonalization_basis hn).symm w) = (hT.diagonalization_basis hn).symm fun i => hT.eigenvalues hn i*w i
    ·
      simpa [-diagonalization_basis_symm_apply] using
        congr_argₓ (fun v => hT.diagonalization_basis hn v i) (this (hT.diagonalization_basis hn v))
    intro w 
    simp [mul_commₓ, mul_smul]

end Version2

end IsSelfAdjoint

