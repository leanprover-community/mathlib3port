/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth

! This file was ported from Lean 3 source module analysis.inner_product_space.spectrum
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
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


variable {𝕜 : Type _} [IsROrC 𝕜] [dec_𝕜 : DecidableEq 𝕜]

variable {E : Type _} [InnerProductSpace 𝕜 E]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 E _ x y

open BigOperators ComplexConjugate

open Module.EndCat

namespace LinearMap

namespace IsSymmetric

variable {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)

include hT

/-- A self-adjoint operator preserves orthogonal complements of its eigenspaces. -/
theorem invariant_orthogonal_eigenspace (μ : 𝕜) (v : E) (hv : v ∈ (eigenspace T μ)ᗮ) :
    T v ∈ (eigenspace T μ)ᗮ := by
  intro w hw
  have : T w = (μ : 𝕜) • w := by rwa [mem_eigenspace_iff] at hw
  simp [← hT w, this, inner_smul_left, hv w hw]
#align
  linear_map.is_symmetric.invariant_orthogonal_eigenspace LinearMap.IsSymmetric.invariant_orthogonal_eigenspace

/-- The eigenvalues of a self-adjoint operator are real. -/
theorem conj_eigenvalue_eq_self {μ : 𝕜} (hμ : HasEigenvalue T μ) : conj μ = μ :=
  by
  obtain ⟨v, hv₁, hv₂⟩ := hμ.exists_has_eigenvector
  rw [mem_eigenspace_iff] at hv₁
  simpa [hv₂, inner_smul_left, inner_smul_right, hv₁] using hT v v
#align linear_map.is_symmetric.conj_eigenvalue_eq_self LinearMap.IsSymmetric.conj_eigenvalue_eq_self

/-- The eigenspaces of a self-adjoint operator are mutually orthogonal. -/
theorem orthogonalFamilyEigenspaces :
    @OrthogonalFamily 𝕜 _ _ _ _ (fun μ => eigenspace T μ) _ fun μ => (eigenspace T μ).subtypeₗᵢ :=
  by
  rintro μ ν hμν ⟨v, hv⟩ ⟨w, hw⟩
  by_cases hv' : v = 0
  · simp [hv']
  have H := hT.conj_eigenvalue_eq_self (has_eigenvalue_of_has_eigenvector ⟨hv, hv'⟩)
  rw [mem_eigenspace_iff] at hv hw
  refine' Or.resolve_left _ hμν.symm
  simpa [inner_smul_left, inner_smul_right, hv, hw, H] using (hT v w).symm
#align
  linear_map.is_symmetric.orthogonal_family_eigenspaces LinearMap.IsSymmetric.orthogonalFamilyEigenspaces

theorem orthogonalFamilyEigenspaces' :
    @OrthogonalFamily 𝕜 _ _ _ _ (fun μ : Eigenvalues T => eigenspace T μ) _ fun μ =>
      (eigenspace T μ).subtypeₗᵢ :=
  hT.orthogonalFamilyEigenspaces.comp Subtype.coe_injective
#align
  linear_map.is_symmetric.orthogonal_family_eigenspaces' LinearMap.IsSymmetric.orthogonalFamilyEigenspaces'

/-- The mutual orthogonal complement of the eigenspaces of a self-adjoint operator on an inner
product space is an invariant subspace of the operator. -/
theorem orthogonal_supr_eigenspaces_invariant ⦃v : E⦄ (hv : v ∈ (⨆ μ, eigenspace T μ)ᗮ) :
    T v ∈ (⨆ μ, eigenspace T μ)ᗮ :=
  by
  rw [← Submodule.infi_orthogonal] at hv⊢
  exact T.infi_invariant hT.invariant_orthogonal_eigenspace v hv
#align
  linear_map.is_symmetric.orthogonal_supr_eigenspaces_invariant LinearMap.IsSymmetric.orthogonal_supr_eigenspaces_invariant

/-- The mutual orthogonal complement of the eigenspaces of a self-adjoint operator on an inner
product space has no eigenvalues. -/
theorem orthogonal_supr_eigenspaces (μ : 𝕜) :
    eigenspace (T.restrict hT.orthogonal_supr_eigenspaces_invariant) μ = ⊥ :=
  by
  set p : Submodule 𝕜 E := (⨆ μ, eigenspace T μ)ᗮ
  refine' eigenspace_restrict_eq_bot hT.orthogonal_supr_eigenspaces_invariant _
  have H₂ : p ≤ (eigenspace T μ)ᗮ := Submodule.orthogonal_le (le_supᵢ _ _)
  exact (eigenspace T μ).orthogonal_disjoint.mono_right H₂
#align
  linear_map.is_symmetric.orthogonal_supr_eigenspaces LinearMap.IsSymmetric.orthogonal_supr_eigenspaces

/-! ### Finite-dimensional theory -/


variable [FiniteDimensional 𝕜 E]

/-- The mutual orthogonal complement of the eigenspaces of a self-adjoint operator on a
finite-dimensional inner product space is trivial. -/
theorem orthogonal_supr_eigenspaces_eq_bot : (⨆ μ, eigenspace T μ)ᗮ = ⊥ :=
  by
  have hT' : is_symmetric _ := hT.restrict_invariant hT.orthogonal_supr_eigenspaces_invariant
  -- a self-adjoint operator on a nontrivial inner product space has an eigenvalue
  haveI := hT'.subsingleton_of_no_eigenvalue_finite_dimensional hT.orthogonal_supr_eigenspaces
  exact Submodule.eq_bot_of_subsingleton _
#align
  linear_map.is_symmetric.orthogonal_supr_eigenspaces_eq_bot LinearMap.IsSymmetric.orthogonal_supr_eigenspaces_eq_bot

theorem orthogonal_supr_eigenspaces_eq_bot' : (⨆ μ : Eigenvalues T, eigenspace T μ)ᗮ = ⊥ :=
  show (⨆ μ : { μ // eigenspace T μ ≠ ⊥ }, eigenspace T μ)ᗮ = ⊥ by
    rw [supᵢ_ne_bot_subtype, hT.orthogonal_supr_eigenspaces_eq_bot]
#align
  linear_map.is_symmetric.orthogonal_supr_eigenspaces_eq_bot' LinearMap.IsSymmetric.orthogonal_supr_eigenspaces_eq_bot'

include dec_𝕜

/-- The eigenspaces of a self-adjoint operator on a finite-dimensional inner product space `E` give
an internal direct sum decomposition of `E`. -/
theorem direct_sum_is_internal : DirectSum.IsInternal fun μ : Eigenvalues T => eigenspace T μ :=
  hT.orthogonalFamilyEigenspaces'.is_internal_iff.mpr hT.orthogonal_supr_eigenspaces_eq_bot'
#align linear_map.is_symmetric.direct_sum_is_internal LinearMap.IsSymmetric.direct_sum_is_internal

section Version1

/-- Isometry from an inner product space `E` to the direct sum of the eigenspaces of some
self-adjoint operator `T` on `E`. -/
noncomputable def diagonalization : E ≃ₗᵢ[𝕜] PiLp 2 fun μ : Eigenvalues T => eigenspace T μ :=
  hT.direct_sum_is_internal.isometryL2OfOrthogonalFamily hT.orthogonalFamilyEigenspaces'
#align linear_map.is_symmetric.diagonalization LinearMap.IsSymmetric.diagonalization

@[simp]
theorem diagonalization_symm_apply (w : PiLp 2 fun μ : Eigenvalues T => eigenspace T μ) :
    hT.diagonalization.symm w = ∑ μ, w μ :=
  hT.direct_sum_is_internal.isometry_L2_of_orthogonal_family_symm_apply
    hT.orthogonalFamilyEigenspaces' w
#align
  linear_map.is_symmetric.diagonalization_symm_apply LinearMap.IsSymmetric.diagonalization_symm_apply

/-- *Diagonalization theorem*, *spectral theorem*; version 1: A self-adjoint operator `T` on a
finite-dimensional inner product space `E` acts diagonally on the decomposition of `E` into the
direct sum of the eigenspaces of `T`. -/
theorem diagonalization_apply_self_apply (v : E) (μ : Eigenvalues T) :
    hT.diagonalization (T v) μ = (μ : 𝕜) • hT.diagonalization v μ :=
  by
  suffices
    ∀ w : PiLp 2 fun μ : eigenvalues T => eigenspace T μ,
      T (hT.diagonalization.symm w) = hT.diagonalization.symm fun μ => (μ : 𝕜) • w μ
    by
    simpa [LinearIsometryEquiv.symm_apply_apply, -is_symmetric.diagonalization_symm_apply] using
      congr_arg (fun w => hT.diagonalization w μ) (this (hT.diagonalization v))
  intro w
  have hwT : ∀ μ : eigenvalues T, T (w μ) = (μ : 𝕜) • w μ :=
    by
    intro μ
    simpa [mem_eigenspace_iff] using (w μ).Prop
  simp [hwT]
#align
  linear_map.is_symmetric.diagonalization_apply_self_apply LinearMap.IsSymmetric.diagonalization_apply_self_apply

end Version1

section Version2

variable {n : ℕ} (hn : FiniteDimensional.finrank 𝕜 E = n)

/-- A choice of orthonormal basis of eigenvectors for self-adjoint operator `T` on a
finite-dimensional inner product space `E`.

TODO Postcompose with a permutation so that these eigenvectors are listed in increasing order of
eigenvalue. -/
noncomputable def eigenvectorBasis : OrthonormalBasis (Fin n) 𝕜 E :=
  hT.direct_sum_is_internal.subordinateOrthonormalBasis hn hT.orthogonalFamilyEigenspaces'
#align linear_map.is_symmetric.eigenvector_basis LinearMap.IsSymmetric.eigenvectorBasis

/-- The sequence of real eigenvalues associated to the standard orthonormal basis of eigenvectors
for a self-adjoint operator `T` on `E`.

TODO Postcompose with a permutation so that these eigenvalues are listed in increasing order. -/
noncomputable def eigenvalues (i : Fin n) : ℝ :=
  @IsROrC.re 𝕜 _ <|
    hT.direct_sum_is_internal.subordinateOrthonormalBasisIndex hn i hT.orthogonalFamilyEigenspaces'
#align linear_map.is_symmetric.eigenvalues LinearMap.IsSymmetric.eigenvalues

theorem has_eigenvector_eigenvector_basis (i : Fin n) :
    HasEigenvector T (hT.Eigenvalues hn i) (hT.eigenvectorBasis hn i) :=
  by
  let v : E := hT.eigenvector_basis hn i
  let μ : 𝕜 :=
    hT.direct_sum_is_internal.subordinate_orthonormal_basis_index hn i
      hT.orthogonal_family_eigenspaces'
  change has_eigenvector T (IsROrC.re μ) v
  have key : has_eigenvector T μ v :=
    by
    have H₁ : v ∈ eigenspace T μ :=
      hT.direct_sum_is_internal.subordinate_orthonormal_basis_subordinate hn i
        hT.orthogonal_family_eigenspaces'
    have H₂ : v ≠ 0 := by simpa using (hT.eigenvector_basis hn).toBasis.NeZero i
    exact ⟨H₁, H₂⟩
  have re_μ : ↑(IsROrC.re μ) = μ := by
    rw [← IsROrC.eq_conj_iff_re]
    exact hT.conj_eigenvalue_eq_self (has_eigenvalue_of_has_eigenvector key)
  simpa [re_μ] using key
#align
  linear_map.is_symmetric.has_eigenvector_eigenvector_basis LinearMap.IsSymmetric.has_eigenvector_eigenvector_basis

theorem has_eigenvalue_eigenvalues (i : Fin n) : HasEigenvalue T (hT.Eigenvalues hn i) :=
  Module.EndCat.has_eigenvalue_of_has_eigenvector (hT.has_eigenvector_eigenvector_basis hn i)
#align
  linear_map.is_symmetric.has_eigenvalue_eigenvalues LinearMap.IsSymmetric.has_eigenvalue_eigenvalues

@[simp]
theorem apply_eigenvector_basis (i : Fin n) :
    T (hT.eigenvectorBasis hn i) = (hT.Eigenvalues hn i : 𝕜) • hT.eigenvectorBasis hn i :=
  mem_eigenspace_iff.mp (hT.has_eigenvector_eigenvector_basis hn i).1
#align linear_map.is_symmetric.apply_eigenvector_basis LinearMap.IsSymmetric.apply_eigenvector_basis

/-- *Diagonalization theorem*, *spectral theorem*; version 2: A self-adjoint operator `T` on a
finite-dimensional inner product space `E` acts diagonally on the identification of `E` with
Euclidean space induced by an orthonormal basis of eigenvectors of `T`. -/
theorem diagonalization_basis_apply_self_apply (v : E) (i : Fin n) :
    (hT.eigenvectorBasis hn).repr (T v) i =
      hT.Eigenvalues hn i * (hT.eigenvectorBasis hn).repr v i :=
  by
  suffices
    ∀ w : EuclideanSpace 𝕜 (Fin n),
      T ((hT.eigenvector_basis hn).repr.symm w) =
        (hT.eigenvector_basis hn).repr.symm fun i => hT.eigenvalues hn i * w i
    by
    simpa [OrthonormalBasis.sum_repr_symm] using
      congr_arg (fun v => (hT.eigenvector_basis hn).repr v i)
        (this ((hT.eigenvector_basis hn).repr v))
  intro w
  simp_rw [← OrthonormalBasis.sum_repr_symm, LinearMap.map_sum, LinearMap.map_smul,
    apply_eigenvector_basis]
  apply Fintype.sum_congr
  intro a
  rw [smul_smul, mul_comm]
#align
  linear_map.is_symmetric.diagonalization_basis_apply_self_apply LinearMap.IsSymmetric.diagonalization_basis_apply_self_apply

end Version2

end IsSymmetric

end LinearMap

section Nonneg

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `inner_product_apply_eigenvector [])
      (Command.declSig
       [(Term.implicitBinder "{" [`μ] [":" `𝕜] "}")
        (Term.implicitBinder "{" [`v] [":" `E] "}")
        (Term.implicitBinder
         "{"
         [`T]
         [":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `E " →ₗ[" `𝕜 "] " `E)]
         "}")
        (Term.explicitBinder
         "("
         [`h]
         [":" («term_∈_» `v "∈" (Term.app `Module.EndCat.eigenspace [`T `μ]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Analysis.InnerProductSpace.Spectrum.«term⟪_,_⟫» "⟪" `v ", " (Term.app `T [`v]) "⟫")
         "="
         («term_*_»
          `μ
          "*"
          («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖") "^" (num "2"))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] (Term.app `mem_eigenspace_iff.mp [`h]))
              ","
              (Tactic.simpLemma [] [] `inner_smul_right)
              ","
              (Tactic.simpLemma [] [] `inner_self_eq_norm_sq_to_K)]
             "]"]
            [])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] (Term.app `mem_eigenspace_iff.mp [`h]))
             ","
             (Tactic.simpLemma [] [] `inner_smul_right)
             ","
             (Tactic.simpLemma [] [] `inner_self_eq_norm_sq_to_K)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] (Term.app `mem_eigenspace_iff.mp [`h]))
         ","
         (Tactic.simpLemma [] [] `inner_smul_right)
         ","
         (Tactic.simpLemma [] [] `inner_self_eq_norm_sq_to_K)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_self_eq_norm_sq_to_K
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_smul_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mem_eigenspace_iff.mp [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mem_eigenspace_iff.mp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Analysis.InnerProductSpace.Spectrum.«term⟪_,_⟫» "⟪" `v ", " (Term.app `T [`v]) "⟫")
       "="
       («term_*_»
        `μ
        "*"
        («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖") "^" (num "2"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       `μ
       "*"
       («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖") "^" (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖") "^" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `v
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.InnerProductSpace.Spectrum.«term⟪_,_⟫» "⟪" `v ", " (Term.app `T [`v]) "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Spectrum.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Spectrum.term⟪_,_⟫._@.Analysis.InnerProductSpace.Spectrum._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    inner_product_apply_eigenvector
    { μ : 𝕜 } { v : E } { T : E →ₗ[ 𝕜 ] E } ( h : v ∈ Module.EndCat.eigenspace T μ )
      : ⟪ v , T v ⟫ = μ * ‖ v ‖ ^ 2
    := by simp only [ mem_eigenspace_iff.mp h , inner_smul_right , inner_self_eq_norm_sq_to_K ]
#align inner_product_apply_eigenvector inner_product_apply_eigenvector

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `eigenvalue_nonneg_of_nonneg [])
      (Command.declSig
       [(Term.implicitBinder "{" [`μ] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
        (Term.implicitBinder
         "{"
         [`T]
         [":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `E " →ₗ[" `𝕜 "] " `E)]
         "}")
        (Term.explicitBinder "(" [`hμ] [":" (Term.app `HasEigenvalue [`T `μ])] [] ")")
        (Term.explicitBinder
         "("
         [`hnn]
         [":"
          (Term.forall
           "∀"
           [`x]
           [(Term.typeSpec ":" `E)]
           ","
           («term_≤_»
            (num "0")
            "≤"
            (Term.app
             `IsROrC.re
             [(Analysis.InnerProductSpace.Spectrum.«term⟪_,_⟫»
               "⟪"
               `x
               ", "
               (Term.app `T [`x])
               "⟫")])))]
         []
         ")")]
       (Term.typeSpec ":" («term_≤_» (num "0") "≤" `μ)))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `v)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hv)])
                  [])]
                "⟩")])]
            []
            [":=" [`hμ.exists_has_eigenvector]])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hpos []]
              [(Term.typeSpec
                ":"
                («term_<_»
                 (num "0")
                 "<"
                 («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖") "^" (num "2"))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.Simpa.simpa
                   "simpa"
                   []
                   []
                   (Std.Tactic.Simpa.simpaArgsRest
                    []
                    []
                    ["only"]
                    [(Tactic.simpArgs
                      "["
                      [(Tactic.simpLemma [] [] `sq_pos_iff)
                       ","
                       (Tactic.simpLemma [] [] `norm_ne_zero_iff)]
                      "]")]
                    ["using" (Term.proj `hv "." (fieldIdx "2"))]))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Term.app
                  `IsROrC.re
                  [(Analysis.InnerProductSpace.Spectrum.«term⟪_,_⟫»
                    "⟪"
                    `v
                    ", "
                    (Term.app `T [`v])
                    "⟫")])
                 "="
                 («term_*_»
                  `μ
                  "*"
                  («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖") "^" (num "2")))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.NormCast.tacticExact_mod_cast_
                   "exact_mod_cast"
                   (Term.app
                    `congr_arg
                    [`IsROrC.re
                     (Term.app
                      `inner_product_apply_eigenvector
                      [(Term.proj `hv "." (fieldIdx "1"))])]))]))))))
           []
           (Tactic.exact
            "exact"
            (Term.app
             (Term.proj (Term.app `zero_le_mul_right [`hpos]) "." `mp)
             [(Term.subst `this "▸" [(Term.app `hnn [`v])])]))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `v)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hv)])
                 [])]
               "⟩")])]
           []
           [":=" [`hμ.exists_has_eigenvector]])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hpos []]
             [(Term.typeSpec
               ":"
               («term_<_»
                (num "0")
                "<"
                («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖") "^" (num "2"))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.Simpa.simpa
                  "simpa"
                  []
                  []
                  (Std.Tactic.Simpa.simpaArgsRest
                   []
                   []
                   ["only"]
                   [(Tactic.simpArgs
                     "["
                     [(Tactic.simpLemma [] [] `sq_pos_iff)
                      ","
                      (Tactic.simpLemma [] [] `norm_ne_zero_iff)]
                     "]")]
                   ["using" (Term.proj `hv "." (fieldIdx "2"))]))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.app
                 `IsROrC.re
                 [(Analysis.InnerProductSpace.Spectrum.«term⟪_,_⟫»
                   "⟪"
                   `v
                   ", "
                   (Term.app `T [`v])
                   "⟫")])
                "="
                («term_*_»
                 `μ
                 "*"
                 («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖") "^" (num "2")))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.NormCast.tacticExact_mod_cast_
                  "exact_mod_cast"
                  (Term.app
                   `congr_arg
                   [`IsROrC.re
                    (Term.app
                     `inner_product_apply_eigenvector
                     [(Term.proj `hv "." (fieldIdx "1"))])]))]))))))
          []
          (Tactic.exact
           "exact"
           (Term.app
            (Term.proj (Term.app `zero_le_mul_right [`hpos]) "." `mp)
            [(Term.subst `this "▸" [(Term.app `hnn [`v])])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj (Term.app `zero_le_mul_right [`hpos]) "." `mp)
        [(Term.subst `this "▸" [(Term.app `hnn [`v])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `zero_le_mul_right [`hpos]) "." `mp)
       [(Term.subst `this "▸" [(Term.app `hnn [`v])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.subst', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.subst', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.subst `this "▸" [(Term.app `hnn [`v])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hnn [`v])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `v
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hnn
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.subst `this "▸" [(Term.app `hnn [`v])])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `zero_le_mul_right [`hpos]) "." `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `zero_le_mul_right [`hpos])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hpos
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zero_le_mul_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `zero_le_mul_right [`hpos])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_=_»
            (Term.app
             `IsROrC.re
             [(Analysis.InnerProductSpace.Spectrum.«term⟪_,_⟫» "⟪" `v ", " (Term.app `T [`v]) "⟫")])
            "="
            («term_*_»
             `μ
             "*"
             («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖") "^" (num "2")))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.NormCast.tacticExact_mod_cast_
              "exact_mod_cast"
              (Term.app
               `congr_arg
               [`IsROrC.re
                (Term.app
                 `inner_product_apply_eigenvector
                 [(Term.proj `hv "." (fieldIdx "1"))])]))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.NormCast.tacticExact_mod_cast_
           "exact_mod_cast"
           (Term.app
            `congr_arg
            [`IsROrC.re
             (Term.app `inner_product_apply_eigenvector [(Term.proj `hv "." (fieldIdx "1"))])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.NormCast.tacticExact_mod_cast_
       "exact_mod_cast"
       (Term.app
        `congr_arg
        [`IsROrC.re
         (Term.app `inner_product_apply_eigenvector [(Term.proj `hv "." (fieldIdx "1"))])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `congr_arg
       [`IsROrC.re
        (Term.app `inner_product_apply_eigenvector [(Term.proj `hv "." (fieldIdx "1"))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `inner_product_apply_eigenvector [(Term.proj `hv "." (fieldIdx "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `hv "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inner_product_apply_eigenvector
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `inner_product_apply_eigenvector [(Term.proj `hv "." (fieldIdx "1"))])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `IsROrC.re
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_arg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app
        `IsROrC.re
        [(Analysis.InnerProductSpace.Spectrum.«term⟪_,_⟫» "⟪" `v ", " (Term.app `T [`v]) "⟫")])
       "="
       («term_*_»
        `μ
        "*"
        («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖") "^" (num "2"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       `μ
       "*"
       («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖") "^" (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖") "^" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `v
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `IsROrC.re
       [(Analysis.InnerProductSpace.Spectrum.«term⟪_,_⟫» "⟪" `v ", " (Term.app `T [`v]) "⟫")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Spectrum.«term⟪_,_⟫»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Spectrum.«term⟪_,_⟫»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Spectrum.«term⟪_,_⟫» "⟪" `v ", " (Term.app `T [`v]) "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Spectrum.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Spectrum.term⟪_,_⟫._@.Analysis.InnerProductSpace.Spectrum._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  eigenvalue_nonneg_of_nonneg
  { μ : ℝ }
      { T : E →ₗ[ 𝕜 ] E }
      ( hμ : HasEigenvalue T μ )
      ( hnn : ∀ x : E , 0 ≤ IsROrC.re ⟪ x , T x ⟫ )
    : 0 ≤ μ
  :=
    by
      obtain ⟨ v , hv ⟩ := hμ.exists_has_eigenvector
        have hpos : 0 < ‖ v ‖ ^ 2 := by simpa only [ sq_pos_iff , norm_ne_zero_iff ] using hv . 2
        have
          : IsROrC.re ⟪ v , T v ⟫ = μ * ‖ v ‖ ^ 2
            :=
            by exact_mod_cast congr_arg IsROrC.re inner_product_apply_eigenvector hv . 1
        exact zero_le_mul_right hpos . mp this ▸ hnn v
#align eigenvalue_nonneg_of_nonneg eigenvalue_nonneg_of_nonneg

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `eigenvalue_pos_of_pos [])
      (Command.declSig
       [(Term.implicitBinder "{" [`μ] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
        (Term.implicitBinder
         "{"
         [`T]
         [":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `E " →ₗ[" `𝕜 "] " `E)]
         "}")
        (Term.explicitBinder "(" [`hμ] [":" (Term.app `HasEigenvalue [`T `μ])] [] ")")
        (Term.explicitBinder
         "("
         [`hnn]
         [":"
          (Term.forall
           "∀"
           [`x]
           [(Term.typeSpec ":" `E)]
           ","
           («term_<_»
            (num "0")
            "<"
            (Term.app
             `IsROrC.re
             [(Analysis.InnerProductSpace.Spectrum.«term⟪_,_⟫»
               "⟪"
               `x
               ", "
               (Term.app `T [`x])
               "⟫")])))]
         []
         ")")]
       (Term.typeSpec ":" («term_<_» (num "0") "<" `μ)))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `v)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hv)])
                  [])]
                "⟩")])]
            []
            [":=" [`hμ.exists_has_eigenvector]])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hpos []]
              [(Term.typeSpec
                ":"
                («term_<_»
                 (num "0")
                 "<"
                 («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖") "^" (num "2"))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.Simpa.simpa
                   "simpa"
                   []
                   []
                   (Std.Tactic.Simpa.simpaArgsRest
                    []
                    []
                    ["only"]
                    [(Tactic.simpArgs
                      "["
                      [(Tactic.simpLemma [] [] `sq_pos_iff)
                       ","
                       (Tactic.simpLemma [] [] `norm_ne_zero_iff)]
                      "]")]
                    ["using" (Term.proj `hv "." (fieldIdx "2"))]))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Term.app
                  `IsROrC.re
                  [(Analysis.InnerProductSpace.Spectrum.«term⟪_,_⟫»
                    "⟪"
                    `v
                    ", "
                    (Term.app `T [`v])
                    "⟫")])
                 "="
                 («term_*_»
                  `μ
                  "*"
                  («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖") "^" (num "2")))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.NormCast.tacticExact_mod_cast_
                   "exact_mod_cast"
                   (Term.app
                    `congr_arg
                    [`IsROrC.re
                     (Term.app
                      `inner_product_apply_eigenvector
                      [(Term.proj `hv "." (fieldIdx "1"))])]))]))))))
           []
           (Tactic.exact
            "exact"
            (Term.app
             (Term.proj (Term.app `zero_lt_mul_right [`hpos]) "." `mp)
             [(Term.subst `this "▸" [(Term.app `hnn [`v])])]))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `v)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hv)])
                 [])]
               "⟩")])]
           []
           [":=" [`hμ.exists_has_eigenvector]])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hpos []]
             [(Term.typeSpec
               ":"
               («term_<_»
                (num "0")
                "<"
                («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖") "^" (num "2"))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.Simpa.simpa
                  "simpa"
                  []
                  []
                  (Std.Tactic.Simpa.simpaArgsRest
                   []
                   []
                   ["only"]
                   [(Tactic.simpArgs
                     "["
                     [(Tactic.simpLemma [] [] `sq_pos_iff)
                      ","
                      (Tactic.simpLemma [] [] `norm_ne_zero_iff)]
                     "]")]
                   ["using" (Term.proj `hv "." (fieldIdx "2"))]))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.app
                 `IsROrC.re
                 [(Analysis.InnerProductSpace.Spectrum.«term⟪_,_⟫»
                   "⟪"
                   `v
                   ", "
                   (Term.app `T [`v])
                   "⟫")])
                "="
                («term_*_»
                 `μ
                 "*"
                 («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖") "^" (num "2")))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.NormCast.tacticExact_mod_cast_
                  "exact_mod_cast"
                  (Term.app
                   `congr_arg
                   [`IsROrC.re
                    (Term.app
                     `inner_product_apply_eigenvector
                     [(Term.proj `hv "." (fieldIdx "1"))])]))]))))))
          []
          (Tactic.exact
           "exact"
           (Term.app
            (Term.proj (Term.app `zero_lt_mul_right [`hpos]) "." `mp)
            [(Term.subst `this "▸" [(Term.app `hnn [`v])])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj (Term.app `zero_lt_mul_right [`hpos]) "." `mp)
        [(Term.subst `this "▸" [(Term.app `hnn [`v])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `zero_lt_mul_right [`hpos]) "." `mp)
       [(Term.subst `this "▸" [(Term.app `hnn [`v])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.subst', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.subst', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.subst `this "▸" [(Term.app `hnn [`v])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hnn [`v])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `v
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hnn
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.subst `this "▸" [(Term.app `hnn [`v])])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `zero_lt_mul_right [`hpos]) "." `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `zero_lt_mul_right [`hpos])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hpos
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zero_lt_mul_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `zero_lt_mul_right [`hpos])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_=_»
            (Term.app
             `IsROrC.re
             [(Analysis.InnerProductSpace.Spectrum.«term⟪_,_⟫» "⟪" `v ", " (Term.app `T [`v]) "⟫")])
            "="
            («term_*_»
             `μ
             "*"
             («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖") "^" (num "2")))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.NormCast.tacticExact_mod_cast_
              "exact_mod_cast"
              (Term.app
               `congr_arg
               [`IsROrC.re
                (Term.app
                 `inner_product_apply_eigenvector
                 [(Term.proj `hv "." (fieldIdx "1"))])]))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.NormCast.tacticExact_mod_cast_
           "exact_mod_cast"
           (Term.app
            `congr_arg
            [`IsROrC.re
             (Term.app `inner_product_apply_eigenvector [(Term.proj `hv "." (fieldIdx "1"))])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.NormCast.tacticExact_mod_cast_
       "exact_mod_cast"
       (Term.app
        `congr_arg
        [`IsROrC.re
         (Term.app `inner_product_apply_eigenvector [(Term.proj `hv "." (fieldIdx "1"))])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `congr_arg
       [`IsROrC.re
        (Term.app `inner_product_apply_eigenvector [(Term.proj `hv "." (fieldIdx "1"))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `inner_product_apply_eigenvector [(Term.proj `hv "." (fieldIdx "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `hv "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inner_product_apply_eigenvector
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `inner_product_apply_eigenvector [(Term.proj `hv "." (fieldIdx "1"))])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `IsROrC.re
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_arg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app
        `IsROrC.re
        [(Analysis.InnerProductSpace.Spectrum.«term⟪_,_⟫» "⟪" `v ", " (Term.app `T [`v]) "⟫")])
       "="
       («term_*_»
        `μ
        "*"
        («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖") "^" (num "2"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       `μ
       "*"
       («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖") "^" (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖") "^" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `v "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `v
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `μ
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `IsROrC.re
       [(Analysis.InnerProductSpace.Spectrum.«term⟪_,_⟫» "⟪" `v ", " (Term.app `T [`v]) "⟫")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Spectrum.«term⟪_,_⟫»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Spectrum.«term⟪_,_⟫»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Spectrum.«term⟪_,_⟫» "⟪" `v ", " (Term.app `T [`v]) "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Spectrum.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Spectrum.term⟪_,_⟫._@.Analysis.InnerProductSpace.Spectrum._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  eigenvalue_pos_of_pos
  { μ : ℝ }
      { T : E →ₗ[ 𝕜 ] E }
      ( hμ : HasEigenvalue T μ )
      ( hnn : ∀ x : E , 0 < IsROrC.re ⟪ x , T x ⟫ )
    : 0 < μ
  :=
    by
      obtain ⟨ v , hv ⟩ := hμ.exists_has_eigenvector
        have hpos : 0 < ‖ v ‖ ^ 2 := by simpa only [ sq_pos_iff , norm_ne_zero_iff ] using hv . 2
        have
          : IsROrC.re ⟪ v , T v ⟫ = μ * ‖ v ‖ ^ 2
            :=
            by exact_mod_cast congr_arg IsROrC.re inner_product_apply_eigenvector hv . 1
        exact zero_lt_mul_right hpos . mp this ▸ hnn v
#align eigenvalue_pos_of_pos eigenvalue_pos_of_pos

end Nonneg

