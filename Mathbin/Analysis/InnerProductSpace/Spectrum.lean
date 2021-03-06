/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
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


variable {???? : Type _} [IsROrC ????] [dec_???? : DecidableEq ????]

variable {E : Type _} [InnerProductSpace ???? E]

-- mathport name: ??expr??? , ?????
local notation "???" x ", " y "???" => @inner ???? E _ x y

open BigOperators ComplexConjugate

open Module.End

namespace InnerProductSpace

namespace IsSelfAdjoint

variable {T : E ??????[????] E} (hT : IsSelfAdjoint T)

include hT

/-- A self-adjoint operator preserves orthogonal complements of its eigenspaces. -/
theorem invariant_orthogonal_eigenspace (?? : ????) (v : E) (hv : v ??? (eigenspace T ??)???) : T v ??? (eigenspace T ??)??? := by
  intro w hw
  have : T w = (?? : ????) ??? w := by
    rwa [mem_eigenspace_iff] at hw
  simp [hT w, ??? this, ??? inner_smul_left, ??? hv w hw]

/-- The eigenvalues of a self-adjoint operator are real. -/
theorem conj_eigenvalue_eq_self {?? : ????} (h?? : HasEigenvalue T ??) : conj ?? = ?? := by
  obtain ???v, hv???, hv?????? := h??.exists_has_eigenvector
  rw [mem_eigenspace_iff] at hv???
  simpa [??? hv???, ??? inner_smul_left, ??? inner_smul_right, ??? hv???] using hT v v

/-- The eigenspaces of a self-adjoint operator are mutually orthogonal. -/
theorem orthogonal_family_eigenspaces :
    @OrthogonalFamily ???? _ _ _ _ (fun ?? => eigenspace T ??) _ fun ?? => (eigenspace T ??).subtype?????? := by
  rintro ?? ?? h???? ???v, hv??? ???w, hw???
  by_cases' hv' : v = 0
  ?? simp [??? hv']
    
  have H := hT.conj_eigenvalue_eq_self (has_eigenvalue_of_has_eigenvector ???hv, hv'???)
  rw [mem_eigenspace_iff] at hv hw
  refine' Or.resolve_left _ h????.symm
  simpa [??? inner_smul_left, ??? inner_smul_right, ??? hv, ??? hw, ??? H] using (hT v w).symm

theorem orthogonal_family_eigenspaces' :
    @OrthogonalFamily ???? _ _ _ _ (fun ?? : Eigenvalues T => eigenspace T ??) _ fun ?? => (eigenspace T ??).subtype?????? :=
  hT.orthogonal_family_eigenspaces.comp Subtype.coe_injective

/-- The mutual orthogonal complement of the eigenspaces of a self-adjoint operator on an inner
product space is an invariant subspace of the operator. -/
theorem orthogonal_supr_eigenspaces_invariant ???v : E??? (hv : v ??? (??? ??, eigenspace T ??)???) :
    T v ??? (??? ??, eigenspace T ??)??? := by
  rw [??? Submodule.infi_orthogonal] at hv???
  exact T.infi_invariant hT.invariant_orthogonal_eigenspace v hv

/-- The mutual orthogonal complement of the eigenspaces of a self-adjoint operator on an inner
product space has no eigenvalues. -/
theorem orthogonal_supr_eigenspaces (?? : ????) : eigenspace (T.restrict hT.orthogonal_supr_eigenspaces_invariant) ?? = ??? :=
  by
  set p : Submodule ???? E := (??? ??, eigenspace T ??)???
  refine' eigenspace_restrict_eq_bot hT.orthogonal_supr_eigenspaces_invariant _
  have H??? : p ??? (eigenspace T ??)??? := Submodule.orthogonal_le (le_supr _ _)
  exact (eigenspace T ??).orthogonal_disjoint.mono_right H???

/-! ### Finite-dimensional theory -/


variable [FiniteDimensional ???? E]

/-- The mutual orthogonal complement of the eigenspaces of a self-adjoint operator on a
finite-dimensional inner product space is trivial. -/
theorem orthogonal_supr_eigenspaces_eq_bot : (??? ??, eigenspace T ??)??? = ??? := by
  have hT' : is_self_adjoint _ := hT.restrict_invariant hT.orthogonal_supr_eigenspaces_invariant
  -- a self-adjoint operator on a nontrivial inner product space has an eigenvalue
  have := hT'.subsingleton_of_no_eigenvalue_finite_dimensional hT.orthogonal_supr_eigenspaces
  exact Submodule.eq_bot_of_subsingleton _

theorem orthogonal_supr_eigenspaces_eq_bot' : (??? ?? : Eigenvalues T, eigenspace T ??)??? = ??? :=
  show (??? ?? : { ?? // eigenspace T ?? ??? ??? }, eigenspace T ??)??? = ??? by
    rw [supr_ne_bot_subtype, hT.orthogonal_supr_eigenspaces_eq_bot]

include dec_????

/-- The eigenspaces of a self-adjoint operator on a finite-dimensional inner product space `E` give
an internal direct sum decomposition of `E`. -/
theorem direct_sum_is_internal : DirectSum.IsInternal fun ?? : Eigenvalues T => eigenspace T ?? :=
  hT.orthogonal_family_eigenspaces'.is_internal_iff.mpr hT.orthogonal_supr_eigenspaces_eq_bot'

section Version1

/-- Isometry from an inner product space `E` to the direct sum of the eigenspaces of some
self-adjoint operator `T` on `E`. -/
noncomputable def diagonalization : E ?????????[????] PiLp 2 fun ?? : Eigenvalues T => eigenspace T ?? :=
  hT.direct_sum_is_internal.isometryL2OfOrthogonalFamily hT.orthogonal_family_eigenspaces'

@[simp]
theorem diagonalization_symm_apply (w : PiLp 2 fun ?? : Eigenvalues T => eigenspace T ??) :
    hT.diagonalization.symm w = ??? ??, w ?? :=
  hT.direct_sum_is_internal.isometry_L2_of_orthogonal_family_symm_apply hT.orthogonal_family_eigenspaces' w

/-- *Diagonalization theorem*, *spectral theorem*; version 1: A self-adjoint operator `T` on a
finite-dimensional inner product space `E` acts diagonally on the decomposition of `E` into the
direct sum of the eigenspaces of `T`. -/
theorem diagonalization_apply_self_apply (v : E) (?? : Eigenvalues T) :
    hT.diagonalization (T v) ?? = (?? : ????) ??? hT.diagonalization v ?? := by
  suffices
    ??? w : PiLp 2 fun ?? : eigenvalues T => eigenspace T ??,
      T (hT.diagonalization.symm w) = hT.diagonalization.symm fun ?? => (?? : ????) ??? w ??
    by
    simpa [??? LinearIsometryEquiv.symm_apply_apply, -is_self_adjoint.diagonalization_symm_apply] using
      congr_arg (fun w => hT.diagonalization w ??) (this (hT.diagonalization v))
  intro w
  have hwT : ??? ?? : eigenvalues T, T (w ??) = (?? : ????) ??? w ?? := by
    intro ??
    simpa [??? mem_eigenspace_iff] using (w ??).Prop
  simp [??? hwT]

end Version1

section Version2

variable {n : ???} (hn : FiniteDimensional.finrank ???? E = n)

/-- A choice of orthonormal basis of eigenvectors for self-adjoint operator `T` on a
finite-dimensional inner product space `E`.

TODO Postcompose with a permutation so that these eigenvectors are listed in increasing order of
eigenvalue. -/
noncomputable def eigenvectorBasis : OrthonormalBasis (Fin??? n) ???? E :=
  hT.direct_sum_is_internal.subordinateOrthonormalBasis hn hT.orthogonal_family_eigenspaces'

/-- The sequence of real eigenvalues associated to the standard orthonormal basis of eigenvectors
for a self-adjoint operator `T` on `E`.

TODO Postcompose with a permutation so that these eigenvalues are listed in increasing order. -/
noncomputable def eigenvalues (i : Fin??? n) : ??? :=
  @IsROrC.re ???? _ <| hT.direct_sum_is_internal.subordinateOrthonormalBasisIndex hn i hT.orthogonal_family_eigenspaces'

theorem has_eigenvector_eigenvector_basis (i : Fin??? n) :
    HasEigenvector T (hT.Eigenvalues hn i) (hT.eigenvectorBasis hn i) := by
  let v : E := hT.eigenvector_basis hn i
  let ?? : ???? := hT.direct_sum_is_internal.subordinate_orthonormal_basis_index hn i hT.orthogonal_family_eigenspaces'
  change has_eigenvector T (IsROrC.re ??) v
  have key : has_eigenvector T ?? v := by
    have H??? : v ??? eigenspace T ?? :=
      hT.direct_sum_is_internal.subordinate_orthonormal_basis_subordinate hn i hT.orthogonal_family_eigenspaces'
    have H??? : v ??? 0 := by
      simpa using (hT.eigenvector_basis hn).toBasis.ne_zero i
    exact ???H???, H??????
  have re_?? : ???(IsROrC.re ??) = ?? := by
    rw [??? IsROrC.eq_conj_iff_re]
    exact hT.conj_eigenvalue_eq_self (has_eigenvalue_of_has_eigenvector key)
  simpa [??? re_??] using key

theorem has_eigenvalue_eigenvalues (i : Fin??? n) : HasEigenvalue T (hT.Eigenvalues hn i) :=
  Module.End.has_eigenvalue_of_has_eigenvector (hT.has_eigenvector_eigenvector_basis hn i)

@[simp]
theorem apply_eigenvector_basis (i : Fin??? n) :
    T (hT.eigenvectorBasis hn i) = (hT.Eigenvalues hn i : ????) ??? hT.eigenvectorBasis hn i :=
  mem_eigenspace_iff.mp (hT.has_eigenvector_eigenvector_basis hn i).1

/-- *Diagonalization theorem*, *spectral theorem*; version 2: A self-adjoint operator `T` on a
finite-dimensional inner product space `E` acts diagonally on the identification of `E` with
Euclidean space induced by an orthonormal basis of eigenvectors of `T`. -/
theorem diagonalization_basis_apply_self_apply (v : E) (i : Fin??? n) :
    (hT.eigenvectorBasis hn).repr (T v) i = hT.Eigenvalues hn i * (hT.eigenvectorBasis hn).repr v i := by
  suffices
    ??? w : EuclideanSpace ???? (Fin??? n),
      T ((hT.eigenvector_basis hn).repr.symm w) = (hT.eigenvector_basis hn).repr.symm fun i => hT.eigenvalues hn i * w i
    by
    simpa [??? OrthonormalBasis.sum_repr_symm] using
      congr_arg (fun v => (hT.eigenvector_basis hn).repr v i) (this ((hT.eigenvector_basis hn).repr v))
  intro w
  simp_rw [??? OrthonormalBasis.sum_repr_symm, LinearMap.map_sum, LinearMap.map_smul, apply_eigenvector_basis]
  apply Fintype.sum_congr
  intro a
  rw [smul_smul, mul_comm]

end Version2

end IsSelfAdjoint

end InnerProductSpace

section Nonneg

@[simp]
theorem inner_product_apply_eigenvector {?? : ????} {v : E} {T : E ??????[????] E} (h : v ??? Module.End.eigenspace T ??) :
    ???v, T v??? = ?? * ???v??? ^ 2 := by
  simp only [??? mem_eigenspace_iff.mp h, ??? inner_smul_right, ??? inner_self_eq_norm_sq_to_K]

theorem eigenvalue_nonneg_of_nonneg {?? : ???} {T : E ??????[????] E} (h?? : HasEigenvalue T ??)
    (hnn : ??? x : E, 0 ??? IsROrC.re ???x, T x???) : 0 ??? ?? := by
  obtain ???v, hv??? := h??.exists_has_eigenvector
  have hpos : 0 < ???v??? ^ 2 := by
    simpa only [??? sq_pos_iff, ??? norm_ne_zero_iff] using hv.2
  have : IsROrC.re ???v, T v??? = ?? * ???v??? ^ 2 := by
    exact_mod_cast congr_arg IsROrC.re (inner_product_apply_eigenvector hv.1)
  exact (zero_le_mul_right hpos).mp (this ??? hnn v)

theorem eigenvalue_pos_of_pos {?? : ???} {T : E ??????[????] E} (h?? : HasEigenvalue T ??) (hnn : ??? x : E, 0 < IsROrC.re ???x, T x???) :
    0 < ?? := by
  obtain ???v, hv??? := h??.exists_has_eigenvector
  have hpos : 0 < ???v??? ^ 2 := by
    simpa only [??? sq_pos_iff, ??? norm_ne_zero_iff] using hv.2
  have : IsROrC.re ???v, T v??? = ?? * ???v??? ^ 2 := by
    exact_mod_cast congr_arg IsROrC.re (inner_product_apply_eigenvector hv.1)
  exact (zero_lt_mul_right hpos).mp (this ??? hnn v)

end Nonneg

