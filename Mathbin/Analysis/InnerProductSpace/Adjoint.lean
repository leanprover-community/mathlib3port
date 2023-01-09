/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Heather Macbeth

! This file was ported from Lean 3 source module analysis.inner_product_space.adjoint
! leanprover-community/mathlib commit 40acfb6aa7516ffe6f91136691df012a64683390
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.InnerProductSpace.Dual
import Mathbin.Analysis.InnerProductSpace.PiL2

/-!
# Adjoint of operators on Hilbert spaces

Given an operator `A : E →L[𝕜] F`, where `E` and `F` are Hilbert spaces, its adjoint
`adjoint A : F →L[𝕜] E` is the unique operator such that `⟪x, A y⟫ = ⟪adjoint A x, y⟫` for all
`x` and `y`.

We then use this to put a C⋆-algebra structure on `E →L[𝕜] E` with the adjoint as the star
operation.

This construction is used to define an adjoint for linear maps (i.e. not continuous) between
finite dimensional spaces.

## Main definitions

* `continuous_linear_map.adjoint : (E →L[𝕜] F) ≃ₗᵢ⋆[𝕜] (F →L[𝕜] E)`: the adjoint of a continuous
  linear map, bundled as a conjugate-linear isometric equivalence.
* `linear_map.adjoint : (E →ₗ[𝕜] F) ≃ₗ⋆[𝕜] (F →ₗ[𝕜] E)`: the adjoint of a linear map between
  finite-dimensional spaces, this time only as a conjugate-linear equivalence, since there is no
  norm defined on these maps.

## Implementation notes

* The continuous conjugate-linear version `adjoint_aux` is only an intermediate
  definition and is not meant to be used outside this file.

## Tags

adjoint

-/


noncomputable section

open IsROrC

open ComplexConjugate

variable {𝕜 E F G : Type _} [IsROrC 𝕜]

variable [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] [InnerProductSpace 𝕜 G]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-! ### Adjoint operator -/


open InnerProductSpace

namespace ContinuousLinearMap

variable [CompleteSpace E] [CompleteSpace G]

/-- The adjoint, as a continuous conjugate-linear map.  This is only meant as an auxiliary
definition for the main definition `adjoint`, where this is bundled as a conjugate-linear isometric
equivalence. -/
def adjointAux : (E →L[𝕜] F) →L⋆[𝕜] F →L[𝕜] E :=
  (ContinuousLinearMap.compSL _ _ _ _ _ ((toDual 𝕜 E).symm : NormedSpace.Dual 𝕜 E →L⋆[𝕜] E)).comp
    (toSesqForm : (E →L[𝕜] F) →L[𝕜] F →L⋆[𝕜] NormedSpace.Dual 𝕜 E)
#align continuous_linear_map.adjoint_aux ContinuousLinearMap.adjointAux

@[simp]
theorem adjoint_aux_apply (A : E →L[𝕜] F) (x : F) :
    adjointAux A x = ((toDual 𝕜 E).symm : NormedSpace.Dual 𝕜 E → E) ((toSesqForm A) x) :=
  rfl
#align continuous_linear_map.adjoint_aux_apply ContinuousLinearMap.adjoint_aux_apply

theorem adjoint_aux_inner_left (A : E →L[𝕜] F) (x : E) (y : F) : ⟪adjointAux A y, x⟫ = ⟪y, A x⟫ :=
  by
  simp only [adjoint_aux_apply, to_dual_symm_apply, to_sesq_form_apply_coe, coe_comp',
    innerSL_apply_coe]
#align continuous_linear_map.adjoint_aux_inner_left ContinuousLinearMap.adjoint_aux_inner_left

theorem adjoint_aux_inner_right (A : E →L[𝕜] F) (x : E) (y : F) : ⟪x, adjointAux A y⟫ = ⟪A x, y⟫ :=
  by rw [← inner_conj_sym, adjoint_aux_inner_left, inner_conj_sym]
#align continuous_linear_map.adjoint_aux_inner_right ContinuousLinearMap.adjoint_aux_inner_right

variable [CompleteSpace F]

theorem adjoint_aux_adjoint_aux (A : E →L[𝕜] F) : adjointAux (adjointAux A) = A :=
  by
  ext v
  refine' ext_inner_left 𝕜 fun w => _
  rw [adjoint_aux_inner_right, adjoint_aux_inner_left]
#align continuous_linear_map.adjoint_aux_adjoint_aux ContinuousLinearMap.adjoint_aux_adjoint_aux

@[simp]
theorem adjoint_aux_norm (A : E →L[𝕜] F) : ‖adjointAux A‖ = ‖A‖ :=
  by
  refine' le_antisymm _ _
  · refine' ContinuousLinearMap.op_norm_le_bound _ (norm_nonneg _) fun x => _
    rw [adjoint_aux_apply, LinearIsometryEquiv.norm_map]
    exact to_sesq_form_apply_norm_le
  · nth_rw_lhs 1 [← adjoint_aux_adjoint_aux A]
    refine' ContinuousLinearMap.op_norm_le_bound _ (norm_nonneg _) fun x => _
    rw [adjoint_aux_apply, LinearIsometryEquiv.norm_map]
    exact to_sesq_form_apply_norm_le
#align continuous_linear_map.adjoint_aux_norm ContinuousLinearMap.adjoint_aux_norm

/-- The adjoint of a bounded operator from Hilbert space E to Hilbert space F. -/
def adjoint : (E →L[𝕜] F) ≃ₗᵢ⋆[𝕜] F →L[𝕜] E :=
  LinearIsometryEquiv.ofSurjective { adjointAux with norm_map' := adjoint_aux_norm } fun A =>
    ⟨adjointAux A, adjoint_aux_adjoint_aux A⟩
#align continuous_linear_map.adjoint ContinuousLinearMap.adjoint

-- mathport name: adjoint
scoped[InnerProduct] postfix:1000 "†" => ContinuousLinearMap.adjoint

/-- The fundamental property of the adjoint. -/
theorem adjoint_inner_left (A : E →L[𝕜] F) (x : E) (y : F) : ⟪(A†) y, x⟫ = ⟪y, A x⟫ :=
  adjoint_aux_inner_left A x y
#align continuous_linear_map.adjoint_inner_left ContinuousLinearMap.adjoint_inner_left

/-- The fundamental property of the adjoint. -/
theorem adjoint_inner_right (A : E →L[𝕜] F) (x : E) (y : F) : ⟪x, (A†) y⟫ = ⟪A x, y⟫ :=
  adjoint_aux_inner_right A x y
#align continuous_linear_map.adjoint_inner_right ContinuousLinearMap.adjoint_inner_right

/-- The adjoint is involutive -/
@[simp]
theorem adjoint_adjoint (A : E →L[𝕜] F) : A†† = A :=
  adjoint_aux_adjoint_aux A
#align continuous_linear_map.adjoint_adjoint ContinuousLinearMap.adjoint_adjoint

/-- The adjoint of the composition of two operators is the composition of the two adjoints
in reverse order. -/
@[simp]
theorem adjoint_comp (A : F →L[𝕜] G) (B : E →L[𝕜] F) : (A ∘L B)† = B† ∘L A† :=
  by
  ext v
  refine' ext_inner_left 𝕜 fun w => _
  simp only [adjoint_inner_right, ContinuousLinearMap.coe_comp', Function.comp_apply]
#align continuous_linear_map.adjoint_comp ContinuousLinearMap.adjoint_comp

theorem apply_norm_sq_eq_inner_adjoint_left (A : E →L[𝕜] E) (x : E) :
    ‖A x‖ ^ 2 = re ⟪(A† * A) x, x⟫ :=
  by
  have h : ⟪(A† * A) x, x⟫ = ⟪A x, A x⟫ :=
    by
    rw [← adjoint_inner_left]
    rfl
  rw [h, ← inner_self_eq_norm_sq _]
#align
  continuous_linear_map.apply_norm_sq_eq_inner_adjoint_left ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left

theorem apply_norm_eq_sqrt_inner_adjoint_left (A : E →L[𝕜] E) (x : E) :
    ‖A x‖ = Real.sqrt (re ⟪(A† * A) x, x⟫) := by
  rw [← apply_norm_sq_eq_inner_adjoint_left, Real.sqrt_sq (norm_nonneg _)]
#align
  continuous_linear_map.apply_norm_eq_sqrt_inner_adjoint_left ContinuousLinearMap.apply_norm_eq_sqrt_inner_adjoint_left

theorem apply_norm_sq_eq_inner_adjoint_right (A : E →L[𝕜] E) (x : E) :
    ‖A x‖ ^ 2 = re ⟪x, (A† * A) x⟫ :=
  by
  have h : ⟪x, (A† * A) x⟫ = ⟪A x, A x⟫ :=
    by
    rw [← adjoint_inner_right]
    rfl
  rw [h, ← inner_self_eq_norm_sq _]
#align
  continuous_linear_map.apply_norm_sq_eq_inner_adjoint_right ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right

theorem apply_norm_eq_sqrt_inner_adjoint_right (A : E →L[𝕜] E) (x : E) :
    ‖A x‖ = Real.sqrt (re ⟪x, (A† * A) x⟫) := by
  rw [← apply_norm_sq_eq_inner_adjoint_right, Real.sqrt_sq (norm_nonneg _)]
#align
  continuous_linear_map.apply_norm_eq_sqrt_inner_adjoint_right ContinuousLinearMap.apply_norm_eq_sqrt_inner_adjoint_right

/-- The adjoint is unique: a map `A` is the adjoint of `B` iff it satisfies `⟪A x, y⟫ = ⟪x, B y⟫`
for all `x` and `y`. -/
theorem eq_adjoint_iff (A : E →L[𝕜] F) (B : F →L[𝕜] E) : A = B† ↔ ∀ x y, ⟪A x, y⟫ = ⟪x, B y⟫ :=
  by
  refine' ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => _⟩
  ext x
  exact ext_inner_right 𝕜 fun y => by simp only [adjoint_inner_left, h x y]
#align continuous_linear_map.eq_adjoint_iff ContinuousLinearMap.eq_adjoint_iff

@[simp]
theorem adjoint_id : (ContinuousLinearMap.id 𝕜 E).adjoint = ContinuousLinearMap.id 𝕜 E :=
  by
  refine' Eq.symm _
  rw [eq_adjoint_iff]
  simp
#align continuous_linear_map.adjoint_id ContinuousLinearMap.adjoint_id

theorem Submodule.adjoint_subtypeL (U : Submodule 𝕜 E) [CompleteSpace U] :
    U.subtypeL† = orthogonalProjection U := by
  symm
  rw [eq_adjoint_iff]
  intro x u
  rw [U.coe_inner, inner_orthogonal_projection_left_eq_right,
    orthogonal_projection_mem_subspace_eq_self]
  rfl
#align submodule.adjoint_subtypeL Submodule.adjoint_subtypeL

theorem Submodule.adjoint_orthogonal_projection (U : Submodule 𝕜 E) [CompleteSpace U] :
    (orthogonalProjection U : E →L[𝕜] U)† = U.subtypeL := by
  rw [← U.adjoint_subtypeL, adjoint_adjoint]
#align submodule.adjoint_orthogonal_projection Submodule.adjoint_orthogonal_projection

/-- `E →L[𝕜] E` is a star algebra with the adjoint as the star operation. -/
instance : Star (E →L[𝕜] E) :=
  ⟨adjoint⟩

instance : InvolutiveStar (E →L[𝕜] E) :=
  ⟨adjoint_adjoint⟩

instance : StarSemigroup (E →L[𝕜] E) :=
  ⟨adjoint_comp⟩

instance : StarRing (E →L[𝕜] E) :=
  ⟨LinearIsometryEquiv.map_add adjoint⟩

instance : StarModule 𝕜 (E →L[𝕜] E) :=
  ⟨LinearIsometryEquiv.map_smulₛₗ adjoint⟩

theorem star_eq_adjoint (A : E →L[𝕜] E) : star A = A† :=
  rfl
#align continuous_linear_map.star_eq_adjoint ContinuousLinearMap.star_eq_adjoint

/-- A continuous linear operator is self-adjoint iff it is equal to its adjoint. -/
theorem is_self_adjoint_iff' {A : E →L[𝕜] E} : IsSelfAdjoint A ↔ A.adjoint = A :=
  Iff.rfl
#align continuous_linear_map.is_self_adjoint_iff' ContinuousLinearMap.is_self_adjoint_iff'

instance : CstarRing (E →L[𝕜] E) :=
  ⟨by
    intro A
    rw [star_eq_adjoint]
    refine' le_antisymm _ _
    ·
      calc
        ‖A† * A‖ ≤ ‖A†‖ * ‖A‖ := op_norm_comp_le _ _
        _ = ‖A‖ * ‖A‖ := by rw [LinearIsometryEquiv.norm_map]
        
    · rw [← sq, ← Real.sqrt_le_sqrt_iff (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
      refine' op_norm_le_bound _ (Real.sqrt_nonneg _) fun x => _
      have :=
        calc
          re ⟪(A† * A) x, x⟫ ≤ ‖(A† * A) x‖ * ‖x‖ := re_inner_le_norm _ _
          _ ≤ ‖A† * A‖ * ‖x‖ * ‖x‖ := mul_le_mul_of_nonneg_right (le_op_norm _ _) (norm_nonneg _)
          
      calc
        ‖A x‖ = Real.sqrt (re ⟪(A† * A) x, x⟫) := by rw [apply_norm_eq_sqrt_inner_adjoint_left]
        _ ≤ Real.sqrt (‖A† * A‖ * ‖x‖ * ‖x‖) := Real.sqrt_le_sqrt this
        _ = Real.sqrt ‖A† * A‖ * ‖x‖ := by
          rw [mul_assoc, Real.sqrt_mul (norm_nonneg _), Real.sqrt_mul_self (norm_nonneg _)]
        ⟩

section Real

variable {E' : Type _} {F' : Type _} [InnerProductSpace ℝ E'] [InnerProductSpace ℝ F']

variable [CompleteSpace E'] [CompleteSpace F']

-- Todo: Generalize this to `is_R_or_C`.
theorem isAdjointPairInner (A : E' →L[ℝ] F') :
    LinearMap.IsAdjointPair (sesqFormOfInner : E' →ₗ[ℝ] E' →ₗ[ℝ] ℝ)
      (sesqFormOfInner : F' →ₗ[ℝ] F' →ₗ[ℝ] ℝ) A (A†) :=
  fun x y => by
  simp only [sesq_form_of_inner_apply_apply, adjoint_inner_left, to_linear_map_eq_coe, coe_coe]
#align continuous_linear_map.is_adjoint_pair_inner ContinuousLinearMap.isAdjointPairInner

end Real

end ContinuousLinearMap

/-! ### Self-adjoint operators -/


namespace IsSelfAdjoint

open ContinuousLinearMap

variable [CompleteSpace E] [CompleteSpace F]

theorem adjoint_eq {A : E →L[𝕜] E} (hA : IsSelfAdjoint A) : A.adjoint = A :=
  hA
#align is_self_adjoint.adjoint_eq IsSelfAdjoint.adjoint_eq

/-- Every self-adjoint operator on an inner product space is symmetric. -/
theorem isSymmetric {A : E →L[𝕜] E} (hA : IsSelfAdjoint A) : (A : E →ₗ[𝕜] E).IsSymmetric :=
  fun x y => by rw_mod_cast [← A.adjoint_inner_right, hA.adjoint_eq]
#align is_self_adjoint.is_symmetric IsSelfAdjoint.isSymmetric

/-- Conjugating preserves self-adjointness -/
theorem conj_adjoint {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) (S : E →L[𝕜] F) :
    IsSelfAdjoint (S ∘L T ∘L S.adjoint) :=
  by
  rw [is_self_adjoint_iff'] at hT⊢
  simp only [hT, adjoint_comp, adjoint_adjoint]
  exact ContinuousLinearMap.comp_assoc _ _ _
#align is_self_adjoint.conj_adjoint IsSelfAdjoint.conj_adjoint

/-- Conjugating preserves self-adjointness -/
theorem adjoint_conj {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) (S : F →L[𝕜] E) :
    IsSelfAdjoint (S.adjoint ∘L T ∘L S) :=
  by
  rw [is_self_adjoint_iff'] at hT⊢
  simp only [hT, adjoint_comp, adjoint_adjoint]
  exact ContinuousLinearMap.comp_assoc _ _ _
#align is_self_adjoint.adjoint_conj IsSelfAdjoint.adjoint_conj

theorem ContinuousLinearMap.is_self_adjoint_iff_is_symmetric {A : E →L[𝕜] E} :
    IsSelfAdjoint A ↔ (A : E →ₗ[𝕜] E).IsSymmetric :=
  ⟨fun hA => hA.IsSymmetric, fun hA =>
    ext fun x => (ext_inner_right 𝕜) fun y => (A.adjoint_inner_left y x).symm ▸ (hA x y).symm⟩
#align
  continuous_linear_map.is_self_adjoint_iff_is_symmetric ContinuousLinearMap.is_self_adjoint_iff_is_symmetric

theorem LinearMap.IsSymmetric.is_self_adjoint {A : E →L[𝕜] E} (hA : (A : E →ₗ[𝕜] E).IsSymmetric) :
    IsSelfAdjoint A := by rwa [← ContinuousLinearMap.is_self_adjoint_iff_is_symmetric] at hA
#align linear_map.is_symmetric.is_self_adjoint LinearMap.IsSymmetric.is_self_adjoint

/-- The orthogonal projection is self-adjoint. -/
theorem orthogonal_projection_is_self_adjoint (U : Submodule 𝕜 E) [CompleteSpace U] :
    IsSelfAdjoint (U.subtypeL ∘L orthogonalProjection U) :=
  (orthogonalProjectionIsSymmetric U).IsSelfAdjoint
#align orthogonal_projection_is_self_adjoint orthogonal_projection_is_self_adjoint

theorem conj_orthogonal_projection {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) (U : Submodule 𝕜 E)
    [CompleteSpace U] :
    IsSelfAdjoint
      (U.subtypeL ∘L orthogonalProjection U ∘L T ∘L U.subtypeL ∘L orthogonalProjection U) :=
  by
  rw [← ContinuousLinearMap.comp_assoc]
  nth_rw 1 [← (orthogonal_projection_is_self_adjoint U).adjoint_eq]
  refine' hT.adjoint_conj _
#align is_self_adjoint.conj_orthogonal_projection IsSelfAdjoint.conj_orthogonal_projection

end IsSelfAdjoint

namespace LinearMap

variable [CompleteSpace E]

variable {T : E →ₗ[𝕜] E}

/-- The **Hellinger--Toeplitz theorem**: Construct a self-adjoint operator from an everywhere
  defined symmetric operator.-/
def IsSymmetric.toSelfAdjoint (hT : IsSymmetric T) : selfAdjoint (E →L[𝕜] E) :=
  ⟨⟨T, hT.Continuous⟩, ContinuousLinearMap.is_self_adjoint_iff_is_symmetric.mpr hT⟩
#align linear_map.is_symmetric.to_self_adjoint LinearMap.IsSymmetric.toSelfAdjoint

theorem IsSymmetric.coe_to_self_adjoint (hT : IsSymmetric T) : (hT.toSelfAdjoint : E →ₗ[𝕜] E) = T :=
  rfl
#align linear_map.is_symmetric.coe_to_self_adjoint LinearMap.IsSymmetric.coe_to_self_adjoint

theorem IsSymmetric.to_self_adjoint_apply (hT : IsSymmetric T) {x : E} : hT.toSelfAdjoint x = T x :=
  rfl
#align linear_map.is_symmetric.to_self_adjoint_apply LinearMap.IsSymmetric.to_self_adjoint_apply

end LinearMap

namespace LinearMap

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]

attribute [local instance] FiniteDimensional.complete

/-- The adjoint of an operator from the finite-dimensional inner product space E to the finite-
dimensional inner product space F. -/
def adjoint : (E →ₗ[𝕜] F) ≃ₗ⋆[𝕜] F →ₗ[𝕜] E :=
  ((LinearMap.toContinuousLinearMap : (E →ₗ[𝕜] F) ≃ₗ[𝕜] E →L[𝕜] F).trans
        ContinuousLinearMap.adjoint.toLinearEquiv).trans
    LinearMap.toContinuousLinearMap.symm
#align linear_map.adjoint LinearMap.adjoint

theorem adjoint_to_continuous_linear_map (A : E →ₗ[𝕜] F) :
    A.adjoint.toContinuousLinearMap = A.toContinuousLinearMap.adjoint :=
  rfl
#align linear_map.adjoint_to_continuous_linear_map LinearMap.adjoint_to_continuous_linear_map

theorem adjoint_eq_to_clm_adjoint (A : E →ₗ[𝕜] F) : A.adjoint = A.toContinuousLinearMap.adjoint :=
  rfl
#align linear_map.adjoint_eq_to_clm_adjoint LinearMap.adjoint_eq_to_clm_adjoint

/-- The fundamental property of the adjoint. -/
theorem adjoint_inner_left (A : E →ₗ[𝕜] F) (x : E) (y : F) : ⟪adjoint A y, x⟫ = ⟪y, A x⟫ :=
  by
  rw [← coe_to_continuous_linear_map A, adjoint_eq_to_clm_adjoint]
  exact ContinuousLinearMap.adjoint_inner_left _ x y
#align linear_map.adjoint_inner_left LinearMap.adjoint_inner_left

/-- The fundamental property of the adjoint. -/
theorem adjoint_inner_right (A : E →ₗ[𝕜] F) (x : E) (y : F) : ⟪x, adjoint A y⟫ = ⟪A x, y⟫ :=
  by
  rw [← coe_to_continuous_linear_map A, adjoint_eq_to_clm_adjoint]
  exact ContinuousLinearMap.adjoint_inner_right _ x y
#align linear_map.adjoint_inner_right LinearMap.adjoint_inner_right

/-- The adjoint is involutive -/
@[simp]
theorem adjoint_adjoint (A : E →ₗ[𝕜] F) : A.adjoint.adjoint = A :=
  by
  ext v
  refine' ext_inner_left 𝕜 fun w => _
  rw [adjoint_inner_right, adjoint_inner_left]
#align linear_map.adjoint_adjoint LinearMap.adjoint_adjoint

/-- The adjoint of the composition of two operators is the composition of the two adjoints
in reverse order. -/
@[simp]
theorem adjoint_comp (A : F →ₗ[𝕜] G) (B : E →ₗ[𝕜] F) : (A ∘ₗ B).adjoint = B.adjoint ∘ₗ A.adjoint :=
  by
  ext v
  refine' ext_inner_left 𝕜 fun w => _
  simp only [adjoint_inner_right, LinearMap.coe_comp, Function.comp_apply]
#align linear_map.adjoint_comp LinearMap.adjoint_comp

/-- The adjoint is unique: a map `A` is the adjoint of `B` iff it satisfies `⟪A x, y⟫ = ⟪x, B y⟫`
for all `x` and `y`. -/
theorem eq_adjoint_iff (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E) :
    A = B.adjoint ↔ ∀ x y, ⟪A x, y⟫ = ⟪x, B y⟫ :=
  by
  refine' ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => _⟩
  ext x
  exact ext_inner_right 𝕜 fun y => by simp only [adjoint_inner_left, h x y]
#align linear_map.eq_adjoint_iff LinearMap.eq_adjoint_iff

/-- The adjoint is unique: a map `A` is the adjoint of `B` iff it satisfies `⟪A x, y⟫ = ⟪x, B y⟫`
for all basis vectors `x` and `y`. -/
theorem eq_adjoint_iff_basis {ι₁ : Type _} {ι₂ : Type _} (b₁ : Basis ι₁ 𝕜 E) (b₂ : Basis ι₂ 𝕜 F)
    (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E) :
    A = B.adjoint ↔ ∀ (i₁ : ι₁) (i₂ : ι₂), ⟪A (b₁ i₁), b₂ i₂⟫ = ⟪b₁ i₁, B (b₂ i₂)⟫ :=
  by
  refine' ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => _⟩
  refine' Basis.ext b₁ fun i₁ => _
  exact ext_inner_right_basis b₂ fun i₂ => by simp only [adjoint_inner_left, h i₁ i₂]
#align linear_map.eq_adjoint_iff_basis LinearMap.eq_adjoint_iff_basis

theorem eq_adjoint_iff_basis_left {ι : Type _} (b : Basis ι 𝕜 E) (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E) :
    A = B.adjoint ↔ ∀ i y, ⟪A (b i), y⟫ = ⟪b i, B y⟫ :=
  by
  refine' ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => Basis.ext b fun i => _⟩
  exact ext_inner_right 𝕜 fun y => by simp only [h i, adjoint_inner_left]
#align linear_map.eq_adjoint_iff_basis_left LinearMap.eq_adjoint_iff_basis_left

theorem eq_adjoint_iff_basis_right {ι : Type _} (b : Basis ι 𝕜 F) (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E) :
    A = B.adjoint ↔ ∀ i x, ⟪A x, b i⟫ = ⟪x, B (b i)⟫ :=
  by
  refine' ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => _⟩
  ext x
  refine' ext_inner_right_basis b fun i => by simp only [h i, adjoint_inner_left]
#align linear_map.eq_adjoint_iff_basis_right LinearMap.eq_adjoint_iff_basis_right

/-- `E →ₗ[𝕜] E` is a star algebra with the adjoint as the star operation. -/
instance : Star (E →ₗ[𝕜] E) :=
  ⟨adjoint⟩

instance : InvolutiveStar (E →ₗ[𝕜] E) :=
  ⟨adjoint_adjoint⟩

instance : StarSemigroup (E →ₗ[𝕜] E) :=
  ⟨adjoint_comp⟩

instance : StarRing (E →ₗ[𝕜] E) :=
  ⟨LinearEquiv.map_add adjoint⟩

instance : StarModule 𝕜 (E →ₗ[𝕜] E) :=
  ⟨LinearEquiv.map_smulₛₗ adjoint⟩

theorem star_eq_adjoint (A : E →ₗ[𝕜] E) : star A = A.adjoint :=
  rfl
#align linear_map.star_eq_adjoint LinearMap.star_eq_adjoint

/-- A continuous linear operator is self-adjoint iff it is equal to its adjoint. -/
theorem is_self_adjoint_iff' {A : E →ₗ[𝕜] E} : IsSelfAdjoint A ↔ A.adjoint = A :=
  Iff.rfl
#align linear_map.is_self_adjoint_iff' LinearMap.is_self_adjoint_iff'

theorem is_symmetric_iff_is_self_adjoint (A : E →ₗ[𝕜] E) : IsSymmetric A ↔ IsSelfAdjoint A :=
  by
  rw [is_self_adjoint_iff', is_symmetric, ← LinearMap.eq_adjoint_iff]
  exact eq_comm
#align linear_map.is_symmetric_iff_is_self_adjoint LinearMap.is_symmetric_iff_is_self_adjoint

section Real

variable {E' : Type _} {F' : Type _} [InnerProductSpace ℝ E'] [InnerProductSpace ℝ F']

variable [FiniteDimensional ℝ E'] [FiniteDimensional ℝ F']

-- Todo: Generalize this to `is_R_or_C`.
theorem isAdjointPairInner (A : E' →ₗ[ℝ] F') :
    IsAdjointPair (sesqFormOfInner : E' →ₗ[ℝ] E' →ₗ[ℝ] ℝ) (sesqFormOfInner : F' →ₗ[ℝ] F' →ₗ[ℝ] ℝ) A
      A.adjoint :=
  fun x y => by simp only [sesq_form_of_inner_apply_apply, adjoint_inner_left]
#align linear_map.is_adjoint_pair_inner LinearMap.isAdjointPairInner

end Real

/-- The Gram operator T†T is symmetric. -/
theorem isSymmetricAdjointMulSelf (T : E →ₗ[𝕜] E) : IsSymmetric (T.adjoint * T) := fun x y => by
  simp only [mul_apply, adjoint_inner_left, adjoint_inner_right]
#align linear_map.is_symmetric_adjoint_mul_self LinearMap.isSymmetricAdjointMulSelf

/-- The Gram operator T†T is a positive operator. -/
theorem re_inner_adjoint_mul_self_nonneg (T : E →ₗ[𝕜] E) (x : E) : 0 ≤ re ⟪x, (T.adjoint * T) x⟫ :=
  by
  simp only [mul_apply, adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast
  exact sq_nonneg _
#align linear_map.re_inner_adjoint_mul_self_nonneg LinearMap.re_inner_adjoint_mul_self_nonneg

@[simp]
theorem im_inner_adjoint_mul_self_eq_zero (T : E →ₗ[𝕜] E) (x : E) :
    im ⟪x, LinearMap.adjoint T (T x)⟫ = 0 :=
  by
  simp only [mul_apply, adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast
#align linear_map.im_inner_adjoint_mul_self_eq_zero LinearMap.im_inner_adjoint_mul_self_eq_zero

end LinearMap

namespace Matrix

variable {m n : Type _} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

open ComplexConjugate

/-- The adjoint of the linear map associated to a matrix is the linear map associated to the
conjugate transpose of that matrix. -/
theorem conj_transpose_eq_adjoint (A : Matrix m n 𝕜) :
    toLin' A.conjTranspose =
      @LinearMap.adjoint _ (EuclideanSpace 𝕜 n) (EuclideanSpace 𝕜 m) _ _ _ _ _ (toLin' A) :=
  by
  rw [@LinearMap.eq_adjoint_iff _ (EuclideanSpace 𝕜 m) (EuclideanSpace 𝕜 n)]
  intro x y
  convert dot_product_assoc (conj ∘ (id x : m → 𝕜)) y A using 1
  simp [dot_product, mul_vec, RingHom.map_sum, ← starRingEnd_apply, mul_comm]
#align matrix.conj_transpose_eq_adjoint Matrix.conj_transpose_eq_adjoint

end Matrix

