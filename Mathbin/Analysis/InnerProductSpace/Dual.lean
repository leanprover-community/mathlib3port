/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis

! This file was ported from Lean 3 source module analysis.inner_product_space.dual
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.InnerProductSpace.Projection
import Mathbin.Analysis.NormedSpace.Dual
import Mathbin.Analysis.NormedSpace.Star.Basic

/-!
# The Fréchet-Riesz representation theorem

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We consider an inner product space `E` over `𝕜`, which is either `ℝ` or `ℂ`. We define
`to_dual_map`, a conjugate-linear isometric embedding of `E` into its dual, which maps an element
`x` of the space to `λ y, ⟪x, y⟫`.

Under the hypothesis of completeness (i.e., for Hilbert spaces), we upgrade this to `to_dual`, a
conjugate-linear isometric *equivalence* of `E` onto its dual; that is, we establish the
surjectivity of `to_dual_map`.  This is the Fréchet-Riesz representation theorem: every element of
the dual of a Hilbert space `E` has the form `λ u, ⟪x, u⟫` for some `x : E`.

For a bounded sesquilinear form `B : E →L⋆[𝕜] E →L[𝕜] 𝕜`,
we define a map `inner_product_space.continuous_linear_map_of_bilin B : E →L[𝕜] E`,
given by substituting `E →L[𝕜] 𝕜` with `E` using `to_dual`.


## References

* [M. Einsiedler and T. Ward, *Functional Analysis, Spectral Theory, and Applications*]
  [EinsiedlerWard2017]

## Tags

dual, Fréchet-Riesz
-/


noncomputable section

open Classical ComplexConjugate

universe u v

namespace InnerProductSpace

open IsROrC ContinuousLinearMap

variable (𝕜 : Type _)

variable (E : Type _) [IsROrC 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 E _ x y

-- mathport name: «expr †»
local postfix:90 "†" => starRingEnd _

#print InnerProductSpace.toDualMap /-
/-- An element `x` of an inner product space `E` induces an element of the dual space `dual 𝕜 E`,
the map `λ y, ⟪x, y⟫`; moreover this operation is a conjugate-linear isometric embedding of `E`
into `dual 𝕜 E`.
If `E` is complete, this operation is surjective, hence a conjugate-linear isometric equivalence;
see `to_dual`.
-/
def toDualMap : E →ₗᵢ⋆[𝕜] NormedSpace.Dual 𝕜 E :=
  { innerSL 𝕜 with norm_map' := innerSL_apply_norm _ }
#align inner_product_space.to_dual_map InnerProductSpace.toDualMap
-/

variable {E}

/- warning: inner_product_space.to_dual_map_apply -> InnerProductSpace.toDualMap_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_product_space.to_dual_map_apply InnerProductSpace.toDualMap_applyₓ'. -/
@[simp]
theorem toDualMap_apply {x y : E} : toDualMap 𝕜 E x y = ⟪x, y⟫ :=
  rfl
#align inner_product_space.to_dual_map_apply InnerProductSpace.toDualMap_apply

/- warning: inner_product_space.innerSL_norm -> InnerProductSpace.innerSL_norm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_product_space.innerSL_norm InnerProductSpace.innerSL_normₓ'. -/
theorem innerSL_norm [Nontrivial E] : ‖(innerSL 𝕜 : E →L⋆[𝕜] E →L[𝕜] 𝕜)‖ = 1 :=
  show ‖(toDualMap 𝕜 E).toContinuousLinearMap‖ = 1 from LinearIsometry.norm_toContinuousLinearMap _
#align inner_product_space.innerSL_norm InnerProductSpace.innerSL_norm

variable {𝕜}

/- warning: inner_product_space.ext_inner_left_basis -> InnerProductSpace.ext_inner_left_basis is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_product_space.ext_inner_left_basis InnerProductSpace.ext_inner_left_basisₓ'. -/
theorem ext_inner_left_basis {ι : Type _} {x y : E} (b : Basis ι 𝕜 E)
    (h : ∀ i : ι, ⟪b i, x⟫ = ⟪b i, y⟫) : x = y :=
  by
  apply (to_dual_map 𝕜 E).map_eq_iff.mp
  refine' (Function.Injective.eq_iff ContinuousLinearMap.coe_injective).mp (Basis.ext b _)
  intro i
  simp only [to_dual_map_apply, ContinuousLinearMap.coe_coe]
  rw [← inner_conj_symm]
  nth_rw_rhs 1 [← inner_conj_symm]
  exact congr_arg conj (h i)
#align inner_product_space.ext_inner_left_basis InnerProductSpace.ext_inner_left_basis

/- warning: inner_product_space.ext_inner_right_basis -> InnerProductSpace.ext_inner_right_basis is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_product_space.ext_inner_right_basis InnerProductSpace.ext_inner_right_basisₓ'. -/
theorem ext_inner_right_basis {ι : Type _} {x y : E} (b : Basis ι 𝕜 E)
    (h : ∀ i : ι, ⟪x, b i⟫ = ⟪y, b i⟫) : x = y :=
  by
  refine' ext_inner_left_basis b fun i => _
  rw [← inner_conj_symm]
  nth_rw_rhs 1 [← inner_conj_symm]
  exact congr_arg conj (h i)
#align inner_product_space.ext_inner_right_basis InnerProductSpace.ext_inner_right_basis

variable (𝕜) (E) [CompleteSpace E]

#print InnerProductSpace.toDual /-
/-- Fréchet-Riesz representation: any `ℓ` in the dual of a Hilbert space `E` is of the form
`λ u, ⟪y, u⟫` for some `y : E`, i.e. `to_dual_map` is surjective.
-/
def toDual : E ≃ₗᵢ⋆[𝕜] NormedSpace.Dual 𝕜 E :=
  LinearIsometryEquiv.ofSurjective (toDualMap 𝕜 E)
    (by
      intro ℓ
      set Y := LinearMap.ker ℓ with hY
      by_cases htriv : Y = ⊤
      · have hℓ : ℓ = 0 := by
          have h' := linear_map.ker_eq_top.mp htriv
          rw [← coe_zero] at h'
          apply coe_injective
          exact h'
        exact ⟨0, by simp [hℓ]⟩
      · rw [← Submodule.orthogonal_eq_bot_iff] at htriv
        change Yᗮ ≠ ⊥ at htriv
        rw [Submodule.ne_bot_iff] at htriv
        obtain ⟨z : E, hz : z ∈ Yᗮ, z_ne_0 : z ≠ 0⟩ := htriv
        refine' ⟨(ℓ z† / ⟪z, z⟫) • z, _⟩
        ext x
        have h₁ : ℓ z • x - ℓ x • z ∈ Y :=
          by
          rw [LinearMap.mem_ker, map_sub, ContinuousLinearMap.map_smul,
            ContinuousLinearMap.map_smul, Algebra.id.smul_eq_mul, Algebra.id.smul_eq_mul, mul_comm]
          exact sub_self (ℓ x * ℓ z)
        have h₂ : ℓ z * ⟪z, x⟫ = ℓ x * ⟪z, z⟫ :=
          haveI h₃ :=
            calc
              0 = ⟪z, ℓ z • x - ℓ x • z⟫ := by rw [(Y.mem_orthogonal' z).mp hz]; exact h₁
              _ = ⟪z, ℓ z • x⟫ - ⟪z, ℓ x • z⟫ := by rw [inner_sub_right]
              _ = ℓ z * ⟪z, x⟫ - ℓ x * ⟪z, z⟫ := by simp [inner_smul_right]
              
          sub_eq_zero.mp (Eq.symm h₃)
        have h₄ :=
          calc
            ⟪(ℓ z† / ⟪z, z⟫) • z, x⟫ = ℓ z / ⟪z, z⟫ * ⟪z, x⟫ := by simp [inner_smul_left, conj_conj]
            _ = ℓ z * ⟪z, x⟫ / ⟪z, z⟫ := by rw [← div_mul_eq_mul_div]
            _ = ℓ x * ⟪z, z⟫ / ⟪z, z⟫ := by rw [h₂]
            _ = ℓ x := by field_simp [inner_self_ne_zero.2 z_ne_0]
            
        exact h₄)
#align inner_product_space.to_dual InnerProductSpace.toDual
-/

variable {𝕜} {E}

/- warning: inner_product_space.to_dual_apply -> InnerProductSpace.toDual_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_product_space.to_dual_apply InnerProductSpace.toDual_applyₓ'. -/
@[simp]
theorem toDual_apply {x y : E} : toDual 𝕜 E x y = ⟪x, y⟫ :=
  rfl
#align inner_product_space.to_dual_apply InnerProductSpace.toDual_apply

/- warning: inner_product_space.to_dual_symm_apply -> InnerProductSpace.toDual_symm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_product_space.to_dual_symm_apply InnerProductSpace.toDual_symm_applyₓ'. -/
@[simp]
theorem toDual_symm_apply {x : E} {y : NormedSpace.Dual 𝕜 E} : ⟪(toDual 𝕜 E).symm y, x⟫ = y x :=
  by
  rw [← to_dual_apply]
  simp only [LinearIsometryEquiv.apply_symm_apply]
#align inner_product_space.to_dual_symm_apply InnerProductSpace.toDual_symm_apply

variable {E 𝕜}

#print InnerProductSpace.continuousLinearMapOfBilin /-
/-- Maps a bounded sesquilinear form to its continuous linear map,
given by interpreting the form as a map `B : E →L⋆[𝕜] normed_space.dual 𝕜 E`
and dualizing the result using `to_dual`.
-/
def continuousLinearMapOfBilin (B : E →L⋆[𝕜] E →L[𝕜] 𝕜) : E →L[𝕜] E :=
  comp (toDual 𝕜 E).symm.toContinuousLinearEquiv.toContinuousLinearMap B
#align inner_product_space.continuous_linear_map_of_bilin InnerProductSpace.continuousLinearMapOfBilin
-/

-- mathport name: «expr ♯»
local postfix:1024 "♯" => continuousLinearMapOfBilin

variable (B : E →L⋆[𝕜] E →L[𝕜] 𝕜)

/- warning: inner_product_space.continuous_linear_map_of_bilin_apply -> InnerProductSpace.continuousLinearMapOfBilin_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_product_space.continuous_linear_map_of_bilin_apply InnerProductSpace.continuousLinearMapOfBilin_applyₓ'. -/
@[simp]
theorem continuousLinearMapOfBilin_apply (v w : E) : ⟪B♯ v, w⟫ = B v w := by
  simp [continuous_linear_map_of_bilin]
#align inner_product_space.continuous_linear_map_of_bilin_apply InnerProductSpace.continuousLinearMapOfBilin_apply

/- warning: inner_product_space.unique_continuous_linear_map_of_bilin -> InnerProductSpace.unique_continuousLinearMapOfBilin is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_product_space.unique_continuous_linear_map_of_bilin InnerProductSpace.unique_continuousLinearMapOfBilinₓ'. -/
theorem unique_continuousLinearMapOfBilin {v f : E} (is_lax_milgram : ∀ w, ⟪f, w⟫ = B v w) :
    f = B♯ v := by
  refine' ext_inner_right 𝕜 _
  intro w
  rw [continuous_linear_map_of_bilin_apply]
  exact is_lax_milgram w
#align inner_product_space.unique_continuous_linear_map_of_bilin InnerProductSpace.unique_continuousLinearMapOfBilin

end InnerProductSpace

