/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Frédéric Dupuis, Heather Macbeth

! This file was ported from Lean 3 source module analysis.inner_product_space.symmetric
! leanprover-community/mathlib commit ba2245edf0c8bb155f1569fd9b9492a9b384cde6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.InnerProductSpace.Basic
import Mathbin.Analysis.NormedSpace.Banach
import Mathbin.LinearAlgebra.SesquilinearForm

/-!
# Symmetric linear maps in an inner product space

This file defines and proves basic theorems about symmetric **not necessarily bounded** operators
on an inner product space, i.e linear maps `T : E → E` such that `∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫`.

In comparison to `is_self_adjoint`, this definition works for non-continuous linear maps, and
doesn't rely on the definition of the adjoint, which allows it to be stated in non-complete space.

## Main definitions

* `linear_map.is_symmetric`: a (not necessarily bounded) operator on an inner product space is
symmetric, if for all `x`, `y`, we have `⟪T x, y⟫ = ⟪x, T y⟫`

## Main statements

* `is_symmetric.continuous`: if a symmetric operator is defined on a complete space, then
  it is automatically continuous.

## Tags

self-adjoint, symmetric
-/


open IsROrC

open ComplexConjugate

variable {𝕜 E E' F G : Type _} [IsROrC 𝕜]

variable [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] [InnerProductSpace 𝕜 G]

variable [InnerProductSpace ℝ E']

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

namespace LinearMap

/-! ### Symmetric operators -/


/-- A (not necessarily bounded) operator on an inner product space is symmetric, if for all
`x`, `y`, we have `⟪T x, y⟫ = ⟪x, T y⟫`. -/
def IsSymmetric (T : E →ₗ[𝕜] E) : Prop :=
  ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫
#align linear_map.is_symmetric LinearMap.IsSymmetric

section Real

variable ()

/-- An operator `T` on an inner product space is symmetric if and only if it is
`linear_map.is_self_adjoint` with respect to the sesquilinear form given by the inner product. -/
theorem is_symmetric_iff_sesq_form (T : E →ₗ[𝕜] E) :
    T.IsSymmetric ↔ @LinearMap.IsSelfAdjoint 𝕜 E _ _ _ (starRingEnd 𝕜) sesqFormOfInner T :=
  ⟨fun h x y => (h y x).symm, fun h x y => (h y x).symm⟩
#align linear_map.is_symmetric_iff_sesq_form LinearMap.is_symmetric_iff_sesq_form

end Real

theorem IsSymmetric.conj_inner_sym {T : E →ₗ[𝕜] E} (hT : IsSymmetric T) (x y : E) :
    conj ⟪T x, y⟫ = ⟪T y, x⟫ := by rw [hT x y, inner_conj_sym]
#align linear_map.is_symmetric.conj_inner_sym LinearMap.IsSymmetric.conj_inner_sym

@[simp]
theorem IsSymmetric.apply_clm {T : E →L[𝕜] E} (hT : IsSymmetric (T : E →ₗ[𝕜] E)) (x y : E) :
    ⟪T x, y⟫ = ⟪x, T y⟫ :=
  hT x y
#align linear_map.is_symmetric.apply_clm LinearMap.IsSymmetric.apply_clm

theorem isSymmetricZero : (0 : E →ₗ[𝕜] E).IsSymmetric := fun x y =>
  (inner_zero_right : ⟪x, 0⟫ = 0).symm ▸ (inner_zero_left : ⟪0, y⟫ = 0)
#align linear_map.is_symmetric_zero LinearMap.isSymmetricZero

theorem isSymmetricId : (LinearMap.id : E →ₗ[𝕜] E).IsSymmetric := fun x y => rfl
#align linear_map.is_symmetric_id LinearMap.isSymmetricId

theorem IsSymmetric.add {T S : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric) :
    (T + S).IsSymmetric := by 
  intro x y
  rw [LinearMap.add_apply, inner_add_left, hT x y, hS x y, ← inner_add_right]
  rfl
#align linear_map.is_symmetric.add LinearMap.IsSymmetric.add

/-- The **Hellinger--Toeplitz theorem**: if a symmetric operator is defined on a complete space,
  then it is automatically continuous. -/
theorem IsSymmetric.continuous [CompleteSpace E] {T : E →ₗ[𝕜] E} (hT : IsSymmetric T) :
    Continuous T :=
  by
  -- We prove it by using the closed graph theorem
  refine' T.continuous_of_seq_closed_graph fun u x y hu hTu => _
  rw [← sub_eq_zero, ← inner_self_eq_zero]
  have hlhs : ∀ k : ℕ, ⟪T (u k) - T x, y - T x⟫ = ⟪u k - x, T (y - T x)⟫ := by
    intro k
    rw [← T.map_sub, hT]
  refine' tendsto_nhds_unique ((hTu.sub_const _).inner tendsto_const_nhds) _
  simp_rw [hlhs]
  rw [← @inner_zero_left 𝕜 E _ _ (T (y - T x))]
  refine' Filter.Tendsto.inner _ tendsto_const_nhds
  rw [← sub_self x]
  exact hu.sub_const _
#align linear_map.is_symmetric.continuous LinearMap.IsSymmetric.continuous

/-- For a symmetric operator `T`, the function `λ x, ⟪T x, x⟫` is real-valued. -/
@[simp]
theorem IsSymmetric.coe_re_apply_inner_self_apply {T : E →L[𝕜] E} (hT : IsSymmetric (T : E →ₗ[𝕜] E))
    (x : E) : (T.reApplyInnerSelf x : 𝕜) = ⟪T x, x⟫ := by
  rsuffices ⟨r, hr⟩ : ∃ r : ℝ, ⟪T x, x⟫ = r
  · simp [hr, T.re_apply_inner_self_apply]
  rw [← eq_conj_iff_real]
  exact hT.conj_inner_sym x x
#align
  linear_map.is_symmetric.coe_re_apply_inner_self_apply LinearMap.IsSymmetric.coe_re_apply_inner_self_apply

/-- If a symmetric operator preserves a submodule, its restriction to that submodule is
symmetric. -/
theorem IsSymmetric.restrictInvariant {T : E →ₗ[𝕜] E} (hT : IsSymmetric T) {V : Submodule 𝕜 E}
    (hV : ∀ v ∈ V, T v ∈ V) : IsSymmetric (T.restrict hV) := fun v w => hT v w
#align linear_map.is_symmetric.restrict_invariant LinearMap.IsSymmetric.restrictInvariant

theorem IsSymmetric.restrictScalars {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    @LinearMap.IsSymmetric ℝ E _ (InnerProductSpace.isROrCToReal 𝕜 E)
      (@LinearMap.restrictScalars ℝ 𝕜 _ _ _ _ _ _ (InnerProductSpace.isROrCToReal 𝕜 E).toModule
        (InnerProductSpace.isROrCToReal 𝕜 E).toModule _ _ _ T) :=
  fun x y => by simp [hT x y, real_inner_eq_re_inner, LinearMap.coe_restrict_scalars_eq_coe]
#align linear_map.is_symmetric.restrict_scalars LinearMap.IsSymmetric.restrictScalars

section Complex

variable {V : Type _} [InnerProductSpace ℂ V]

/-- A linear operator on a complex inner product space is symmetric precisely when
`⟪T v, v⟫_ℂ` is real for all v.-/
theorem is_symmetric_iff_inner_map_self_real (T : V →ₗ[ℂ] V) :
    IsSymmetric T ↔ ∀ v : V, conj ⟪T v, v⟫_ℂ = ⟪T v, v⟫_ℂ := by
  constructor
  · intro hT v
    apply is_symmetric.conj_inner_sym hT
  · intro h x y
    nth_rw 2 [← inner_conj_sym]
    nth_rw 2 [inner_map_polarization]
    simp only [star_ring_end_apply, star_div', star_sub, star_add, star_mul]
    simp only [← star_ring_end_apply]
    rw [h (x + y), h (x - y), h (x + Complex.i • y), h (x - Complex.i • y)]
    simp only [Complex.conj_I]
    rw [inner_map_polarization']
    norm_num
    ring
#align
  linear_map.is_symmetric_iff_inner_map_self_real LinearMap.is_symmetric_iff_inner_map_self_real

end Complex

end LinearMap

