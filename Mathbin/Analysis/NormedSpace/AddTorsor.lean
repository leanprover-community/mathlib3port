import Mathbin.Analysis.NormedSpace.Basic
import Mathbin.Analysis.Normed.Group.AddTorsor
import Mathbin.LinearAlgebra.AffineSpace.Midpoint
import Mathbin.Topology.Instances.RealVectorSpace

/-!
# Torsors of normed space actions.

This file contains lemmas about normed additive torsors over normed spaces.
-/


noncomputable section

open_locale Nnreal TopologicalSpace

open Filter

variable {α V P : Type _} [SemiNormedGroup V] [PseudoMetricSpace P] [NormedAddTorsor V P]

variable {W Q : Type _} [NormedGroup W] [MetricSpace Q] [NormedAddTorsor W Q]

include V

section NormedSpace

variable {𝕜 : Type _} [NormedField 𝕜] [NormedSpace 𝕜 V]

open AffineMap

@[simp]
theorem dist_center_homothety (p₁ p₂ : P) (c : 𝕜) : dist p₁ (homothety p₁ c p₂) = ∥c∥ * dist p₁ p₂ := by
  simp [homothety_def, norm_smul, ← dist_eq_norm_vsub, dist_comm]

@[simp]
theorem dist_homothety_center (p₁ p₂ : P) (c : 𝕜) : dist (homothety p₁ c p₂) p₁ = ∥c∥ * dist p₁ p₂ := by
  rw [dist_comm, dist_center_homothety]

@[simp]
theorem dist_homothety_self (p₁ p₂ : P) (c : 𝕜) : dist (homothety p₁ c p₂) p₂ = ∥1 - c∥ * dist p₁ p₂ := by
  rw [homothety_eq_line_map, ← line_map_apply_one_sub, ← homothety_eq_line_map, dist_homothety_center, dist_comm]

@[simp]
theorem dist_self_homothety (p₁ p₂ : P) (c : 𝕜) : dist p₂ (homothety p₁ c p₂) = ∥1 - c∥ * dist p₁ p₂ := by
  rw [dist_comm, dist_homothety_self]

variable [Invertible (2 : 𝕜)]

@[simp]
theorem dist_left_midpoint (p₁ p₂ : P) : dist p₁ (midpoint 𝕜 p₁ p₂) = ∥(2 : 𝕜)∥⁻¹ * dist p₁ p₂ := by
  rw [midpoint, ← homothety_eq_line_map, dist_center_homothety, inv_of_eq_inv, ← NormedField.norm_inv]

@[simp]
theorem dist_midpoint_left (p₁ p₂ : P) : dist (midpoint 𝕜 p₁ p₂) p₁ = ∥(2 : 𝕜)∥⁻¹ * dist p₁ p₂ := by
  rw [dist_comm, dist_left_midpoint]

@[simp]
theorem dist_midpoint_right (p₁ p₂ : P) : dist (midpoint 𝕜 p₁ p₂) p₂ = ∥(2 : 𝕜)∥⁻¹ * dist p₁ p₂ := by
  rw [midpoint_comm, dist_midpoint_left, dist_comm]

@[simp]
theorem dist_right_midpoint (p₁ p₂ : P) : dist p₂ (midpoint 𝕜 p₁ p₂) = ∥(2 : 𝕜)∥⁻¹ * dist p₁ p₂ := by
  rw [dist_comm, dist_midpoint_right]

theorem dist_midpoint_midpoint_le' (p₁ p₂ p₃ p₄ : P) :
    dist (midpoint 𝕜 p₁ p₂) (midpoint 𝕜 p₃ p₄) ≤ (dist p₁ p₃ + dist p₂ p₄) / ∥(2 : 𝕜)∥ := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, midpoint_vsub_midpoint] <;>
    try
      infer_instance
  rw [midpoint_eq_smul_add, norm_smul, inv_of_eq_inv, NormedField.norm_inv, ← div_eq_inv_mul]
  exact div_le_div_of_le_of_nonneg (norm_add_le _ _) (norm_nonneg _)

end NormedSpace

variable [NormedSpace ℝ V] [NormedSpace ℝ W]

theorem dist_midpoint_midpoint_le (p₁ p₂ p₃ p₄ : V) :
    dist (midpoint ℝ p₁ p₂) (midpoint ℝ p₃ p₄) ≤ (dist p₁ p₃ + dist p₂ p₄) / 2 := by
  simpa using dist_midpoint_midpoint_le' p₁ p₂ p₃ p₄

include W

/-- A continuous map between two normed affine spaces is an affine map provided that
it sends midpoints to midpoints. -/
def AffineMap.ofMapMidpoint (f : P → Q) (h : ∀ x y, f (midpoint ℝ x y) = midpoint ℝ (f x) (f y)) (hfc : Continuous f) :
    P →ᵃ[ℝ] Q :=
  AffineMap.mk' f
    (↑((AddMonoidHom.ofMapMidpoint ℝ ℝ
            ((AffineEquiv.vaddConst ℝ (f <| Classical.arbitrary P)).symm ∘
              f ∘ AffineEquiv.vaddConst ℝ (Classical.arbitrary P))
            (by
              simp )
            fun x y => by
            simp [h]).toRealLinearMap <|
        by
        apply_rules [Continuous.vadd, Continuous.vsub, continuous_const, hfc.comp, continuous_id]))
    (Classical.arbitrary P) fun p => by
    simp

