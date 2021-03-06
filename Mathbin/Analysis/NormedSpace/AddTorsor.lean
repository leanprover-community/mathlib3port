/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov
-/
import Mathbin.Analysis.NormedSpace.Basic
import Mathbin.Analysis.Normed.Group.AddTorsor
import Mathbin.LinearAlgebra.AffineSpace.Midpoint
import Mathbin.LinearAlgebra.AffineSpace.AffineSubspace
import Mathbin.Topology.Instances.RealVectorSpace

/-!
# Torsors of normed space actions.

This file contains lemmas about normed additive torsors over normed spaces.
-/


noncomputable section

open Nnreal TopologicalSpace

open Filter

variable {ฮฑ V P : Type _} [SemiNormedGroup V] [PseudoMetricSpace P] [NormedAddTorsor V P]

variable {W Q : Type _} [NormedGroup W] [MetricSpace Q] [NormedAddTorsor W Q]

section NormedSpace

variable {๐ : Type _} [NormedField ๐] [NormedSpace ๐ V] [NormedSpace ๐ W]

open AffineMap

theorem AffineSubspace.is_closed_direction_iff (s : AffineSubspace ๐ Q) :
    IsClosed (s.direction : Set W) โ IsClosed (s : Set Q) := by
  rcases s.eq_bot_or_nonempty with (rfl | โจx, hxโฉ)
  ยท simp [โ is_closed_singleton]
    
  rw [โ (Isometric.vaddConst x).toHomeomorph.symm.is_closed_image, AffineSubspace.coe_direction_eq_vsub_set_right hx]
  rfl

include V

@[simp]
theorem dist_center_homothety (pโ pโ : P) (c : ๐) : dist pโ (homothety pโ c pโ) = โฅcโฅ * dist pโ pโ := by
  simp [โ homothety_def, โ norm_smul, dist_eq_norm_vsub, โ dist_comm]

@[simp]
theorem dist_homothety_center (pโ pโ : P) (c : ๐) : dist (homothety pโ c pโ) pโ = โฅcโฅ * dist pโ pโ := by
  rw [dist_comm, dist_center_homothety]

@[simp]
theorem dist_line_map_line_map (pโ pโ : P) (cโ cโ : ๐) :
    dist (lineMap pโ pโ cโ) (lineMap pโ pโ cโ) = dist cโ cโ * dist pโ pโ := by
  rw [dist_comm pโ pโ]
  simp only [โ line_map_apply, โ dist_eq_norm_vsub, โ vadd_vsub_vadd_cancel_right, sub_smul, โ norm_smul, โ vsub_eq_sub]

theorem lipschitz_with_line_map (pโ pโ : P) : LipschitzWith (nndist pโ pโ) (lineMap pโ pโ : ๐ โ P) :=
  LipschitzWith.of_dist_le_mul fun cโ cโ => ((dist_line_map_line_map pโ pโ cโ cโ).trans (mul_comm _ _)).le

@[simp]
theorem dist_line_map_left (pโ pโ : P) (c : ๐) : dist (lineMap pโ pโ c) pโ = โฅcโฅ * dist pโ pโ := by
  simpa only [โ line_map_apply_zero, โ dist_zero_right] using dist_line_map_line_map pโ pโ c 0

@[simp]
theorem dist_left_line_map (pโ pโ : P) (c : ๐) : dist pโ (lineMap pโ pโ c) = โฅcโฅ * dist pโ pโ :=
  (dist_comm _ _).trans (dist_line_map_left _ _ _)

@[simp]
theorem dist_line_map_right (pโ pโ : P) (c : ๐) : dist (lineMap pโ pโ c) pโ = โฅ1 - cโฅ * dist pโ pโ := by
  simpa only [โ line_map_apply_one, โ dist_eq_norm'] using dist_line_map_line_map pโ pโ c 1

@[simp]
theorem dist_right_line_map (pโ pโ : P) (c : ๐) : dist pโ (lineMap pโ pโ c) = โฅ1 - cโฅ * dist pโ pโ :=
  (dist_comm _ _).trans (dist_line_map_right _ _ _)

@[simp]
theorem dist_homothety_self (pโ pโ : P) (c : ๐) : dist (homothety pโ c pโ) pโ = โฅ1 - cโฅ * dist pโ pโ := by
  rw [homothety_eq_line_map, dist_line_map_right]

@[simp]
theorem dist_self_homothety (pโ pโ : P) (c : ๐) : dist pโ (homothety pโ c pโ) = โฅ1 - cโฅ * dist pโ pโ := by
  rw [dist_comm, dist_homothety_self]

section invertibleTwo

variable [Invertible (2 : ๐)]

@[simp]
theorem dist_left_midpoint (pโ pโ : P) : dist pโ (midpoint ๐ pโ pโ) = โฅ(2 : ๐)โฅโปยน * dist pโ pโ := by
  rw [midpoint, dist_comm, dist_line_map_left, inv_of_eq_inv, โ norm_inv]

@[simp]
theorem dist_midpoint_left (pโ pโ : P) : dist (midpoint ๐ pโ pโ) pโ = โฅ(2 : ๐)โฅโปยน * dist pโ pโ := by
  rw [dist_comm, dist_left_midpoint]

@[simp]
theorem dist_midpoint_right (pโ pโ : P) : dist (midpoint ๐ pโ pโ) pโ = โฅ(2 : ๐)โฅโปยน * dist pโ pโ := by
  rw [midpoint_comm, dist_midpoint_left, dist_comm]

@[simp]
theorem dist_right_midpoint (pโ pโ : P) : dist pโ (midpoint ๐ pโ pโ) = โฅ(2 : ๐)โฅโปยน * dist pโ pโ := by
  rw [dist_comm, dist_midpoint_right]

theorem dist_midpoint_midpoint_le' (pโ pโ pโ pโ : P) :
    dist (midpoint ๐ pโ pโ) (midpoint ๐ pโ pโ) โค (dist pโ pโ + dist pโ pโ) / โฅ(2 : ๐)โฅ := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, midpoint_vsub_midpoint] <;>
    try
      infer_instance
  rw [midpoint_eq_smul_add, norm_smul, inv_of_eq_inv, norm_inv, โ div_eq_inv_mul]
  exact div_le_div_of_le_of_nonneg (norm_add_le _ _) (norm_nonneg _)

end invertibleTwo

omit V

include W

theorem antilipschitz_with_line_map {pโ pโ : Q} (h : pโ โ? pโ) :
    AntilipschitzWith (nndist pโ pโ)โปยน (lineMap pโ pโ : ๐ โ Q) :=
  AntilipschitzWith.of_le_mul_dist fun cโ cโ => by
    rw [dist_line_map_line_map, Nnreal.coe_inv, โ dist_nndist, mul_left_commโ, inv_mul_cancel (dist_ne_zero.2 h),
      mul_oneโ]

variable (๐)

theorem eventually_homothety_mem_of_mem_interior (x : Q) {s : Set Q} {y : Q} (hy : y โ Interior s) :
    โแถ? ฮด in ๐ (1 : ๐), homothety x ฮด y โ s := by
  rw [(NormedGroup.nhds_basis_norm_lt (1 : ๐)).eventually_iff]
  cases' eq_or_ne y x with h h
  ยท use 1
    simp [โ h.symm, โ interior_subset hy]
    
  have hxy : 0 < โฅy -แตฅ xโฅ := by
    rwa [norm_pos_iff, vsub_ne_zero]
  obtain โจu, huโ, huโ, huโโฉ := mem_interior.mp hy
  obtain โจฮต, hฮต, hyฮตโฉ := metric.is_open_iff.mp huโ y huโ
  refine' โจฮต / โฅy -แตฅ xโฅ, div_pos hฮต hxy, fun ฮด (hฮด : โฅฮด - 1โฅ < ฮต / โฅy -แตฅ xโฅ) => huโ (hyฮต _)โฉ
  rw [lt_div_iff hxy, โ norm_smul, sub_smul, one_smul] at hฮด
  rwa [homothety_apply, Metric.mem_ball, dist_eq_norm_vsub W, vadd_vsub_eq_sub_vsub]

theorem eventually_homothety_image_subset_of_finite_subset_interior (x : Q) {s : Set Q} {t : Set Q} (ht : t.Finite)
    (h : t โ Interior s) : โแถ? ฮด in ๐ (1 : ๐), homothety x ฮด '' t โ s := by
  suffices โ, โ y โ t, โ, โแถ? ฮด in ๐ (1 : ๐), homothety x ฮด y โ s by
    simp_rw [Set.image_subset_iff]
    exact (Filter.eventually_all_finite ht).mpr this
  intro y hy
  exact eventually_homothety_mem_of_mem_interior ๐ x (h hy)

end NormedSpace

variable [NormedSpace โ V] [NormedSpace โ W]

theorem dist_midpoint_midpoint_le (pโ pโ pโ pโ : V) :
    dist (midpoint โ pโ pโ) (midpoint โ pโ pโ) โค (dist pโ pโ + dist pโ pโ) / 2 := by
  simpa using dist_midpoint_midpoint_le' pโ pโ pโ pโ

include V W

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
/-- A continuous map between two normed affine spaces is an affine map provided that
it sends midpoints to midpoints. -/
def AffineMap.ofMapMidpoint (f : P โ Q) (h : โ x y, f (midpoint โ x y) = midpoint โ (f x) (f y)) (hfc : Continuous f) :
    P โแต[โ] Q :=
  AffineMap.mk' f
    (โ((AddMonoidHom.ofMapMidpoint โ โ
            ((AffineEquiv.vaddConst โ (f <| Classical.arbitrary P)).symm โ
              f โ AffineEquiv.vaddConst โ (Classical.arbitrary P))
            (by
              simp )
            fun x y => by
            simp [โ h]).toRealLinearMap <|
        by
        apply_rules [Continuous.vadd, Continuous.vsub, continuous_const, hfc.comp, continuous_id]))
    (Classical.arbitrary P) fun p => by
    simp

