/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module topology.instances.int
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Int.Interval
import Mathbin.Topology.MetricSpace.Basic
import Mathbin.Order.Filter.Archimedean

/-!
# Topology on the integers

The structure of a metric space on `ℤ` is introduced in this file, induced from `ℝ`.
-/


noncomputable section

open Metric Set Filter

namespace Int

instance : HasDist ℤ :=
  ⟨fun x y => dist (x : ℝ) y⟩

theorem dist_eq (x y : ℤ) : dist x y = |x - y| :=
  rfl
#align int.dist_eq Int.dist_eq

@[norm_cast, simp]
theorem dist_cast_real (x y : ℤ) : dist (x : ℝ) y = dist x y :=
  rfl
#align int.dist_cast_real Int.dist_cast_real

theorem pairwise_one_le_dist : Pairwise fun m n : ℤ => 1 ≤ dist m n :=
  by
  intro m n hne
  rw [dist_eq]; norm_cast; rwa [← zero_add (1 : ℤ), Int.add_one_le_iff, abs_pos, sub_ne_zero]
#align int.pairwise_one_le_dist Int.pairwise_one_le_dist

theorem uniformEmbedding_coe_real : UniformEmbedding (coe : ℤ → ℝ) :=
  uniformEmbedding_bot_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist
#align int.uniform_embedding_coe_real Int.uniformEmbedding_coe_real

theorem closedEmbedding_coe_real : ClosedEmbedding (coe : ℤ → ℝ) :=
  closedEmbedding_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist
#align int.closed_embedding_coe_real Int.closedEmbedding_coe_real

instance : MetricSpace ℤ :=
  Int.uniformEmbedding_coe_real.comapMetricSpace _

theorem preimage_ball (x : ℤ) (r : ℝ) : coe ⁻¹' ball (x : ℝ) r = ball x r :=
  rfl
#align int.preimage_ball Int.preimage_ball

theorem preimage_closedBall (x : ℤ) (r : ℝ) : coe ⁻¹' closedBall (x : ℝ) r = closedBall x r :=
  rfl
#align int.preimage_closed_ball Int.preimage_closedBall

theorem ball_eq_ioo (x : ℤ) (r : ℝ) : ball x r = Ioo ⌊↑x - r⌋ ⌈↑x + r⌉ := by
  rw [← preimage_ball, Real.ball_eq_ioo, preimage_Ioo]
#align int.ball_eq_Ioo Int.ball_eq_ioo

theorem closedBall_eq_icc (x : ℤ) (r : ℝ) : closedBall x r = Icc ⌈↑x - r⌉ ⌊↑x + r⌋ := by
  rw [← preimage_closed_ball, Real.closedBall_eq_icc, preimage_Icc]
#align int.closed_ball_eq_Icc Int.closedBall_eq_icc

instance : ProperSpace ℤ :=
  ⟨by
    intro x r
    rw [closed_ball_eq_Icc]
    exact (Set.finite_Icc _ _).IsCompact⟩

@[simp]
theorem cocompact_eq : cocompact ℤ = at_bot ⊔ at_top := by
  simp only [← comap_dist_right_atTop_eq_cocompact (0 : ℤ), dist_eq, sub_zero, cast_zero, ←
    cast_abs, ← @comap_comap _ _ _ _ abs, Int.comap_cast_atTop, comap_abs_at_top]
#align int.cocompact_eq Int.cocompact_eq

@[simp]
theorem cofinite_eq : (cofinite : Filter ℤ) = at_bot ⊔ at_top := by
  rw [← cocompact_eq_cofinite, cocompact_eq]
#align int.cofinite_eq Int.cofinite_eq

end Int

