/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module topology.instances.nat
! leanprover-community/mathlib commit ba2245edf0c8bb155f1569fd9b9492a9b384cde6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Instances.Int

/-!
# Topology on the natural numbers

The structure of a metric space on `ℕ` is introduced in this file, induced from `ℝ`.
-/


noncomputable section

open Metric Set Filter

namespace Nat

noncomputable instance : HasDist ℕ :=
  ⟨fun x y => dist (x : ℝ) y⟩

theorem dist_eq (x y : ℕ) : dist x y = |x - y| :=
  rfl
#align nat.dist_eq Nat.dist_eq

theorem dist_coe_int (x y : ℕ) : dist (x : ℤ) (y : ℤ) = dist x y :=
  rfl
#align nat.dist_coe_int Nat.dist_coe_int

@[norm_cast, simp]
theorem dist_cast_real (x y : ℕ) : dist (x : ℝ) y = dist x y :=
  rfl
#align nat.dist_cast_real Nat.dist_cast_real

theorem pairwise_one_le_dist : Pairwise fun m n : ℕ => 1 ≤ dist m n := by
  intro m n hne
  rw [← dist_coe_int]
  apply Int.pairwise_one_le_dist
  exact_mod_cast hne
#align nat.pairwise_one_le_dist Nat.pairwise_one_le_dist

theorem uniform_embedding_coe_real : UniformEmbedding (coe : ℕ → ℝ) :=
  uniform_embedding_bot_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist
#align nat.uniform_embedding_coe_real Nat.uniform_embedding_coe_real

theorem closed_embedding_coe_real : ClosedEmbedding (coe : ℕ → ℝ) :=
  closed_embedding_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist
#align nat.closed_embedding_coe_real Nat.closed_embedding_coe_real

instance : MetricSpace ℕ :=
  Nat.uniform_embedding_coe_real.comapMetricSpace _

theorem preimage_ball (x : ℕ) (r : ℝ) : coe ⁻¹' ball (x : ℝ) r = ball x r :=
  rfl
#align nat.preimage_ball Nat.preimage_ball

theorem preimage_closed_ball (x : ℕ) (r : ℝ) : coe ⁻¹' closedBall (x : ℝ) r = closedBall x r :=
  rfl
#align nat.preimage_closed_ball Nat.preimage_closed_ball

theorem closed_ball_eq_Icc (x : ℕ) (r : ℝ) : closedBall x r = Icc ⌈↑x - r⌉₊ ⌊↑x + r⌋₊ := by
  rcases le_or_lt 0 r with (hr | hr)
  · rw [← preimage_closed_ball, Real.closed_ball_eq_Icc, preimage_Icc]
    exact add_nonneg (cast_nonneg x) hr
  · rw [closed_ball_eq_empty.2 hr]
    apply (Icc_eq_empty _).symm
    rw [not_le]
    calc
      ⌊(x : ℝ) + r⌋₊ ≤ ⌊(x : ℝ)⌋₊ := by 
        apply floor_mono
        linarith
      _ < ⌈↑x - r⌉₊ := by 
        rw [floor_coe, Nat.lt_ceil]
        linarith
      
#align nat.closed_ball_eq_Icc Nat.closed_ball_eq_Icc

instance : ProperSpace ℕ :=
  ⟨by 
    intro x r
    rw [closed_ball_eq_Icc]
    exact (Set.finite_Icc _ _).IsCompact⟩

instance : NoncompactSpace ℕ :=
  noncompact_space_of_ne_bot <| by simp [Filter.at_top_ne_bot]

end Nat

