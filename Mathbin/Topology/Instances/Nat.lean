/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathbin.Topology.Instances.Int

#align_import topology.instances.nat from "leanprover-community/mathlib"@"f47581155c818e6361af4e4fda60d27d020c226b"

/-!
# Topology on the natural numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The structure of a metric space on `ℕ` is introduced in this file, induced from `ℝ`.
-/


noncomputable section

open Metric Set Filter

namespace Nat

noncomputable instance : Dist ℕ :=
  ⟨fun x y => dist (x : ℝ) y⟩

#print Nat.dist_eq /-
theorem dist_eq (x y : ℕ) : dist x y = |x - y| :=
  rfl
#align nat.dist_eq Nat.dist_eq
-/

#print Nat.dist_coe_int /-
theorem dist_coe_int (x y : ℕ) : dist (x : ℤ) (y : ℤ) = dist x y :=
  rfl
#align nat.dist_coe_int Nat.dist_coe_int
-/

#print Nat.dist_cast_real /-
@[norm_cast, simp]
theorem dist_cast_real (x y : ℕ) : dist (x : ℝ) y = dist x y :=
  rfl
#align nat.dist_cast_real Nat.dist_cast_real
-/

#print Nat.pairwise_one_le_dist /-
theorem pairwise_one_le_dist : Pairwise fun m n : ℕ => 1 ≤ dist m n :=
  by
  intro m n hne
  rw [← dist_coe_int]
  apply Int.pairwise_one_le_dist
  exact_mod_cast hne
#align nat.pairwise_one_le_dist Nat.pairwise_one_le_dist
-/

#print Nat.uniformEmbedding_coe_real /-
theorem uniformEmbedding_coe_real : UniformEmbedding (coe : ℕ → ℝ) :=
  uniformEmbedding_bot_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist
#align nat.uniform_embedding_coe_real Nat.uniformEmbedding_coe_real
-/

#print Nat.closedEmbedding_coe_real /-
theorem closedEmbedding_coe_real : ClosedEmbedding (coe : ℕ → ℝ) :=
  closedEmbedding_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist
#align nat.closed_embedding_coe_real Nat.closedEmbedding_coe_real
-/

instance : MetricSpace ℕ :=
  Nat.uniformEmbedding_coe_real.comapMetricSpace _

#print Nat.preimage_ball /-
theorem preimage_ball (x : ℕ) (r : ℝ) : coe ⁻¹' ball (x : ℝ) r = ball x r :=
  rfl
#align nat.preimage_ball Nat.preimage_ball
-/

#print Nat.preimage_closedBall /-
theorem preimage_closedBall (x : ℕ) (r : ℝ) : coe ⁻¹' closedBall (x : ℝ) r = closedBall x r :=
  rfl
#align nat.preimage_closed_ball Nat.preimage_closedBall
-/

#print Nat.closedBall_eq_Icc /-
theorem closedBall_eq_Icc (x : ℕ) (r : ℝ) : closedBall x r = Icc ⌈↑x - r⌉₊ ⌊↑x + r⌋₊ :=
  by
  rcases le_or_lt 0 r with (hr | hr)
  · rw [← preimage_closed_ball, Real.closedBall_eq_Icc, preimage_Icc]
    exact add_nonneg (cast_nonneg x) hr
  · rw [closed_ball_eq_empty.2 hr]
    apply (Icc_eq_empty _).symm
    rw [not_le]
    calc
      ⌊(x : ℝ) + r⌋₊ ≤ ⌊(x : ℝ)⌋₊ := by apply floor_mono; linarith
      _ < ⌈↑x - r⌉₊ := by rw [floor_coe, Nat.lt_ceil]; linarith
#align nat.closed_ball_eq_Icc Nat.closedBall_eq_Icc
-/

instance : ProperSpace ℕ :=
  ⟨by
    intro x r
    rw [closed_ball_eq_Icc]
    exact (Set.finite_Icc _ _).IsCompact⟩

instance : NoncompactSpace ℕ :=
  noncompactSpace_of_neBot <| by simp [Filter.atTop_neBot]

end Nat

