/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Analysis.Normed.Group.Basic
import Mathbin.Topology.MetricSpace.HausdorffDistance

/-!
# Properties of pointwise addition of sets in normed groups.

We explore the relationships between pointwise addition of sets in normed groups, and the norm.
Notably, we show that the sum of bounded sets remain bounded.
-/


open Metric Set

open Pointwise TopologicalSpace

section SemiNormedGroup

variable {E : Type _} [SemiNormedGroup E]

theorem bounded_iff_exists_norm_le {s : Set E} : Bounded s ↔ ∃ R, ∀, ∀ x ∈ s, ∀, ∥x∥ ≤ R := by
  simp [subset_def, bounded_iff_subset_ball (0 : E)]

alias bounded_iff_exists_norm_le ↔ Metric.Bounded.exists_norm_le _

theorem Metric.Bounded.exists_pos_norm_le {s : Set E} (hs : Metric.Bounded s) : ∃ R > 0, ∀, ∀ x ∈ s, ∀, ∥x∥ ≤ R := by
  obtain ⟨R₀, hR₀⟩ := hs.exists_norm_le
  refine' ⟨max R₀ 1, _, _⟩
  · exact
      (by
            norm_num : (0 : ℝ) < 1).trans_le
        (le_max_rightₓ R₀ 1)
    
  intro x hx
  exact (hR₀ x hx).trans (le_max_leftₓ _ _)

theorem Metric.Bounded.add {s t : Set E} (hs : Bounded s) (ht : Bounded t) : Bounded (s + t) := by
  obtain ⟨Rs, hRs⟩ : ∃ R : ℝ, ∀, ∀ x ∈ s, ∀, ∥x∥ ≤ R := hs.exists_norm_le
  obtain ⟨Rt, hRt⟩ : ∃ R : ℝ, ∀, ∀ x ∈ t, ∀, ∥x∥ ≤ R := ht.exists_norm_le
  refine' bounded_iff_exists_norm_le.2 ⟨Rs + Rt, _⟩
  rintro z ⟨x, y, hx, hy, rfl⟩
  calc ∥x + y∥ ≤ ∥x∥ + ∥y∥ := norm_add_le _ _ _ ≤ Rs + Rt := add_le_add (hRs x hx) (hRt y hy)

@[simp]
theorem singleton_add_ball (x y : E) (r : ℝ) : {x} + Ball y r = Ball (x + y) r := by
  simp only [preimage_add_ball, image_add_left, singleton_add, sub_neg_eq_add, add_commₓ y x]

@[simp]
theorem ball_add_singleton (x y : E) (r : ℝ) : Ball x r + {y} = Ball (x + y) r := by
  simp [add_commₓ _ {y}, add_commₓ y]

theorem singleton_add_ball_zero (x : E) (r : ℝ) : {x} + Ball 0 r = Ball x r := by
  simp

theorem ball_zero_add_singleton (x : E) (r : ℝ) : Ball 0 r + {x} = Ball x r := by
  simp

@[simp]
theorem singleton_add_closed_ball (x y : E) (r : ℝ) : {x} + ClosedBall y r = ClosedBall (x + y) r := by
  simp only [add_commₓ y x, preimage_add_closed_ball, image_add_left, singleton_add, sub_neg_eq_add]

@[simp]
theorem closed_ball_add_singleton (x y : E) (r : ℝ) : ClosedBall x r + {y} = ClosedBall (x + y) r := by
  simp [add_commₓ _ {y}, add_commₓ y]

theorem singleton_add_closed_ball_zero (x : E) (r : ℝ) : {x} + ClosedBall 0 r = ClosedBall x r := by
  simp

theorem closed_ball_zero_add_singleton (x : E) (r : ℝ) : ClosedBall 0 r + {x} = ClosedBall x r := by
  simp

theorem IsCompact.cthickening_eq_add_closed_ball {s : Set E} (hs : IsCompact s) {r : ℝ} (hr : 0 ≤ r) :
    Cthickening r s = s + ClosedBall 0 r := by
  rw [hs.cthickening_eq_bUnion_closed_ball hr]
  ext x
  simp only [mem_add, dist_eq_norm, exists_prop, mem_Union, mem_closed_ball, exists_and_distrib_left,
    mem_closed_ball_zero_iff, ← eq_sub_iff_add_eq', exists_eq_right]

end SemiNormedGroup

