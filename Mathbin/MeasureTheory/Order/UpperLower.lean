/-
Copyright (c) 2022 Yaël Dillies, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kexing Ying
-/
import Analysis.Normed.Order.UpperLower
import Logic.Lemmas
import MeasureTheory.Covering.BesicovitchVectorSpace

#align_import measure_theory.order.upper_lower from "leanprover-community/mathlib"@"b1abe23ae96fef89ad30d9f4362c307f72a55010"

/-!
# Order-connected sets are null-measurable

This file proves that order-connected sets in `ℝⁿ` under the pointwise order are null-measurable.
Recall that `x ≤ y` iff `∀ i, x i ≤ y i`, and `s` is order-connected iff
`∀ x y ∈ s, ∀ z, x ≤ z → z ≤ y → z ∈ s`.

## Main declarations

* `set.ord_connected.null_frontier`: The frontier of an order-connected set in `ℝⁿ` has measure `0`.

## Notes

We prove null-measurability in `ℝⁿ` with the `∞`-metric, but this transfers directly to `ℝⁿ` with
the Euclidean metric because they have the same measurable sets.

Null-measurability can't be strengthened to measurability because any antichain (and in particular
any subset of the antidiagonal `{(x, y) | x + y = 0}`) is order-connected.

## TODO

Generalize so that it also applies to `ℝ × ℝ`, for example.
-/


open Filter MeasureTheory Metric Set

open scoped Topology

variable {ι : Type _} [Fintype ι] {s : Set (ι → ℝ)} {x y : ι → ℝ} {δ : ℝ}

/-- If we can fit a small ball inside a set `s` intersected with any neighborhood of `x`, then the
density of `s` near `x` is not `0`. Along with `aux₁`, this proves that `x` is a Lebesgue point of
`s`. This will be used to prove that the frontier of an order-connected set is null. -/
private theorem aux₀
    (h :
      ∀ δ, 0 < δ → ∃ y, closedBall y (δ / 4) ⊆ closedBall x δ ∧ closedBall y (δ / 4) ⊆ interior s) :
    ¬Tendsto (fun r => volume (closure s ∩ closedBall x r) / volume (closedBall x r)) (𝓝[>] 0)
        (𝓝 0) :=
  by
  choose f hf₀ hf₁ using h
  intro H
  obtain ⟨ε, hε, hε', hε₀⟩ := exists_seq_strictAnti_tendsto_nhdsWithin (0 : ℝ)
  refine'
    not_eventually.2
      (frequently_of_forall fun _ => lt_irrefl <| ENNReal.ofReal <| 4⁻¹ ^ Fintype.card ι)
      ((Filter.Tendsto.eventually_lt (H.comp hε₀) tendsto_const_nhds _).mono fun n =>
        lt_of_le_of_lt _)
  swap
  refine'
    (ENNReal.div_le_div_right
          (volume.mono <|
            subset_inter ((hf₁ _ <| hε' n).trans interior_subset_closure) <| hf₀ _ <| hε' n)
          _).trans_eq'
      _
  dsimp
  have := hε' n
  rw [Real.volume_pi_closedBall, Real.volume_pi_closedBall, ← ENNReal.ofReal_div_of_pos, ← div_pow,
    mul_div_mul_left _ _ (two_ne_zero' ℝ), div_right_comm, div_self, one_div]
  all_goals positivity

/-- If we can fit a small ball inside a set `sᶜ` intersected with any neighborhood of `x`, then the
density of `s` near `x` is not `1`. Along with `aux₀`, this proves that `x` is a Lebesgue point of
`s`. This will be used to prove that the frontier of an order-connected set is null. -/
private theorem aux₁
    (h :
      ∀ δ,
        0 < δ → ∃ y, closedBall y (δ / 4) ⊆ closedBall x δ ∧ closedBall y (δ / 4) ⊆ interior (sᶜ)) :
    ¬Tendsto (fun r => volume (closure s ∩ closedBall x r) / volume (closedBall x r)) (𝓝[>] 0)
        (𝓝 1) :=
  by
  choose f hf₀ hf₁ using h
  intro H
  obtain ⟨ε, hε, hε', hε₀⟩ := exists_seq_strictAnti_tendsto_nhdsWithin (0 : ℝ)
  refine'
    not_eventually.2
      (frequently_of_forall fun _ => lt_irrefl <| 1 - ENNReal.ofReal (4⁻¹ ^ Fintype.card ι))
      ((Filter.Tendsto.eventually_lt tendsto_const_nhds (H.comp hε₀) <|
            ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero _).mono
        fun n => lt_of_le_of_lt' _)
  swap
  refine' (ENNReal.div_le_div_right (volume.mono _) _).trans_eq _
  · exact closed_ball x (ε n) \ closed_ball (f (ε n) <| hε' n) (ε n / 4)
  · rw [diff_eq_compl_inter]
    refine' inter_subset_inter_left _ _
    rw [subset_compl_comm, ← interior_compl]
    exact hf₁ _ _
  dsimp
  have := hε' n
  rw [measure_diff (hf₀ _ _) _ ((Real.volume_pi_closedBall _ _).trans_ne ENNReal.ofReal_ne_top),
    Real.volume_pi_closedBall, Real.volume_pi_closedBall, ENNReal.sub_div fun _ _ => _,
    ENNReal.div_self _ ENNReal.ofReal_ne_top, ← ENNReal.ofReal_div_of_pos, ← div_pow,
    mul_div_mul_left _ _ (two_ne_zero' ℝ), div_right_comm, div_self, one_div]
  all_goals
    first
    | positivity
    | measurability

theorem IsUpperSet.null_frontier (hs : IsUpperSet s) : volume (frontier s) = 0 :=
  by
  refine'
    eq_bot_mono (volume.mono fun x hx => _)
      (Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet _ is_closed_closure.measurable_set)
  · exact s
  by_cases x ∈ closure s <;> simp [h]
  ·
    exact
      aux₁ fun _ =>
        hs.compl.exists_subset_ball <| frontier_subset_closure <| by rwa [frontier_compl]
  · exact aux₀ fun _ => hs.exists_subset_ball <| frontier_subset_closure hx
#align is_upper_set.null_frontier IsUpperSet.null_frontier

theorem IsLowerSet.null_frontier (hs : IsLowerSet s) : volume (frontier s) = 0 :=
  by
  refine'
    eq_bot_mono (volume.mono fun x hx => _)
      (Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet _ is_closed_closure.measurable_set)
  · exact s
  by_cases x ∈ closure s <;> simp [h]
  ·
    exact
      aux₁ fun _ =>
        hs.compl.exists_subset_ball <| frontier_subset_closure <| by rwa [frontier_compl]
  · exact aux₀ fun _ => hs.exists_subset_ball <| frontier_subset_closure hx
#align is_lower_set.null_frontier IsLowerSet.null_frontier

theorem Set.OrdConnected.null_frontier (hs : s.OrdConnected) : volume (frontier s) = 0 :=
  by
  rw [← hs.upper_closure_inter_lower_closure]
  refine'
    le_bot_iff.1
      ((volume.mono <|
            (frontier_inter_subset _ _).trans <|
              union_subset_union (inter_subset_left _ _) <| inter_subset_right _ _).trans <|
        (measure_union_le _ _).trans_eq _)
  rw [(UpperSet.upper _).null_frontier, (LowerSet.lower _).null_frontier, zero_add, bot_eq_zero]
#align set.ord_connected.null_frontier Set.OrdConnected.null_frontier

protected theorem Set.OrdConnected.nullMeasurableSet (hs : s.OrdConnected) : NullMeasurableSet s :=
  nullMeasurableSet_of_null_frontier hs.null_frontier
#align set.ord_connected.null_measurable_set Set.OrdConnected.nullMeasurableSet

theorem IsAntichain.volume_eq_zero [Nonempty ι] (hs : IsAntichain (· ≤ ·) s) : volume s = 0 :=
  le_bot_iff.1 <|
    (volume.mono <| by
          rw [← closure_diff_interior, hs.interior_eq_empty, diff_empty]
          exact subset_closure).trans_eq
      hs.OrdConnected.null_frontier
#align is_antichain.volume_eq_zero IsAntichain.volume_eq_zero

