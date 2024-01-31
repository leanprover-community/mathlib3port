/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo, Yury Kudryashov
-/
import Analysis.NormedSpace.Basic
import Topology.MetricSpace.HausdorffDistance

#align_import analysis.normed_space.riesz_lemma from "leanprover-community/mathlib"@"9a48a083b390d9b84a71efbdc4e8dfa26a687104"

/-!
# Applications of the Hausdorff distance in normed spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Riesz's lemma, stated for a normed space over a normed field: for any
closed proper subspace `F` of `E`, there is a nonzero `x` such that `‖x - F‖`
is at least `r * ‖x‖` for any `r < 1`. This is `riesz_lemma`.

In a nontrivially normed field (with an element `c` of norm `> 1`) and any `R > ‖c‖`, one can
guarantee `‖x‖ ≤ R` and `‖x - y‖ ≥ 1` for any `y` in `F`. This is `riesz_lemma_of_norm_lt`.

A further lemma, `metric.closed_ball_inf_dist_compl_subset_closure`, finds a *closed* ball within
the closure of a set `s` of optimal distance from a point in `x` to the frontier of `s`.
-/


open Set Metric

open scoped Topology

variable {𝕜 : Type _} [NormedField 𝕜]

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {F : Type _} [SeminormedAddCommGroup F] [NormedSpace ℝ F]

#print riesz_lemma /-
/-- Riesz's lemma, which usually states that it is possible to find a
vector with norm 1 whose distance to a closed proper subspace is
arbitrarily close to 1. The statement here is in terms of multiples of
norms, since in general the existence of an element of norm exactly 1
is not guaranteed. For a variant giving an element with norm in `[1, R]`, see
`riesz_lemma_of_norm_lt`. -/
theorem riesz_lemma {F : Subspace 𝕜 E} (hFc : IsClosed (F : Set E)) (hF : ∃ x : E, x ∉ F) {r : ℝ}
    (hr : r < 1) : ∃ x₀ : E, x₀ ∉ F ∧ ∀ y ∈ F, r * ‖x₀‖ ≤ ‖x₀ - y‖ := by classical
#align riesz_lemma riesz_lemma
-/

#print riesz_lemma_of_norm_lt /-
/--
A version of Riesz lemma: given a strict closed subspace `F`, one may find an element of norm `≤ R`
which is at distance  at least `1` of every element of `F`. Here, `R` is any given constant
strictly larger than the norm of an element of norm `> 1`. For a version without an `R`, see
`riesz_lemma`.

Since we are considering a general nontrivially normed field, there may be a gap in possible norms
(for instance no element of norm in `(1,2)`). Hence, we can not allow `R` arbitrarily close to `1`,
and require `R > ‖c‖` for some `c : 𝕜` with norm `> 1`.
-/
theorem riesz_lemma_of_norm_lt {c : 𝕜} (hc : 1 < ‖c‖) {R : ℝ} (hR : ‖c‖ < R) {F : Subspace 𝕜 E}
    (hFc : IsClosed (F : Set E)) (hF : ∃ x : E, x ∉ F) :
    ∃ x₀ : E, ‖x₀‖ ≤ R ∧ ∀ y ∈ F, 1 ≤ ‖x₀ - y‖ :=
  by
  have Rpos : 0 < R := (norm_nonneg _).trans_lt hR
  have : ‖c‖ / R < 1 := by rw [div_lt_iff Rpos]; simpa using hR
  rcases riesz_lemma hFc hF this with ⟨x, xF, hx⟩
  have x0 : x ≠ 0 := fun H => by simpa [H] using xF
  obtain ⟨d, d0, dxlt, ledx, -⟩ :
    ∃ d : 𝕜, d ≠ 0 ∧ ‖d • x‖ < R ∧ R / ‖c‖ ≤ ‖d • x‖ ∧ ‖d‖⁻¹ ≤ R⁻¹ * ‖c‖ * ‖x‖ :=
    rescale_to_shell hc Rpos x0
  refine' ⟨d • x, dxlt.le, fun y hy => _⟩
  set y' := d⁻¹ • y with hy'
  have y'F : y' ∈ F := by simp [hy', Submodule.smul_mem _ _ hy]
  have yy' : y = d • y' := by simp [hy', smul_smul, mul_inv_cancel d0]
  calc
    1 = ‖c‖ / R * (R / ‖c‖) := by field_simp [Rpos.ne', (zero_lt_one.trans hc).ne']
    _ ≤ ‖c‖ / R * ‖d • x‖ := (mul_le_mul_of_nonneg_left ledx (div_nonneg (norm_nonneg _) Rpos.le))
    _ = ‖d‖ * (‖c‖ / R * ‖x‖) := by simp [norm_smul]; ring
    _ ≤ ‖d‖ * ‖x - y'‖ :=
      (mul_le_mul_of_nonneg_left (hx y' (by simp [hy', Submodule.smul_mem _ _ hy])) (norm_nonneg _))
    _ = ‖d • x - y‖ := by simp [yy', ← smul_sub, norm_smul]
#align riesz_lemma_of_norm_lt riesz_lemma_of_norm_lt
-/

#print Metric.closedBall_infDist_compl_subset_closure /-
theorem Metric.closedBall_infDist_compl_subset_closure {x : F} {s : Set F} (hx : x ∈ s) :
    closedBall x (infDist x (sᶜ)) ⊆ closure s :=
  by
  cases' eq_or_ne (inf_dist x (sᶜ)) 0 with h₀ h₀
  · rw [h₀, closed_ball_zero']
    exact closure_mono (singleton_subset_iff.2 hx)
  · rw [← closure_ball x h₀]
    exact closure_mono ball_inf_dist_compl_subset
#align metric.closed_ball_inf_dist_compl_subset_closure Metric.closedBall_infDist_compl_subset_closure
-/

