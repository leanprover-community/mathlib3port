/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module analysis.analytic.radius_liminf
! leanprover-community/mathlib commit 1f0096e6caa61e9c849ec2adbd227e960e9dff58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Analytic.Basic
import Mathbin.Analysis.SpecialFunctions.Pow

/-!
# Representation of `formal_multilinear_series.radius` as a `liminf`

In this file we prove that the radius of convergence of a `formal_multilinear_series` is equal to
$\liminf_{n\to\infty} \frac{1}{\sqrt[n]{‖p n‖}}$. This lemma can't go to `basic.lean` because this
would create a circular dependency once we redefine `exp` using `formal_multilinear_series`.
-/


variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open TopologicalSpace Classical BigOperators Nnreal Ennreal

open Filter Asymptotics

namespace FormalMultilinearSeries

variable (p : FormalMultilinearSeries 𝕜 E F)

/-- The radius of a formal multilinear series is equal to
$\liminf_{n\to\infty} \frac{1}{\sqrt[n]{‖p n‖}}$. The actual statement uses `ℝ≥0` and some
coercions. -/
theorem radius_eq_liminf : p.radius = liminf (fun n => 1 / (‖p n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0)) atTop :=
  by
  have :
    ∀ (r : ℝ≥0) {n : ℕ},
      0 < n → ((r : ℝ≥0∞) ≤ 1 / ↑(‖p n‖₊ ^ (1 / (n : ℝ))) ↔ ‖p n‖₊ * r ^ n ≤ 1) :=
    by
    intro r n hn
    have : 0 < (n : ℝ) := Nat.cast_pos.2 hn
    conv_lhs =>
      rw [one_div, Ennreal.le_inv_iff_mul_le, ← Ennreal.coe_mul, Ennreal.coe_le_one_iff, one_div, ←
        Nnreal.rpow_one r, ← mul_inv_cancel this.ne', Nnreal.rpow_mul, ← Nnreal.mul_rpow, ←
        Nnreal.one_rpow n⁻¹, Nnreal.rpow_le_rpow_iff (inv_pos.2 this), mul_comm,
        Nnreal.rpow_nat_cast]
  apply le_antisymm <;> refine' Ennreal.le_of_forall_nnreal_lt fun r hr => _
  · rcases((tFAE_exists_lt_isO_pow (fun n => ‖p n‖ * r ^ n) 1).out 1 7).1
        (p.is_o_of_lt_radius hr) with ⟨a, ha, H⟩
    refine' le_Liminf_of_le (by infer_param) (eventually_map.2 <| _)
    refine'
      H.mp ((eventually_gt_at_top 0).mono fun n hn₀ hn => (this _ hn₀).2 (Nnreal.coe_le_coe.1 _))
    push_cast
    exact (le_abs_self _).trans (hn.trans (pow_le_one _ ha.1.le ha.2.le))
  · refine' p.le_radius_of_is_O (is_O.of_bound 1 _)
    refine' (eventually_lt_of_lt_liminf hr).mp ((eventually_gt_at_top 0).mono fun n hn₀ hn => _)
    simpa using Nnreal.coe_le_coe.2 ((this _ hn₀).1 hn.le)
#align formal_multilinear_series.radius_eq_liminf FormalMultilinearSeries.radius_eq_liminf

end FormalMultilinearSeries

