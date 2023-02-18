/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module analysis.normed_space.triv_sq_zero_ext
! leanprover-community/mathlib commit 2738d2ca56cbc63be80c3bd48e9ed90ad94e947d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.NormedSpace.Basic
import Mathbin.Analysis.NormedSpace.Exponential
import Mathbin.Topology.Instances.TrivSqZeroExt

/-!
# Results on `triv_sq_zero_ext R M` related to the norm

For now, this file contains results about `exp` for this type.

TODO: actually define a sensible norm on `triv_sq_zero_ext R M`, so that we have access to lemmas
like `exp_add`.

## Main results

* `triv_sq_zero_ext.fst_exp`
* `triv_sq_zero_ext.snd_exp`
* `triv_sq_zero_ext.exp_inl`
* `triv_sq_zero_ext.exp_inr`

-/


variable (𝕜 : Type _) {R M : Type _}

-- mathport name: exprtsze
local notation "tsze" => TrivSqZeroExt

namespace TrivSqZeroExt

section Topology

variable [TopologicalSpace R] [TopologicalSpace M]

/-- If `exp R x.fst` converges to `e` then `exp R x` converges to `inl e + inr (e • x.snd)`. -/
theorem hasSum_expSeries [Field 𝕜] [CharZero 𝕜] [CommRing R] [AddCommGroup M] [Algebra 𝕜 R]
    [Module R M] [Module 𝕜 M] [IsScalarTower 𝕜 R M] [TopologicalRing R] [TopologicalAddGroup M]
    [ContinuousSMul R M] (x : tsze R M) {e : R}
    (h : HasSum (fun n => expSeries 𝕜 R n fun _ => x.fst) e) :
    HasSum (fun n => expSeries 𝕜 (tsze R M) n fun _ => x) (inl e + inr (e • x.snd)) :=
  by
  simp_rw [expSeries_apply_eq] at *
  conv =>
    congr
    ext
    rw [← inl_fst_add_inr_snd_eq (x ^ _), fst_pow, snd_pow, smul_add, ← inr_smul, ← inl_smul,
      nsmul_eq_smul_cast 𝕜 n, smul_smul, inv_mul_eq_div, ← inv_div, ← smul_assoc]
  refine' (has_sum_inl M h).add (has_sum_inr M _)
  apply HasSum.smul_const
  rw [← hasSum_nat_add_iff' 1]; swap; infer_instance
  rw [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, div_zero, inv_zero, zero_smul,
    sub_zero]
  simp_rw [← Nat.succ_eq_add_one, Nat.pred_succ, Nat.factorial_succ, Nat.cast_mul, ←
    Nat.succ_eq_add_one,
    mul_div_cancel_left _ ((@Nat.cast_ne_zero 𝕜 _ _ _).mpr <| Nat.succ_ne_zero _)]
  exact h
#align triv_sq_zero_ext.has_sum_exp_series TrivSqZeroExt.hasSum_expSeries

end Topology

section NormedRing

variable [IsROrC 𝕜] [NormedCommRing R] [AddCommGroup M]

variable [NormedAlgebra 𝕜 R] [Module R M] [Module 𝕜 M] [IsScalarTower 𝕜 R M]

variable [TopologicalSpace M] [TopologicalRing R]

variable [TopologicalAddGroup M] [ContinuousSMul R M]

variable [CompleteSpace R] [T2Space R] [T2Space M]

theorem exp_def (x : tsze R M) : exp 𝕜 x = inl (exp 𝕜 x.fst) + inr (exp 𝕜 x.fst • x.snd) :=
  by
  simp_rw [exp, FormalMultilinearSeries.sum]
  refine' (has_sum_exp_series 𝕜 x _).tsum_eq
  exact expSeries_hasSum_exp _
#align triv_sq_zero_ext.exp_def TrivSqZeroExt.exp_def

@[simp]
theorem fst_exp (x : tsze R M) : fst (exp 𝕜 x) = exp 𝕜 x.fst := by
  rw [exp_def, fst_add, fst_inl, fst_inr, add_zero]
#align triv_sq_zero_ext.fst_exp TrivSqZeroExt.fst_exp

@[simp]
theorem snd_exp (x : tsze R M) : snd (exp 𝕜 x) = exp 𝕜 x.fst • x.snd := by
  rw [exp_def, snd_add, snd_inl, snd_inr, zero_add]
#align triv_sq_zero_ext.snd_exp TrivSqZeroExt.snd_exp

@[simp]
theorem exp_inl (x : R) : exp 𝕜 (inl x : tsze R M) = inl (exp 𝕜 x) := by
  rw [exp_def, fst_inl, snd_inl, smul_zero, inr_zero, add_zero]
#align triv_sq_zero_ext.exp_inl TrivSqZeroExt.exp_inl

@[simp]
theorem exp_inr (m : M) : exp 𝕜 (inr m : tsze R M) = 1 + inr m := by
  rw [exp_def, fst_inr, exp_zero, snd_inr, one_smul, inl_one]
#align triv_sq_zero_ext.exp_inr TrivSqZeroExt.exp_inr

/-- Polar form of trivial-square-zero extension. -/
theorem eq_smul_exp_of_invertible (x : tsze R M) [Invertible x.fst] :
    x = x.fst • exp 𝕜 (⅟ x.fst • inr x.snd) := by
  rw [← inr_smul, exp_inr, smul_add, ← inl_one, ← inl_smul, ← inr_smul, smul_eq_mul, mul_one,
    smul_smul, mul_invOf_self, one_smul, inl_fst_add_inr_snd_eq]
#align triv_sq_zero_ext.eq_smul_exp_of_invertible TrivSqZeroExt.eq_smul_exp_of_invertible

end NormedRing

section NormedField

variable [IsROrC 𝕜] [NormedField R] [AddCommGroup M]

variable [NormedAlgebra 𝕜 R] [Module R M] [Module 𝕜 M] [IsScalarTower 𝕜 R M]

variable [TopologicalSpace M] [TopologicalRing R]

variable [TopologicalAddGroup M] [ContinuousSMul R M]

variable [CompleteSpace R] [T2Space R] [T2Space M]

/-- More convenient version of `triv_sq_zero_ext.eq_smul_exp_of_invertible` for when `R` is a
field. -/
theorem eq_smul_exp_of_ne_zero (x : tsze R M) (hx : x.fst ≠ 0) :
    x = x.fst • exp 𝕜 (x.fst⁻¹ • inr x.snd) :=
  letI : Invertible x.fst := invertibleOfNonzero hx
  eq_smul_exp_of_invertible _ _
#align triv_sq_zero_ext.eq_smul_exp_of_ne_zero TrivSqZeroExt.eq_smul_exp_of_ne_zero

end NormedField

end TrivSqZeroExt

