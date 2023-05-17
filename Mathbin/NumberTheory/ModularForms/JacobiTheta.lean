/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler

! This file was ported from Lean 3 source module number_theory.modular_forms.jacobi_theta
! leanprover-community/mathlib commit f0c8bf9245297a541f468be517f1bde6195105e9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Gaussian
import Mathbin.Analysis.Complex.LocallyUniformLimit
import Mathbin.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathbin.Analysis.Complex.UpperHalfPlane.Topology

/-! # Jacobi's theta function

This file defines the Jacobi theta function

$$\theta(\tau) = \sum_{n \in \mathbb{Z}} \exp (i \pi n ^ 2 \tau),$$

and proves the modular transformation properties `θ (τ + 2) = θ τ` and
`θ (-1 / τ) = (-I * τ) ^ (1 / 2) * θ τ`, using Poisson's summation formula for the latter. We also
show that `θ` is differentiable on `ℍ`, and `θ(τ) - 1` has exponential decay as `im τ → ∞`.
-/


open Complex Real Asymptotics

open Real BigOperators UpperHalfPlane Manifold

/-- Jacobi's theta function `∑' (n : ℤ), exp (π * I * n ^ 2 * τ)`. -/
noncomputable def jacobiTheta (τ : ℍ) : ℂ :=
  ∑' n : ℤ, cexp (π * I * n ^ 2 * τ)
#align jacobi_theta jacobiTheta

theorem norm_exp_mul_sq_le {z : ℂ} (hz : 0 < z.im) (n : ℤ) :
    ‖cexp (π * I * n ^ 2 * z)‖ ≤ exp (-π * z.im) ^ n.natAbs :=
  by
  let y := rexp (-π * z.im)
  have h : y < 1 := exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr pi_pos) hz)
  refine' (le_of_eq _).trans (_ : y ^ n ^ 2 ≤ _)
  · rw [Complex.norm_eq_abs, Complex.abs_exp]
    have : (↑π * I * n ^ 2 * z).re = -π * z.im * n ^ 2 :=
      by
      rw [(by
          push_cast
          ring : ↑π * I * n ^ 2 * z = ↑(π * n ^ 2) * (z * I)),
        of_real_mul_re, mul_I_re]
      ring
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (sq_nonneg n)
    rw [this, exp_mul, ← Int.cast_pow, rpow_int_cast, hm, zpow_ofNat]
  · have : n ^ 2 = ↑(n.nat_abs ^ 2) := by rw [Nat.cast_pow, Int.natAbs_sq]
    rw [this, zpow_ofNat]
    exact pow_le_pow_of_le_one (exp_pos _).le h.le ((sq n.nat_abs).symm ▸ n.nat_abs.le_mul_self)
#align norm_exp_mul_sq_le norm_exp_mul_sq_le

theorem exists_summable_bound_exp_mul_sq {R : ℝ} (hR : 0 < R) :
    ∃ bd : ℤ → ℝ,
      Summable bd ∧ ∀ {τ : ℂ} (hτ : R ≤ τ.im) (n : ℤ), ‖cexp (π * I * n ^ 2 * τ)‖ ≤ bd n :=
  by
  let y := rexp (-π * R)
  have h : y < 1 := exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr pi_pos) hR)
  refine' ⟨fun n => y ^ n.natAbs, summable_int_of_summable_nat _ _, fun τ hτ n => _⟩
  pick_goal 3
  · refine' (norm_exp_mul_sq_le (hR.trans_le hτ) n).trans _
    refine' pow_le_pow_of_le_left (exp_pos _).le (real.exp_le_exp.mpr _) _
    rwa [mul_le_mul_left_of_neg (neg_lt_zero.mpr pi_pos)]
  all_goals
    simpa only [Int.natAbs_neg, Int.natAbs_ofNat] using
      summable_geometric_of_lt_1 (Real.exp_pos _).le h
#align exists_summable_bound_exp_mul_sq exists_summable_bound_exp_mul_sq

theorem summable_exp_mul_sq {z : ℂ} (hz : 0 < z.im) :
    Summable fun n : ℤ => cexp (π * I * n ^ 2 * z) :=
  let ⟨bd, h, h'⟩ := exists_summable_bound_exp_mul_sq hz
  summable_norm_iff.mp (summable_of_nonneg_of_le (fun n => norm_nonneg _) (h' <| le_refl _) h)
#align summable_exp_mul_sq summable_exp_mul_sq

theorem jacobiTheta_two_vadd (τ : ℍ) : jacobiTheta ((2 : ℝ) +ᵥ τ) = jacobiTheta τ :=
  by
  refine' tsum_congr fun n => _
  rw [UpperHalfPlane.coe_vadd, of_real_bit0, of_real_one]
  suffices cexp (↑π * I * ↑n ^ 2 * 2) = 1 by rw [mul_add, Complex.exp_add, this, one_mul]
  rw [(by
      push_cast
      ring : ↑π * I * ↑n ^ 2 * 2 = ↑(n ^ 2) * (2 * π * I)),
    Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]
#align jacobi_theta_two_vadd jacobiTheta_two_vadd

theorem jacobiTheta_t_sq_smul (τ : ℍ) : jacobiTheta (ModularGroup.t ^ 2 • τ) = jacobiTheta τ :=
  by
  suffices : (2 : ℝ) +ᵥ τ = ModularGroup.t ^ (2 : ℤ) • τ; exact this ▸ jacobiTheta_two_vadd τ
  simp only [← Subtype.coe_inj, UpperHalfPlane.modular_t_zpow_smul, Int.cast_two]
#align jacobi_theta_T_sq_smul jacobiTheta_t_sq_smul

theorem jacobiTheta_s_smul (τ : ℍ) :
    jacobiTheta (ModularGroup.s • τ) = (-I * τ) ^ (1 / 2 : ℂ) * jacobiTheta τ :=
  by
  unfold jacobiTheta
  rw [UpperHalfPlane.modular_s_smul, UpperHalfPlane.coe_mk]
  have ha : 0 < (-I * τ).re :=
    by
    rw [neg_mul, neg_re, mul_re, I_re, I_im, MulZeroClass.zero_mul, one_mul, zero_sub, neg_neg]
    exact τ.im_pos
  have ha' : (-I * τ) ^ (1 / 2 : ℂ) ≠ 0 :=
    by
    rw [Ne.def, cpow_eq_zero_iff]
    contrapose! ha
    rw [ha.1, zero_re]
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have := Complex.tsum_exp_neg_mul_int_sq ha
  rw [mul_comm ((1 : ℂ) / _) _, mul_one_div, eq_div_iff ha', mul_comm _ (_ ^ _), eq_comm] at this
  convert this using 3
  · ext1 n
    congr 1
    field_simp [hτ, I_ne_zero]
    ring_nf
    rw [I_sq, mul_neg, mul_one, neg_mul, neg_neg]
  · ext1 n
    congr 1
    ring_nf
#align jacobi_theta_S_smul jacobiTheta_s_smul

theorem hasSum_nat_jacobiTheta (τ : ℍ) :
    HasSum (fun n : ℕ => cexp (π * I * (n + 1) ^ 2 * τ)) ((jacobiTheta τ - 1) / 2) :=
  by
  have := (summable_exp_mul_sq τ.im_pos).HasSum.sum_nat_of_sum_int
  rw [← @hasSum_nat_add_iff' ℂ _ _ _ _ 1] at this
  simp_rw [Finset.sum_range_one, Int.cast_neg, Int.cast_ofNat, Nat.cast_zero, neg_zero,
    Int.cast_zero, sq (0 : ℂ), MulZeroClass.mul_zero, MulZeroClass.zero_mul, neg_sq, ← mul_two,
    Complex.exp_zero, add_sub_assoc, (by norm_num : (1 : ℂ) - 1 * 2 = -1), ← sub_eq_add_neg,
    Nat.cast_add, Nat.cast_one] at this
  convert this.div_const 2
  simp_rw [mul_div_cancel _ two_ne_zero]
#align has_sum_nat_jacobi_theta hasSum_nat_jacobiTheta

theorem jacobiTheta_eq_tsum_nat (τ : ℍ) :
    jacobiTheta τ = 1 + 2 * ∑' n : ℕ, cexp (π * I * (n + 1) ^ 2 * τ) := by
  rw [(hasSum_nat_jacobiTheta τ).tsum_eq, mul_div_cancel' _ (two_ne_zero' ℂ), ← add_sub_assoc,
    add_sub_cancel']
#align jacobi_theta_eq_tsum_nat jacobiTheta_eq_tsum_nat

/-- An explicit upper bound for `‖jacobi_theta τ - 1‖`. -/
theorem norm_jacobiTheta_sub_one_le (τ : ℍ) :
    ‖jacobiTheta τ - 1‖ ≤ 2 / (1 - exp (-π * τ.im)) * exp (-π * τ.im) :=
  by
  suffices ‖∑' n : ℕ, cexp (π * I * (n + 1) ^ 2 * τ)‖ ≤ exp (-π * τ.im) / (1 - exp (-π * τ.im)) by
    calc
      ‖jacobiTheta τ - 1‖ = 2 * ‖∑' n : ℕ, cexp (π * I * (n + 1) ^ 2 * τ)‖ := by
        rw [sub_eq_iff_eq_add'.mpr (jacobiTheta_eq_tsum_nat τ), norm_mul, Complex.norm_eq_abs,
          Complex.abs_two]
      _ ≤ 2 * (rexp (-π * τ.im) / (1 - rexp (-π * τ.im))) := by
        rwa [mul_le_mul_left (zero_lt_two' ℝ)]
      _ = 2 / (1 - rexp (-π * τ.im)) * rexp (-π * τ.im) := by rw [div_mul_comm, mul_comm]
      
  have : ∀ n : ℕ, ‖cexp (π * I * (n + 1) ^ 2 * τ)‖ ≤ exp (-π * τ.im) ^ (n + 1) :=
    by
    intro n
    simpa only [Int.cast_add, Int.cast_one] using norm_exp_mul_sq_le τ.im_pos (n + 1)
  have s :
    HasSum (fun n : ℕ => rexp (-π * τ.im) ^ (n + 1)) (exp (-π * τ.im) / (1 - exp (-π * τ.im))) :=
    by
    simp_rw [pow_succ, div_eq_mul_inv, hasSum_mul_left_iff (Real.exp_ne_zero _)]
    exact
      hasSum_geometric_of_lt_1 (exp_pos (-π * τ.im)).le
        (exp_lt_one_iff.mpr <| mul_neg_of_neg_of_pos (neg_lt_zero.mpr pi_pos) τ.im_pos)
  have aux : Summable fun n : ℕ => ‖cexp (↑π * I * (↑n + 1) ^ 2 * ↑τ)‖ :=
    summable_of_nonneg_of_le (fun n => norm_nonneg _) this s.summable
  exact
    (norm_tsum_le_tsum_norm aux).trans ((tsum_mono aux s.summable this).trans (le_of_eq s.tsum_eq))
#align norm_jacobi_theta_sub_one_le norm_jacobiTheta_sub_one_le

/-- The norm of `jacobi_theta τ - 1` decays exponentially as `im τ → ∞`. -/
theorem isBigO_atImInfty_jacobiTheta_sub_one :
    IsBigO UpperHalfPlane.atImInfty (fun τ => jacobiTheta τ - 1) fun τ => rexp (-π * τ.im) :=
  by
  simp_rw [is_O, is_O_with, Filter.Eventually, UpperHalfPlane.atImInfty_mem]
  refine' ⟨2 / (1 - rexp (-π)), 1, fun τ hτ => (norm_jacobiTheta_sub_one_le τ).trans _⟩
  rw [Real.norm_eq_abs, Real.abs_exp]
  refine' mul_le_mul_of_nonneg_right _ (exp_pos _).le
  rw [div_le_div_left (zero_lt_two' ℝ), sub_le_sub_iff_left, exp_le_exp, neg_mul, neg_le_neg_iff]
  · exact le_mul_of_one_le_right pi_pos.le hτ
  · rw [sub_pos, exp_lt_one_iff, neg_mul, neg_lt_zero]
    exact mul_pos pi_pos τ.im_pos
  · rw [sub_pos, exp_lt_one_iff, neg_lt_zero]
    exact pi_pos
#align is_O_at_im_infty_jacobi_theta_sub_one isBigO_atImInfty_jacobiTheta_sub_one

theorem differentiableAt_tsum_exp_mul_sq (τ : ℍ) :
    DifferentiableAt ℂ (fun z => ∑' n : ℤ, cexp (π * I * n ^ 2 * z)) ↑τ :=
  by
  suffices :
    ∀ (y : ℝ) (hy : 0 < y),
      DifferentiableOn ℂ (fun z => ∑' n : ℤ, cexp (π * I * n ^ 2 * z)) { w : ℂ | y < im w }
  exact
    let ⟨y, hy, hy'⟩ := exists_between τ.im_pos
    (this y hy).DifferentiableAt
      ((complex.continuous_im.is_open_preimage _ isOpen_Ioi).mem_nhds (τ.coe_im ▸ hy'))
  intro y hy
  have h1 :
    ∀ (n : ℤ) (w : ℂ) (hw : y < im w),
      DifferentiableWithinAt ℂ (fun v : ℂ => cexp (↑π * I * ↑n ^ 2 * v)) { z : ℂ | y < im z } w :=
    fun n w hw => (differentiable_at_id.const_mul _).cexp.DifferentiableWithinAt
  have h2 : IsOpen { w : ℂ | y < im w } := continuous_im.is_open_preimage _ isOpen_Ioi
  obtain ⟨bd, bd_s, le_bd⟩ := exists_summable_bound_exp_mul_sq hy
  exact differentiable_on_tsum_of_summable_norm bd_s h1 h2 fun i w hw => le_bd (le_of_lt hw) i
#align differentiable_at_tsum_exp_mul_sq differentiableAt_tsum_exp_mul_sq

theorem mdifferentiable_jacobiTheta : Mdifferentiable 𝓘(ℂ) 𝓘(ℂ) jacobiTheta := fun τ =>
  (differentiableAt_tsum_exp_mul_sq τ).MdifferentiableAt.comp τ τ.mdifferentiable_coe
#align mdifferentiable_jacobi_theta mdifferentiable_jacobiTheta

theorem continuous_jacobiTheta : Continuous jacobiTheta :=
  mdifferentiable_jacobiTheta.Continuous
#align continuous_jacobi_theta continuous_jacobiTheta

