/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler

! This file was ported from Lean 3 source module number_theory.modular_forms.jacobi_theta
! leanprover-community/mathlib commit 34d3797325d202bd7250431275bb871133cdb611
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Complex.UpperHalfPlane.Basic
import Mathbin.Analysis.SpecialFunctions.Gaussian

/-! # Jacobi's theta function

This file defines the Jacobi theta function

$$\theta(\tau) = \sum_{n \in \mathbb{Z}} \exp (i \pi n ^ 2 \tau),$$

and proves the modular transformation properties `θ (τ + 2) = θ τ` and
`θ (-1 / τ) = (-I * τ) ^ (1 / 2) * θ τ`, using Poisson's summation formula for the latter.
-/


open Complex Real

open Real BigOperators UpperHalfPlane

/-- Jacobi's theta function `∑' (n : ℤ), exp (π * I * n ^ 2 * τ)`. -/
noncomputable def jacobiTheta (τ : ℍ) : ℂ :=
  ∑' n : ℤ, cexp (π * I * n ^ 2 * τ)
#align jacobi_theta jacobiTheta

theorem jacobi_theta_unif_summable {R : ℝ} (hR : 0 < R) :
    ∃ bd : ℤ → ℝ,
      Summable bd ∧ ∀ {τ : ℍ} (hτ : R ≤ τ.im) (n : ℤ), ‖cexp (π * I * n ^ 2 * τ)‖ ≤ bd n :=
  by
  let y := rexp (-π * R)
  have h : y < 1 := exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr pi_pos) hR)
  refine' ⟨fun n => y ^ |n|, summable_int_of_summable_nat _ _, fun τ hτ n => _⟩
  pick_goal 3
  · refine' le_trans _ (_ : y ^ n ^ 2 ≤ y ^ |n|)
    · rw [Complex.norm_eq_abs, Complex.abs_exp]
      have : (↑π * I * n ^ 2 * τ).re = -π * (τ : ℂ).im * n ^ 2 :=
        by
        rw [(by
            push_cast
            ring : ↑π * I * n ^ 2 * τ = ↑(π * n ^ 2) * (τ * I)),
          of_real_mul_re, mul_I_re]
        ring
      obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (sq_nonneg n)
      rw [this, exp_mul, ← Int.cast_pow, rpow_int_cast, hm, zpow_ofNat, zpow_ofNat]
      refine' pow_le_pow_of_le_left (exp_pos _).le (real.exp_le_exp.mpr _) _
      rwa [mul_le_mul_left_of_neg (neg_lt_zero.mpr pi_pos), UpperHalfPlane.coe_im]
    · rw [← inv_inv y, inv_zpow' _ (|n|), inv_zpow' _ (n ^ 2)]
      refine' zpow_le_of_le (one_le_inv (exp_pos _) h.le) (neg_le_neg _)
      rw [Int.abs_eq_natAbs, ← Int.natAbs_sq, ← Nat.cast_pow, Nat.cast_le, sq]
      exact n.nat_abs.le_mul_self
  all_goals
    simp only [abs_neg, Int.abs_coe_nat, zpow_ofNat]
    exact summable_geometric_of_lt_1 (Real.exp_pos _).le h
#align jacobi_theta_unif_summable jacobi_theta_unif_summable

theorem jacobi_theta_summable (τ : ℍ) : Summable fun n : ℤ => cexp (π * I * n ^ 2 * τ) :=
  let ⟨bd, h, h'⟩ := jacobi_theta_unif_summable τ.im_pos
  summable_norm_iff.mp (summable_of_nonneg_of_le (fun n => norm_nonneg _) (h' <| le_refl _) h)
#align jacobi_theta_summable jacobi_theta_summable

theorem jacobiTheta_two_vadd (τ : ℍ) : jacobiTheta ((2 : ℝ) +ᵥ τ) = jacobiTheta τ :=
  by
  refine' tsum_congr fun n => _
  rw [UpperHalfPlane.coe_vadd, of_real_bit0, of_real_one]
  suffices cexp (↑π * I * ↑n ^ 2 * 2) = 1 by rw [mul_add, Complex.exp_add, this, one_mul]
  rw [(by
      push_cast
      ring : ↑π * I * ↑n ^ 2 * 2 = ↑(n ^ 2) * (2 * π * I)),
    Complex.exp_int_mul, Complex.exp_two_pi_mul_i, one_zpow]
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

