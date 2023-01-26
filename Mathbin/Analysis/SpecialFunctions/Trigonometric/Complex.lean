/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson

! This file was ported from Lean 3 source module analysis.special_functions.trigonometric.complex
! leanprover-community/mathlib commit f93c11933efbc3c2f0299e47b8ff83e9b539cbf6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.QuadraticDiscriminant
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathbin.Analysis.Convex.SpecificFunctions

/-!
# Complex trigonometric functions

Basic facts and derivatives for the complex trigonometric functions.

Several facts about the real trigonometric functions have the proofs deferred here, rather than
`analysis.special_functions.trigonometric.basic`,
as they are most easily proved by appealing to the corresponding fact for complex trigonometric
functions, or require additional imports which are not available in that file.
-/


noncomputable section

namespace Complex

open Set Filter

open Real

theorem cos_eq_zero_iff {θ : ℂ} : cos θ = 0 ↔ ∃ k : ℤ, θ = (2 * k + 1) * π / 2 :=
  by
  have h : (exp (θ * I) + exp (-θ * I)) / 2 = 0 ↔ exp (2 * θ * I) = -1 :=
    by
    rw [@div_eq_iff _ _ (exp (θ * I) + exp (-θ * I)) 2 0 two_neZero, zero_mul,
      add_eq_zero_iff_eq_neg, neg_eq_neg_one_mul, ← div_eq_iff (exp_ne_zero _), ← exp_sub]
    field_simp only
    congr 3
    ring
  rw [cos, h, ← exp_pi_mul_I, exp_eq_exp_iff_exists_int, mul_right_comm]
  refine' exists_congr fun x => _
  refine' (iff_of_eq <| congr_arg _ _).trans (mul_right_inj' <| mul_ne_zero two_neZero I_ne_zero)
  field_simp
  ring
#align complex.cos_eq_zero_iff Complex.cos_eq_zero_iff

theorem cos_ne_zero_iff {θ : ℂ} : cos θ ≠ 0 ↔ ∀ k : ℤ, θ ≠ (2 * k + 1) * π / 2 := by
  rw [← not_exists, not_iff_not, cos_eq_zero_iff]
#align complex.cos_ne_zero_iff Complex.cos_ne_zero_iff

theorem sin_eq_zero_iff {θ : ℂ} : sin θ = 0 ↔ ∃ k : ℤ, θ = k * π :=
  by
  rw [← Complex.cos_sub_pi_div_two, cos_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    use k + 1
    field_simp [eq_add_of_sub_eq hk]
    ring
  · rintro ⟨k, rfl⟩
    use k - 1
    field_simp
    ring
#align complex.sin_eq_zero_iff Complex.sin_eq_zero_iff

theorem sin_ne_zero_iff {θ : ℂ} : sin θ ≠ 0 ↔ ∀ k : ℤ, θ ≠ k * π := by
  rw [← not_exists, not_iff_not, sin_eq_zero_iff]
#align complex.sin_ne_zero_iff Complex.sin_ne_zero_iff

theorem tan_eq_zero_iff {θ : ℂ} : tan θ = 0 ↔ ∃ k : ℤ, θ = k * π / 2 :=
  by
  have h := (sin_two_mul θ).symm
  rw [mul_assoc] at h
  rw [tan, div_eq_zero_iff, ← mul_eq_zero, ← zero_mul (1 / 2 : ℂ), mul_one_div,
    CancelFactors.cancel_factors_eq_div h two_neZero, mul_comm]
  simpa only [zero_div, zero_mul, Ne.def, not_false_iff, field_simps] using sin_eq_zero_iff
#align complex.tan_eq_zero_iff Complex.tan_eq_zero_iff

theorem tan_ne_zero_iff {θ : ℂ} : tan θ ≠ 0 ↔ ∀ k : ℤ, θ ≠ k * π / 2 := by
  rw [← not_exists, not_iff_not, tan_eq_zero_iff]
#align complex.tan_ne_zero_iff Complex.tan_ne_zero_iff

theorem tan_int_mul_pi_div_two (n : ℤ) : tan (n * π / 2) = 0 :=
  tan_eq_zero_iff.mpr (by use n)
#align complex.tan_int_mul_pi_div_two Complex.tan_int_mul_pi_div_two

theorem cos_eq_cos_iff {x y : ℂ} : cos x = cos y ↔ ∃ k : ℤ, y = 2 * k * π + x ∨ y = 2 * k * π - x :=
  calc
    cos x = cos y ↔ cos x - cos y = 0 := sub_eq_zero.symm
    _ ↔ -2 * sin ((x + y) / 2) * sin ((x - y) / 2) = 0 := by rw [cos_sub_cos]
    _ ↔ sin ((x + y) / 2) = 0 ∨ sin ((x - y) / 2) = 0 := by simp [(by norm_num : (2 : ℂ) ≠ 0)]
    _ ↔ sin ((x - y) / 2) = 0 ∨ sin ((x + y) / 2) = 0 := or_comm
    _ ↔ (∃ k : ℤ, y = 2 * k * π + x) ∨ ∃ k : ℤ, y = 2 * k * π - x :=
      by
      apply or_congr <;>
        field_simp [sin_eq_zero_iff, (by norm_num : -(2 : ℂ) ≠ 0), eq_sub_iff_add_eq',
          sub_eq_iff_eq_add, mul_comm (2 : ℂ), mul_right_comm _ (2 : ℂ)]
      constructor <;>
        · rintro ⟨k, rfl⟩
          use -k
          simp
    _ ↔ ∃ k : ℤ, y = 2 * k * π + x ∨ y = 2 * k * π - x := exists_or.symm
    
#align complex.cos_eq_cos_iff Complex.cos_eq_cos_iff

theorem sin_eq_sin_iff {x y : ℂ} :
    sin x = sin y ↔ ∃ k : ℤ, y = 2 * k * π + x ∨ y = (2 * k + 1) * π - x :=
  by
  simp only [← Complex.cos_sub_pi_div_two, cos_eq_cos_iff, sub_eq_iff_eq_add]
  refine' exists_congr fun k => or_congr _ _ <;> refine' Eq.congr rfl _ <;> field_simp <;> ring
#align complex.sin_eq_sin_iff Complex.sin_eq_sin_iff

theorem tan_add {x y : ℂ}
    (h :
      ((∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, y ≠ (2 * l + 1) * π / 2) ∨
        (∃ k : ℤ, x = (2 * k + 1) * π / 2) ∧ ∃ l : ℤ, y = (2 * l + 1) * π / 2) :
    tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) :=
  by
  rcases h with (⟨h1, h2⟩ | ⟨⟨k, rfl⟩, ⟨l, rfl⟩⟩)
  · rw [tan, sin_add, cos_add, ←
      div_div_div_cancel_right (sin x * cos y + cos x * sin y)
        (mul_ne_zero (cos_ne_zero_iff.mpr h1) (cos_ne_zero_iff.mpr h2)),
      add_div, sub_div]
    simp only [← div_mul_div_comm, ← tan, mul_one, one_mul, div_self (cos_ne_zero_iff.mpr h1),
      div_self (cos_ne_zero_iff.mpr h2)]
  · obtain ⟨t, hx, hy, hxy⟩ := tan_int_mul_pi_div_two, t (2 * k + 1), t (2 * l + 1),
      t (2 * k + 1 + (2 * l + 1))
    simp only [Int.cast_add, Int.cast_bit0, Int.cast_mul, Int.cast_one, hx, hy] at hx hy hxy
    rw [hx, hy, add_zero, zero_div, mul_div_assoc, mul_div_assoc, ←
      add_mul (2 * (k : ℂ) + 1) (2 * l + 1) (π / 2), ← mul_div_assoc, hxy]
#align complex.tan_add Complex.tan_add

theorem tan_add' {x y : ℂ}
    (h : (∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, y ≠ (2 * l + 1) * π / 2) :
    tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) :=
  tan_add (Or.inl h)
#align complex.tan_add' Complex.tan_add'

theorem tan_two_mul {z : ℂ} : tan (2 * z) = 2 * tan z / (1 - tan z ^ 2) :=
  by
  by_cases h : ∀ k : ℤ, z ≠ (2 * k + 1) * π / 2
  · rw [two_mul, two_mul, sq, tan_add (Or.inl ⟨h, h⟩)]
  · rw [not_forall_not] at h
    rw [two_mul, two_mul, sq, tan_add (Or.inr ⟨h, h⟩)]
#align complex.tan_two_mul Complex.tan_two_mul

theorem tan_add_mul_i {x y : ℂ}
    (h :
      ((∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, y * I ≠ (2 * l + 1) * π / 2) ∨
        (∃ k : ℤ, x = (2 * k + 1) * π / 2) ∧ ∃ l : ℤ, y * I = (2 * l + 1) * π / 2) :
    tan (x + y * I) = (tan x + tanh y * I) / (1 - tan x * tanh y * I) := by
  rw [tan_add h, tan_mul_I, mul_assoc]
#align complex.tan_add_mul_I Complex.tan_add_mul_i

theorem tan_eq {z : ℂ}
    (h :
      ((∀ k : ℤ, (z.re : ℂ) ≠ (2 * k + 1) * π / 2) ∧
          ∀ l : ℤ, (z.im : ℂ) * I ≠ (2 * l + 1) * π / 2) ∨
        (∃ k : ℤ, (z.re : ℂ) = (2 * k + 1) * π / 2) ∧
          ∃ l : ℤ, (z.im : ℂ) * I = (2 * l + 1) * π / 2) :
    tan z = (tan z.re + tanh z.im * I) / (1 - tan z.re * tanh z.im * I) := by
  convert tan_add_mul_I h <;> exact (re_add_im z).symm
#align complex.tan_eq Complex.tan_eq

open TopologicalSpace

theorem continuousOn_tan : ContinuousOn tan { x | cos x ≠ 0 } :=
  continuousOn_sin.div continuousOn_cos fun x => id
#align complex.continuous_on_tan Complex.continuousOn_tan

@[continuity]
theorem continuous_tan : Continuous fun x : { x | cos x ≠ 0 } => tan x :=
  continuousOn_iff_continuous_restrict.1 continuousOn_tan
#align complex.continuous_tan Complex.continuous_tan

theorem cos_eq_iff_quadratic {z w : ℂ} :
    cos z = w ↔ exp (z * I) ^ 2 - 2 * w * exp (z * I) + 1 = 0 :=
  by
  rw [← sub_eq_zero]
  field_simp [cos, exp_neg, exp_ne_zero]
  refine' Eq.congr _ rfl
  ring
#align complex.cos_eq_iff_quadratic Complex.cos_eq_iff_quadratic

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (w «expr ≠ » 0) -/
theorem cos_surjective : Function.Surjective cos :=
  by
  intro x
  obtain ⟨w, w₀, hw⟩ : ∃ (w : _)(_ : w ≠ 0), 1 * w * w + -2 * x * w + 1 = 0 :=
    by
    rcases exists_quadratic_eq_zero one_neZero
        ⟨_, (cpow_nat_inv_pow _ two_neZero).symm.trans <| pow_two _⟩ with
      ⟨w, hw⟩
    refine' ⟨w, _, hw⟩
    rintro rfl
    simpa only [zero_add, one_neZero, mul_zero] using hw
  refine' ⟨log w / I, cos_eq_iff_quadratic.2 _⟩
  rw [div_mul_cancel _ I_ne_zero, exp_log w₀]
  convert hw
  ring
#align complex.cos_surjective Complex.cos_surjective

@[simp]
theorem range_cos : range cos = Set.univ :=
  cos_surjective.range_eq
#align complex.range_cos Complex.range_cos

theorem sin_surjective : Function.Surjective sin :=
  by
  intro x
  rcases cos_surjective x with ⟨z, rfl⟩
  exact ⟨z + π / 2, sin_add_pi_div_two z⟩
#align complex.sin_surjective Complex.sin_surjective

@[simp]
theorem range_sin : range sin = Set.univ :=
  sin_surjective.range_eq
#align complex.range_sin Complex.range_sin

end Complex

namespace Real

open Real

theorem cos_eq_zero_iff {θ : ℝ} : cos θ = 0 ↔ ∃ k : ℤ, θ = (2 * k + 1) * π / 2 := by
  exact_mod_cast @Complex.cos_eq_zero_iff θ
#align real.cos_eq_zero_iff Real.cos_eq_zero_iff

theorem cos_ne_zero_iff {θ : ℝ} : cos θ ≠ 0 ↔ ∀ k : ℤ, θ ≠ (2 * k + 1) * π / 2 := by
  rw [← not_exists, not_iff_not, cos_eq_zero_iff]
#align real.cos_ne_zero_iff Real.cos_ne_zero_iff

theorem cos_eq_cos_iff {x y : ℝ} : cos x = cos y ↔ ∃ k : ℤ, y = 2 * k * π + x ∨ y = 2 * k * π - x :=
  by exact_mod_cast @Complex.cos_eq_cos_iff x y
#align real.cos_eq_cos_iff Real.cos_eq_cos_iff

theorem sin_eq_sin_iff {x y : ℝ} :
    sin x = sin y ↔ ∃ k : ℤ, y = 2 * k * π + x ∨ y = (2 * k + 1) * π - x := by
  exact_mod_cast @Complex.sin_eq_sin_iff x y
#align real.sin_eq_sin_iff Real.sin_eq_sin_iff

theorem lt_sin_mul {x : ℝ} (hx : 0 < x) (hx' : x < 1) : x < sin (π / 2 * x) := by
  simpa [mul_comm x] using
    strictConcaveOn_sin_icc.2 ⟨le_rfl, pi_pos.le⟩ ⟨pi_div_two_pos.le, half_le_self pi_pos.le⟩
      pi_div_two_pos.ne (sub_pos.2 hx') hx
#align real.lt_sin_mul Real.lt_sin_mul

theorem le_sin_mul {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) : x ≤ sin (π / 2 * x) := by
  simpa [mul_comm x] using
    strict_concave_on_sin_Icc.concave_on.2 ⟨le_rfl, pi_pos.le⟩
      ⟨pi_div_two_pos.le, half_le_self pi_pos.le⟩ (sub_nonneg.2 hx') hx
#align real.le_sin_mul Real.le_sin_mul

theorem mul_lt_sin {x : ℝ} (hx : 0 < x) (hx' : x < π / 2) : 2 / π * x < sin x :=
  by
  rw [← inv_div]
  simpa [-inv_div, pi_div_two_pos.ne'] using @lt_sin_mul ((π / 2)⁻¹ * x) _ _
  · exact mul_pos (inv_pos.2 pi_div_two_pos) hx
  · rwa [← div_eq_inv_mul, div_lt_one pi_div_two_pos]
#align real.mul_lt_sin Real.mul_lt_sin

/-- In the range `[0, π / 2]`, we have a linear lower bound on `sin`. This inequality forms one half
of Jordan's inequality, the other half is `real.sin_lt` -/
theorem mul_le_sin {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ π / 2) : 2 / π * x ≤ sin x :=
  by
  rw [← inv_div]
  simpa [-inv_div, pi_div_two_pos.ne'] using @le_sin_mul ((π / 2)⁻¹ * x) _ _
  · exact mul_nonneg (inv_nonneg.2 pi_div_two_pos.le) hx
  · rwa [← div_eq_inv_mul, div_le_one pi_div_two_pos]
#align real.mul_le_sin Real.mul_le_sin

end Real

