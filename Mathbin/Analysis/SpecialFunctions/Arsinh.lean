/-
Copyright (c) 2020 James Arthur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Arthur, Chris Hughes, Shing Tak Lam
-/
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathbin.Analysis.SpecialFunctions.Log.Basic

/-!
# Inverse of the sinh function

In this file we prove that sinh is bijective and hence has an
inverse, arsinh.

## Main Results

- `sinh_injective`: The proof that `sinh` is injective
- `sinh_surjective`: The proof that `sinh` is surjective
- `sinh_bijective`: The proof `sinh` is bijective
- `arsinh`: The inverse function of `sinh`

## Tags

arsinh, arcsinh, argsinh, asinh, sinh injective, sinh bijective, sinh surjective
-/


noncomputable section

namespace Real

/-- `arsinh` is defined using a logarithm, `arsinh x = log (x + sqrt(1 + x^2))`. -/
@[pp_nodot]
def arsinh (x : ℝ) :=
  log (x + sqrt (1 + x ^ 2))

/-- `sinh` is injective, `∀ a b, sinh a = sinh b → a = b`. -/
theorem sinh_injective : Function.Injective sinh :=
  sinh_strict_mono.Injective

private theorem aux_lemma (x : ℝ) : 1 / (x + sqrt (1 + x ^ 2)) = -x + sqrt (1 + x ^ 2) := by
  refine' (eq_one_div_of_mul_eq_one_right _).symm
  have : 0 ≤ 1 + x ^ 2 := add_nonneg zero_le_one (sq_nonneg x)
  rw [add_commₓ, ← sub_eq_neg_add, ← mul_self_sub_mul_self, mul_self_sqrt this, sq, add_sub_cancel]

private theorem b_lt_sqrt_b_one_add_sq (b : ℝ) : b < sqrt (1 + b ^ 2) :=
  calc
    b ≤ sqrt (b ^ 2) := le_sqrt_of_sq_le le_rfl
    _ < sqrt (1 + b ^ 2) := sqrt_lt_sqrt (sq_nonneg _) (lt_one_add _)
    

private theorem add_sqrt_one_add_sq_pos (b : ℝ) : 0 < b + sqrt (1 + b ^ 2) := by
  rw [← neg_negₓ b, ← sub_eq_neg_add, sub_pos, sq, neg_mul_neg, ← sq]
  exact b_lt_sqrt_b_one_add_sq (-b)

/-- `arsinh` is the right inverse of `sinh`. -/
theorem sinh_arsinh (x : ℝ) : sinh (arsinh x) = x := by
  rw [sinh_eq, arsinh, ← log_inv, exp_log (add_sqrt_one_add_sq_pos x), exp_log (inv_pos.2 (add_sqrt_one_add_sq_pos x)),
    inv_eq_one_div, aux_lemma x, sub_eq_add_neg, neg_add, neg_negₓ, ← sub_eq_add_neg, add_add_sub_cancel,
    add_self_div_two]

/-- `sinh` is surjective, `∀ b, ∃ a, sinh a = b`. In this case, we use `a = arsinh b`. -/
theorem sinh_surjective : Function.Surjective sinh :=
  Function.LeftInverse.surjectiveₓ sinh_arsinh

/-- `sinh` is bijective, both injective and surjective. -/
theorem sinh_bijective : Function.Bijective sinh :=
  ⟨sinh_injective, sinh_surjective⟩

/-- A rearrangement and `sqrt` of `real.cosh_sq_sub_sinh_sq`. -/
theorem sqrt_one_add_sinh_sq (x : ℝ) : sqrt (1 + sinh x ^ 2) = cosh x := by
  have H := Real.cosh_sq_sub_sinh_sq x
  have G : cosh x ^ 2 - sinh x ^ 2 + sinh x ^ 2 = 1 + sinh x ^ 2 := by
    rw [H]
  rw [sub_add_cancel] at G
  rw [← G, sqrt_sq]
  exact le_of_ltₓ (cosh_pos x)

/-- `arsinh` is the left inverse of `sinh`. -/
theorem arsinh_sinh (x : ℝ) : arsinh (sinh x) = x :=
  Function.right_inverse_of_injective_of_left_inverse sinh_injective sinh_arsinh x

end Real

