import Mathbin.Analysis.SpecialFunctions.Trigonometric.Deriv 
import Mathbin.Analysis.SpecialFunctions.Log

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


noncomputable theory

namespace Real

/-- `arsinh` is defined using a logarithm, `arsinh x = log (x + sqrt(1 + x^2))`. -/
@[pp_nodot]
def arsinh (x : ℝ) :=
  log (x+sqrt (1+x^2))

/-- `sinh` is injective, `∀ a b, sinh a = sinh b → a = b`. -/
theorem sinh_injective : Function.Injective sinh :=
  sinh_strict_mono.Injective

-- error in Analysis.SpecialFunctions.Arsinh: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem aux_lemma
(x : exprℝ()) : «expr = »(«expr / »(1, «expr + »(x, sqrt «expr + »(1, «expr ^ »(x, 2)))), «expr + »(«expr- »(x), sqrt «expr + »(1, «expr ^ »(x, 2)))) :=
begin
  refine [expr (eq_one_div_of_mul_eq_one _).symm],
  have [] [":", expr «expr ≤ »(0, «expr + »(1, «expr ^ »(x, 2)))] [":=", expr add_nonneg zero_le_one (sq_nonneg x)],
  rw ["[", expr add_comm, ",", "<-", expr sub_eq_neg_add, ",", "<-", expr mul_self_sub_mul_self, ",", expr mul_self_sqrt this, ",", expr sq, ",", expr add_sub_cancel, "]"] []
end

private theorem b_lt_sqrt_b_one_add_sq (b : ℝ) : b < sqrt (1+b^2) :=
  calc b ≤ sqrt (b^2) := le_sqrt_of_sq_le le_rfl 
    _ < sqrt (1+b^2) := sqrt_lt_sqrt (sq_nonneg _) (lt_one_add _)
    

private theorem add_sqrt_one_add_sq_pos (b : ℝ) : 0 < b+sqrt (1+b^2) :=
  by 
    rw [←neg_negₓ b, ←sub_eq_neg_add, sub_pos, sq, neg_mul_neg, ←sq]
    exact b_lt_sqrt_b_one_add_sq (-b)

/-- `arsinh` is the right inverse of `sinh`. -/
theorem sinh_arsinh (x : ℝ) : sinh (arsinh x) = x :=
  by 
    rw [sinh_eq, arsinh, ←log_inv, exp_log (add_sqrt_one_add_sq_pos x), exp_log (inv_pos.2 (add_sqrt_one_add_sq_pos x)),
      inv_eq_one_div, aux_lemma x, sub_eq_add_neg, neg_add, neg_negₓ, ←sub_eq_add_neg, add_add_sub_cancel,
      add_self_div_two]

/-- `sinh` is surjective, `∀ b, ∃ a, sinh a = b`. In this case, we use `a = arsinh b`. -/
theorem sinh_surjective : Function.Surjective sinh :=
  Function.LeftInverse.surjective sinh_arsinh

/-- `sinh` is bijective, both injective and surjective. -/
theorem sinh_bijective : Function.Bijective sinh :=
  ⟨sinh_injective, sinh_surjective⟩

-- error in Analysis.SpecialFunctions.Arsinh: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A rearrangement and `sqrt` of `real.cosh_sq_sub_sinh_sq`. -/
theorem sqrt_one_add_sinh_sq (x : exprℝ()) : «expr = »(sqrt «expr + »(1, «expr ^ »(sinh x, 2)), cosh x) :=
begin
  have [ident H] [] [":=", expr real.cosh_sq_sub_sinh_sq x],
  have [ident G] [":", expr «expr = »(«expr + »(«expr - »(«expr ^ »(cosh x, 2), «expr ^ »(sinh x, 2)), «expr ^ »(sinh x, 2)), «expr + »(1, «expr ^ »(sinh x, 2)))] [":=", expr by rw [expr H] []],
  rw [expr sub_add_cancel] ["at", ident G],
  rw ["[", "<-", expr G, ",", expr sqrt_sq, "]"] [],
  exact [expr le_of_lt (cosh_pos x)]
end

/-- `arsinh` is the left inverse of `sinh`. -/
theorem arsinh_sinh (x : ℝ) : arsinh (sinh x) = x :=
  Function.right_inverse_of_injective_of_left_inverse sinh_injective sinh_arsinh x

end Real

