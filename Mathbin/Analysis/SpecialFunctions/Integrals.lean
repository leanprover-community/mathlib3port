import Mathbin.MeasureTheory.Integral.IntervalIntegral 
import Mathbin.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Integration of specific interval integrals

This file contains proofs of the integrals of various specific functions. This includes:
* Integrals of simple functions, such as `id`, `pow`, `inv`, `exp`, `log`
* Integrals of some trigonometric functions, such as `sin`, `cos`, `1 / (1 + x^2)`
* The integral of `cos x ^ 2 - sin x ^ 2`
* Reduction formulae for the integrals of `sin x ^ n` and `cos x ^ n` for `n ≥ 2`
* The computation of `∫ x in 0..π, sin x ^ n` as a product for even and odd `n` (used in proving the
  Wallis product for pi)
* Integrals of the form `sin x ^ m * cos x ^ n`

With these lemmas, many simple integrals can be computed by `simp` or `norm_num`.
See `test/integration.lean` for specific examples.

This file also contains some facts about the interval integrability of specific functions.

This file is still being developed.

## Tags

integrate, integration, integrable, integrability
-/


open Real Nat Set Finset

open_locale Real BigOperators Interval

variable {a b : ℝ} (n : ℕ)

namespace intervalIntegral

open MeasureTheory

variable {f : ℝ → ℝ} {μ ν : Measureₓ ℝ} [is_locally_finite_measure μ] (c d : ℝ)

/-! ### Interval integrability -/


@[simp]
theorem interval_integrable_pow : IntervalIntegrable (fun x => x^n) μ a b :=
  (continuous_pow n).IntervalIntegrable a b

@[simp]
theorem interval_integrable_id : IntervalIntegrable (fun x => x) μ a b :=
  continuous_id.IntervalIntegrable a b

@[simp]
theorem interval_integrable_const : IntervalIntegrable (fun x => c) μ a b :=
  continuous_const.IntervalIntegrable a b

@[simp]
theorem interval_integrable.const_mul (h : IntervalIntegrable f ν a b) : IntervalIntegrable (fun x => c*f x) ν a b :=
  by 
    convert h.smul c

@[simp]
theorem interval_integrable.mul_const (h : IntervalIntegrable f ν a b) : IntervalIntegrable (fun x => f x*c) ν a b :=
  by 
    simp only [mul_commₓ, interval_integrable.const_mul c h]

@[simp]
theorem interval_integrable.div (h : IntervalIntegrable f ν a b) : IntervalIntegrable (fun x => f x / c) ν a b :=
  interval_integrable.mul_const (c⁻¹) h

-- error in Analysis.SpecialFunctions.Integrals: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
theorem interval_integrable_one_div
(h : ∀ x : exprℝ(), «expr ∈ »(x, «expr[ , ]»(a, b)) → «expr ≠ »(f x, 0))
(hf : continuous_on f «expr[ , ]»(a, b)) : interval_integrable (λ x, «expr / »(1, f x)) μ a b :=
(continuous_on_const.div hf h).interval_integrable

-- error in Analysis.SpecialFunctions.Integrals: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
@[simp]
theorem interval_integrable_inv
(h : ∀ x : exprℝ(), «expr ∈ »(x, «expr[ , ]»(a, b)) → «expr ≠ »(f x, 0))
(hf : continuous_on f «expr[ , ]»(a, b)) : interval_integrable (λ x, «expr ⁻¹»(f x)) μ a b :=
by simpa [] [] ["only"] ["[", expr one_div, "]"] [] ["using", expr interval_integrable_one_div h hf]

@[simp]
theorem interval_integrable_exp : IntervalIntegrable exp μ a b :=
  continuous_exp.IntervalIntegrable a b

-- error in Analysis.SpecialFunctions.Integrals: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
@[simp]
theorem interval_integrable.log
(hf : continuous_on f «expr[ , ]»(a, b))
(h : ∀ x : exprℝ(), «expr ∈ »(x, «expr[ , ]»(a, b)) → «expr ≠ »(f x, 0)) : interval_integrable (λ x, log (f x)) μ a b :=
(continuous_on.log hf h).interval_integrable

-- error in Analysis.SpecialFunctions.Integrals: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
@[simp]
theorem interval_integrable_log (h : «expr ∉ »((0 : exprℝ()), «expr[ , ]»(a, b))) : interval_integrable log μ a b :=
«expr $ »(interval_integrable.log continuous_on_id, λ x hx, ne_of_mem_of_not_mem hx h)

@[simp]
theorem interval_integrable_sin : IntervalIntegrable sin μ a b :=
  continuous_sin.IntervalIntegrable a b

@[simp]
theorem interval_integrable_cos : IntervalIntegrable cos μ a b :=
  continuous_cos.IntervalIntegrable a b

theorem interval_integrable_one_div_one_add_sq : IntervalIntegrable (fun x : ℝ => 1 / 1+x^2) μ a b :=
  by 
    refine' (continuous_const.div _ fun x => _).IntervalIntegrable a b
    ·
      continuity
    ·
      nlinarith

@[simp]
theorem interval_integrable_inv_one_add_sq : IntervalIntegrable (fun x : ℝ => (1+x^2)⁻¹) μ a b :=
  by 
    simpa only [one_div] using interval_integrable_one_div_one_add_sq

/-! ### Integrals of the form `c * ∫ x in a..b, f (c * x + d)` -/


@[simp]
theorem mul_integral_comp_mul_right : (c*∫x in a..b, f (x*c)) = ∫x in a*c..b*c, f x :=
  smul_integral_comp_mul_right f c

@[simp]
theorem mul_integral_comp_mul_left : (c*∫x in a..b, f (c*x)) = ∫x in c*a..c*b, f x :=
  smul_integral_comp_mul_left f c

@[simp]
theorem inv_mul_integral_comp_div : (c⁻¹*∫x in a..b, f (x / c)) = ∫x in a / c..b / c, f x :=
  inv_smul_integral_comp_div f c

@[simp]
theorem mul_integral_comp_mul_add : (c*∫x in a..b, f ((c*x)+d)) = ∫x in (c*a)+d..(c*b)+d, f x :=
  smul_integral_comp_mul_add f c d

@[simp]
theorem mul_integral_comp_add_mul : (c*∫x in a..b, f (d+c*x)) = ∫x in d+c*a..d+c*b, f x :=
  smul_integral_comp_add_mul f c d

@[simp]
theorem inv_mul_integral_comp_div_add : (c⁻¹*∫x in a..b, f ((x / c)+d)) = ∫x in (a / c)+d..(b / c)+d, f x :=
  inv_smul_integral_comp_div_add f c d

@[simp]
theorem inv_mul_integral_comp_add_div : (c⁻¹*∫x in a..b, f (d+x / c)) = ∫x in d+a / c..d+b / c, f x :=
  inv_smul_integral_comp_add_div f c d

@[simp]
theorem mul_integral_comp_mul_sub : (c*∫x in a..b, f ((c*x) - d)) = ∫x in (c*a) - d..(c*b) - d, f x :=
  smul_integral_comp_mul_sub f c d

@[simp]
theorem mul_integral_comp_sub_mul : (c*∫x in a..b, f (d - c*x)) = ∫x in d - c*b..d - c*a, f x :=
  smul_integral_comp_sub_mul f c d

@[simp]
theorem inv_mul_integral_comp_div_sub : (c⁻¹*∫x in a..b, f (x / c - d)) = ∫x in a / c - d..b / c - d, f x :=
  inv_smul_integral_comp_div_sub f c d

@[simp]
theorem inv_mul_integral_comp_sub_div : (c⁻¹*∫x in a..b, f (d - x / c)) = ∫x in d - b / c..d - a / c, f x :=
  inv_smul_integral_comp_sub_div f c d

end intervalIntegral

open intervalIntegral

/-! ### Integrals of simple functions -/


-- error in Analysis.SpecialFunctions.Integrals: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem integral_pow : «expr = »(«expr∫ in .. , »((x), a, b, «expr ^ »(x, n)), «expr / »(«expr - »(«expr ^ »(b, «expr + »(n, 1)), «expr ^ »(a, «expr + »(n, 1))), «expr + »(n, 1))) :=
begin
  have [ident hderiv] [":", expr «expr = »(deriv (λ
     x : exprℝ(), «expr / »(«expr ^ »(x, «expr + »(n, 1)), «expr + »(n, 1))), λ x, «expr ^ »(x, n))] [],
  { ext [] [] [],
    have [ident hne] [":", expr «expr ≠ »((«expr + »(n, 1) : exprℝ()), 0)] [":=", expr by exact_mod_cast [expr succ_ne_zero n]],
    simp [] [] [] ["[", expr mul_div_assoc, ",", expr mul_div_cancel' _ hne, "]"] [] [] },
  rw [expr integral_deriv_eq_sub' _ hderiv] []; norm_num ["[", expr div_sub_div_same, ",", expr continuous_on_pow, "]"] []
end

/-- Integral of `|x - a| ^ n` over `Ι a b`. This integral appears in the proof of the
Picard-Lindelöf/Cauchy-Lipschitz theorem. -/
theorem integral_pow_abs_sub_interval_oc : (∫x in Ι a b, |x - a|^n) = (|b - a|^n+1) / n+1 :=
  by 
    cases' le_or_ltₓ a b with hab hab
    ·
      calc (∫x in Ι a b, |x - a|^n) = ∫x in a..b, |x - a|^n :=
        by 
          rw [interval_oc_of_le hab, ←integral_of_le hab]_ = ∫x in 0 ..b - a, x^n :=
        by 
          simp only [integral_comp_sub_right fun x => |x|^n, sub_self]
          refine' integral_congr fun x hx => congr_arg2 Pow.pow (abs_of_nonneg$ _) rfl 
          rw [interval_of_le (sub_nonneg.2 hab)] at hx 
          exact hx.1_ = (|b - a|^n+1) / n+1 :=
        by 
          simp [abs_of_nonneg (sub_nonneg.2 hab)]
    ·
      calc (∫x in Ι a b, |x - a|^n) = ∫x in b..a, |x - a|^n :=
        by 
          rw [interval_oc_of_lt hab, ←integral_of_le hab.le]_ = ∫x in b - a..0, -x^n :=
        by 
          simp only [integral_comp_sub_right fun x => |x|^n, sub_self]
          refine' integral_congr fun x hx => congr_arg2 Pow.pow (abs_of_nonpos$ _) rfl 
          rw [interval_of_le (sub_nonpos.2 hab.le)] at hx 
          exact hx.2_ = (|b - a|^n+1) / n+1 :=
        by 
          simp [integral_comp_neg fun x => x^n, abs_of_neg (sub_neg.2 hab)]

@[simp]
theorem integral_id : (∫x in a..b, x) = ((b^2) - (a^2)) / 2 :=
  by 
    simpa using integral_pow 1

@[simp]
theorem integral_one : (∫x in a..b, (1 : ℝ)) = b - a :=
  by 
    simp only [mul_oneₓ, smul_eq_mul, integral_const]

-- error in Analysis.SpecialFunctions.Integrals: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
@[simp]
theorem integral_inv
(h : «expr ∉ »((0 : exprℝ()), «expr[ , ]»(a, b))) : «expr = »(«expr∫ in .. , »((x), a, b, «expr ⁻¹»(x)), log «expr / »(b, a)) :=
begin
  have [ident h'] [] [":=", expr λ x hx, ne_of_mem_of_not_mem hx h],
  rw ["[", expr integral_deriv_eq_sub' _ deriv_log' (λ
    x
    hx, differentiable_at_log (h' x hx)) «expr $ »(continuous_on_inv₀.mono, subset_compl_singleton_iff.mpr h), ",", expr log_div (h' b right_mem_interval) (h' a left_mem_interval), "]"] []
end

@[simp]
theorem integral_inv_of_pos (ha : 0 < a) (hb : 0 < b) : (∫x in a..b, x⁻¹) = log (b / a) :=
  integral_inv$ not_mem_interval_of_lt ha hb

@[simp]
theorem integral_inv_of_neg (ha : a < 0) (hb : b < 0) : (∫x in a..b, x⁻¹) = log (b / a) :=
  integral_inv$ not_mem_interval_of_gt ha hb

-- error in Analysis.SpecialFunctions.Integrals: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
theorem integral_one_div
(h : «expr ∉ »((0 : exprℝ()), «expr[ , ]»(a, b))) : «expr = »(«expr∫ in .. , »((x : exprℝ()), a, b, «expr / »(1, x)), log «expr / »(b, a)) :=
by simp [] [] ["only"] ["[", expr one_div, ",", expr integral_inv h, "]"] [] []

theorem integral_one_div_of_pos (ha : 0 < a) (hb : 0 < b) : (∫x : ℝ in a..b, 1 / x) = log (b / a) :=
  by 
    simp only [one_div, integral_inv_of_pos ha hb]

theorem integral_one_div_of_neg (ha : a < 0) (hb : b < 0) : (∫x : ℝ in a..b, 1 / x) = log (b / a) :=
  by 
    simp only [one_div, integral_inv_of_neg ha hb]

@[simp]
theorem integral_exp : (∫x in a..b, exp x) = exp b - exp a :=
  by 
    rw [integral_deriv_eq_sub'] <;> normNum [continuous_on_exp]

-- error in Analysis.SpecialFunctions.Integrals: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
@[simp]
theorem integral_log
(h : «expr ∉ »((0 : exprℝ()), «expr[ , ]»(a, b))) : «expr = »(«expr∫ in .. , »((x), a, b, log x), «expr + »(«expr - »(«expr - »(«expr * »(b, log b), «expr * »(a, log a)), b), a)) :=
begin
  obtain ["⟨", ident h', ",", ident heq, "⟩", ":=", "⟨", expr λ
   x hx, ne_of_mem_of_not_mem hx h, ",", expr λ x hx, mul_inv_cancel (h' x hx), "⟩"],
  convert [] [expr integral_mul_deriv_eq_deriv_mul (λ
    x
    hx, has_deriv_at_log (h' x hx)) (λ
    x
    hx, has_deriv_at_id x) «expr $ »(continuous_on_inv₀.mono, subset_compl_singleton_iff.mpr h).interval_integrable continuous_on_const.interval_integrable] ["using", 1]; simp [] [] [] ["[", expr integral_congr heq, ",", expr mul_comm, ",", "<-", expr sub_add, "]"] [] []
end

@[simp]
theorem integral_log_of_pos (ha : 0 < a) (hb : 0 < b) : (∫x in a..b, log x) = (((b*log b) - a*log a) - b)+a :=
  integral_log$ not_mem_interval_of_lt ha hb

@[simp]
theorem integral_log_of_neg (ha : a < 0) (hb : b < 0) : (∫x in a..b, log x) = (((b*log b) - a*log a) - b)+a :=
  integral_log$ not_mem_interval_of_gt ha hb

@[simp]
theorem integral_sin : (∫x in a..b, sin x) = cos a - cos b :=
  by 
    rw [integral_deriv_eq_sub' fun x => -cos x] <;> normNum [continuous_on_sin]

@[simp]
theorem integral_cos : (∫x in a..b, cos x) = sin b - sin a :=
  by 
    rw [integral_deriv_eq_sub'] <;> normNum [continuous_on_cos]

theorem integral_cos_sq_sub_sin_sq : (∫x in a..b, (cos x^2) - (sin x^2)) = (sin b*cos b) - sin a*cos a :=
  by 
    simpa only [sq, sub_eq_add_neg, neg_mul_eq_mul_neg] using
      integral_deriv_mul_eq_sub (fun x hx => has_deriv_at_sin x) (fun x hx => has_deriv_at_cos x)
        continuous_on_cos.interval_integrable continuous_on_sin.neg.interval_integrable

@[simp]
theorem integral_inv_one_add_sq : (∫x : ℝ in a..b, (1+x^2)⁻¹) = arctan b - arctan a :=
  by 
    simp only [←one_div]
    refine' integral_deriv_eq_sub' _ _ _ (continuous_const.div _ fun x => _).ContinuousOn
    ·
      normNum
    ·
      normNum
    ·
      continuity
    ·
      nlinarith

theorem integral_one_div_one_add_sq : (∫x : ℝ in a..b, 1 / 1+x^2) = arctan b - arctan a :=
  by 
    simp only [one_div, integral_inv_one_add_sq]

/-! ### Integral of `sin x ^ n` -/


-- error in Analysis.SpecialFunctions.Integrals: ././Mathport/Syntax/Translate/Basic.lean:341:40: in have: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
theorem integral_sin_pow_aux : «expr = »(«expr∫ in .. , »((x), a, b, «expr ^ »(sin x, «expr + »(n, 2))), «expr - »(«expr + »(«expr - »(«expr * »(«expr ^ »(sin a, «expr + »(n, 1)), cos a), «expr * »(«expr ^ »(sin b, «expr + »(n, 1)), cos b)), «expr * »(«expr + »(n, 1), «expr∫ in .. , »((x), a, b, «expr ^ »(sin x, n)))), «expr * »(«expr + »(n, 1), «expr∫ in .. , »((x), a, b, «expr ^ »(sin x, «expr + »(n, 2)))))) :=
begin
  let [ident C] [] [":=", expr «expr - »(«expr * »(«expr ^ »(sin a, «expr + »(n, 1)), cos a), «expr * »(«expr ^ »(sin b, «expr + »(n, 1)), cos b))],
  have [ident h] [":", expr ∀
   α
   β
   γ : exprℝ(), «expr = »(«expr * »(α, «expr * »(«expr * »(β, α), γ)), «expr * »(β, «expr * »(«expr * »(α, α), γ)))] [":=", expr λ
   α β γ, by ring []],
  have [ident hu] [":", expr ∀
   x «expr ∈ » _, has_deriv_at (λ
    y, «expr ^ »(sin y, «expr + »(n, 1))) «expr * »(«expr * »(«expr + »(n, 1), cos x), «expr ^ »(sin x, n)) x] [":=", expr λ
   x hx, by simpa [] [] ["only"] ["[", expr mul_right_comm, "]"] [] ["using", expr (has_deriv_at_sin x).pow]],
  have [ident hv] [":", expr ∀
   x «expr ∈ » «expr[ , ]»(a, b), has_deriv_at «expr- »(cos) (sin x) x] [":=", expr λ
   x hx, by simpa [] [] ["only"] ["[", expr neg_neg, "]"] [] ["using", expr (has_deriv_at_cos x).neg]],
  have [ident H] [] [":=", expr integral_mul_deriv_eq_deriv_mul hu hv _ _],
  calc
    «expr = »(«expr∫ in .. , »((x), a, b, «expr ^ »(sin x, «expr + »(n, 2))), «expr∫ in .. , »((x), a, b, «expr * »(«expr ^ »(sin x, «expr + »(n, 1)), sin x))) : by simp [] [] ["only"] ["[", expr pow_succ', "]"] [] []
    «expr = »(..., «expr + »(C, «expr * »(«expr + »(n, 1), «expr∫ in .. , »((x), a, b, «expr * »(«expr ^ »(cos x, 2), «expr ^ »(sin x, n)))))) : by simp [] [] [] ["[", expr H, ",", expr h, ",", expr sq, "]"] [] []
    «expr = »(..., «expr + »(C, «expr * »(«expr + »(n, 1), «expr∫ in .. , »((x), a, b, «expr - »(«expr ^ »(sin x, n), «expr ^ »(sin x, «expr + »(n, 2))))))) : by simp [] [] [] ["[", expr cos_sq', ",", expr sub_mul, ",", "<-", expr pow_add, ",", expr add_comm, "]"] [] []
    «expr = »(..., «expr - »(«expr + »(C, «expr * »(«expr + »(n, 1), «expr∫ in .. , »((x), a, b, «expr ^ »(sin x, n)))), «expr * »(«expr + »(n, 1), «expr∫ in .. , »((x), a, b, «expr ^ »(sin x, «expr + »(n, 2)))))) : by rw ["[", expr integral_sub, ",", expr mul_sub, ",", expr add_sub_assoc, "]"] []; apply [expr continuous.interval_integrable]; continuity [] [],
  all_goals { apply [expr continuous.interval_integrable],
    continuity [] [] }
end

-- error in Analysis.SpecialFunctions.Integrals: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The reduction formula for the integral of `sin x ^ n` for any natural `n ≥ 2`. -/
theorem integral_sin_pow : «expr = »(«expr∫ in .. , »((x), a, b, «expr ^ »(sin x, «expr + »(n, 2))), «expr + »(«expr / »(«expr - »(«expr * »(«expr ^ »(sin a, «expr + »(n, 1)), cos a), «expr * »(«expr ^ »(sin b, «expr + »(n, 1)), cos b)), «expr + »(n, 2)), «expr * »(«expr / »(«expr + »(n, 1), «expr + »(n, 2)), «expr∫ in .. , »((x), a, b, «expr ^ »(sin x, n))))) :=
begin
  have [] [":", expr «expr ≠ »(«expr + »((n : exprℝ()), 2), 0)] [":=", expr by exact_mod_cast [expr succ_ne_zero n.succ]],
  field_simp [] [] [] [],
  convert [] [expr eq_sub_iff_add_eq.mp (integral_sin_pow_aux n)] [],
  ring []
end

@[simp]
theorem integral_sin_sq : (∫x in a..b, sin x^2) = ((((sin a*cos a) - sin b*cos b)+b) - a) / 2 :=
  by 
    fieldSimp [integral_sin_pow, add_sub_assoc]

theorem integral_sin_pow_odd : (∫x in 0 ..π, sin x^(2*n)+1) = 2*∏i in range n, ((2*i)+2) / (2*i)+3 :=
  by 
    induction' n with k ih
    ·
      normNum 
    rw [prod_range_succ_comm, mul_left_commₓ, ←ih, mul_succ, integral_sin_pow]
    normCast 
    simp' [-cast_add] with field_simps

theorem integral_sin_pow_even : (∫x in 0 ..π, sin x^2*n) = π*∏i in range n, ((2*i)+1) / (2*i)+2 :=
  by 
    induction' n with k ih
    ·
      simp 
    rw [prod_range_succ_comm, mul_left_commₓ, ←ih, mul_succ, integral_sin_pow]
    normCast 
    simp' [-cast_add] with field_simps

theorem integral_sin_pow_pos : 0 < ∫x in 0 ..π, sin x^n :=
  by 
    rcases even_or_odd' n with ⟨k, rfl | rfl⟩ <;>
      simp only [integral_sin_pow_even, integral_sin_pow_odd] <;>
        refine'
            mul_pos
              (by 
                normNum [pi_pos])
              (prod_pos fun n hn => div_pos _ _) <;>
          normCast <;> linarith

theorem integral_sin_pow_succ_le : (∫x in 0 ..π, sin x^n+1) ≤ ∫x in 0 ..π, sin x^n :=
  let H := fun x h => pow_le_pow_of_le_one (sin_nonneg_of_mem_Icc h) (sin_le_one x) (n.le_add_right 1)
  by 
    refine' integral_mono_on pi_pos.le _ _ H <;> exact (continuous_sin.pow _).IntervalIntegrable 0 π

theorem integral_sin_pow_antitone : Antitone fun n : ℕ => ∫x in 0 ..π, sin x^n :=
  antitone_nat_of_succ_le integral_sin_pow_succ_le

/-! ### Integral of `cos x ^ n` -/


-- error in Analysis.SpecialFunctions.Integrals: ././Mathport/Syntax/Translate/Basic.lean:341:40: in have: ././Mathport/Syntax/Translate/Basic.lean:546:47: unsupported (impossible)
theorem integral_cos_pow_aux : «expr = »(«expr∫ in .. , »((x), a, b, «expr ^ »(cos x, «expr + »(n, 2))), «expr - »(«expr + »(«expr - »(«expr * »(«expr ^ »(cos b, «expr + »(n, 1)), sin b), «expr * »(«expr ^ »(cos a, «expr + »(n, 1)), sin a)), «expr * »(«expr + »(n, 1), «expr∫ in .. , »((x), a, b, «expr ^ »(cos x, n)))), «expr * »(«expr + »(n, 1), «expr∫ in .. , »((x), a, b, «expr ^ »(cos x, «expr + »(n, 2)))))) :=
begin
  let [ident C] [] [":=", expr «expr - »(«expr * »(«expr ^ »(cos b, «expr + »(n, 1)), sin b), «expr * »(«expr ^ »(cos a, «expr + »(n, 1)), sin a))],
  have [ident h] [":", expr ∀
   α
   β
   γ : exprℝ(), «expr = »(«expr * »(α, «expr * »(«expr * »(β, α), γ)), «expr * »(β, «expr * »(«expr * »(α, α), γ)))] [":=", expr λ
   α β γ, by ring []],
  have [ident hu] [":", expr ∀
   x «expr ∈ » _, has_deriv_at (λ
    y, «expr ^ »(cos y, «expr + »(n, 1))) «expr * »(«expr * »(«expr- »(«expr + »(n, 1)), sin x), «expr ^ »(cos x, n)) x] [":=", expr λ
   x
   hx, by simpa [] [] ["only"] ["[", expr mul_right_comm, ",", expr neg_mul_eq_neg_mul_symm, ",", expr mul_neg_eq_neg_mul_symm, "]"] [] ["using", expr (has_deriv_at_cos x).pow]],
  have [ident hv] [":", expr ∀
   x «expr ∈ » «expr[ , ]»(a, b), has_deriv_at sin (cos x) x] [":=", expr λ x hx, has_deriv_at_sin x],
  have [ident H] [] [":=", expr integral_mul_deriv_eq_deriv_mul hu hv _ _],
  calc
    «expr = »(«expr∫ in .. , »((x), a, b, «expr ^ »(cos x, «expr + »(n, 2))), «expr∫ in .. , »((x), a, b, «expr * »(«expr ^ »(cos x, «expr + »(n, 1)), cos x))) : by simp [] [] ["only"] ["[", expr pow_succ', "]"] [] []
    «expr = »(..., «expr + »(C, «expr * »(«expr + »(n, 1), «expr∫ in .. , »((x), a, b, «expr * »(«expr ^ »(sin x, 2), «expr ^ »(cos x, n)))))) : by simp [] [] [] ["[", expr H, ",", expr h, ",", expr sq, ",", "-", ident neg_add_rev, "]"] [] []
    «expr = »(..., «expr + »(C, «expr * »(«expr + »(n, 1), «expr∫ in .. , »((x), a, b, «expr - »(«expr ^ »(cos x, n), «expr ^ »(cos x, «expr + »(n, 2))))))) : by simp [] [] [] ["[", expr sin_sq, ",", expr sub_mul, ",", "<-", expr pow_add, ",", expr add_comm, "]"] [] []
    «expr = »(..., «expr - »(«expr + »(C, «expr * »(«expr + »(n, 1), «expr∫ in .. , »((x), a, b, «expr ^ »(cos x, n)))), «expr * »(«expr + »(n, 1), «expr∫ in .. , »((x), a, b, «expr ^ »(cos x, «expr + »(n, 2)))))) : by rw ["[", expr integral_sub, ",", expr mul_sub, ",", expr add_sub_assoc, "]"] []; apply [expr continuous.interval_integrable]; continuity [] [],
  all_goals { apply [expr continuous.interval_integrable],
    continuity [] [] }
end

-- error in Analysis.SpecialFunctions.Integrals: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The reduction formula for the integral of `cos x ^ n` for any natural `n ≥ 2`. -/
theorem integral_cos_pow : «expr = »(«expr∫ in .. , »((x), a, b, «expr ^ »(cos x, «expr + »(n, 2))), «expr + »(«expr / »(«expr - »(«expr * »(«expr ^ »(cos b, «expr + »(n, 1)), sin b), «expr * »(«expr ^ »(cos a, «expr + »(n, 1)), sin a)), «expr + »(n, 2)), «expr * »(«expr / »(«expr + »(n, 1), «expr + »(n, 2)), «expr∫ in .. , »((x), a, b, «expr ^ »(cos x, n))))) :=
begin
  have [] [":", expr «expr ≠ »(«expr + »((n : exprℝ()), 2), 0)] [":=", expr by exact_mod_cast [expr succ_ne_zero n.succ]],
  field_simp [] [] [] [],
  convert [] [expr eq_sub_iff_add_eq.mp (integral_cos_pow_aux n)] [],
  ring []
end

@[simp]
theorem integral_cos_sq : (∫x in a..b, cos x^2) = ((((cos b*sin b) - cos a*sin a)+b) - a) / 2 :=
  by 
    fieldSimp [integral_cos_pow, add_sub_assoc]

/-! ### Integral of `sin x ^ m * cos x ^ n` -/


/-- Simplification of the integral of `sin x ^ m * cos x ^ n`, case `n` is odd. -/
theorem integral_sin_pow_mul_cos_pow_odd (m n : ℕ) :
  (∫x in a..b, (sin x^m)*cos x^(2*n)+1) = ∫u in sin a..sin b, (u^m)*1 - (u^2)^n :=
  have hc : Continuous fun u : ℝ => (u^m)*1 - (u^2)^n :=
    by 
      continuity 
  calc (∫x in a..b, (sin x^m)*cos x^(2*n)+1) = ∫x in a..b, ((sin x^m)*1 - (sin x^2)^n)*cos x :=
    by 
      simp only [pow_succ'ₓ, ←mul_assocₓ, pow_mulₓ, cos_sq']
    _ = ∫u in sin a..sin b, (u^m)*1 - (u^2)^n :=
    integral_comp_mul_deriv (fun x hx => has_deriv_at_sin x) continuous_on_cos hc
    

/-- The integral of `sin x * cos x`, given in terms of sin².
  See `integral_sin_mul_cos₂` below for the integral given in terms of cos². -/
@[simp]
theorem integral_sin_mul_cos₁ : (∫x in a..b, sin x*cos x) = ((sin b^2) - (sin a^2)) / 2 :=
  by 
    simpa using integral_sin_pow_mul_cos_pow_odd 1 0

@[simp]
theorem integral_sin_sq_mul_cos : (∫x in a..b, (sin x^2)*cos x) = ((sin b^3) - (sin a^3)) / 3 :=
  by 
    simpa using integral_sin_pow_mul_cos_pow_odd 2 0

@[simp]
theorem integral_cos_pow_three : (∫x in a..b, cos x^3) = sin b - sin a - ((sin b^3) - (sin a^3)) / 3 :=
  by 
    simpa using integral_sin_pow_mul_cos_pow_odd 0 1

/-- Simplification of the integral of `sin x ^ m * cos x ^ n`, case `m` is odd. -/
theorem integral_sin_pow_odd_mul_cos_pow (m n : ℕ) :
  (∫x in a..b, (sin x^(2*m)+1)*cos x^n) = ∫u in cos b..cos a, (u^n)*1 - (u^2)^m :=
  have hc : Continuous fun u : ℝ => (u^n)*1 - (u^2)^m :=
    by 
      continuity 
  calc (∫x in a..b, (sin x^(2*m)+1)*cos x^n) = -∫x in b..a, (sin x^(2*m)+1)*cos x^n :=
    by 
      rw [integral_symm]
    _ = ∫x in b..a, ((1 - (cos x^2)^m)*-sin x)*cos x^n :=
    by 
      simp [pow_succ'ₓ, pow_mulₓ, sin_sq]
    _ = ∫x in b..a, ((cos x^n)*1 - (cos x^2)^m)*-sin x :=
    by 
      congr 
      ext 
      ring 
    _ = ∫u in cos b..cos a, (u^n)*1 - (u^2)^m :=
    integral_comp_mul_deriv (fun x hx => has_deriv_at_cos x) continuous_on_sin.neg hc
    

/-- The integral of `sin x * cos x`, given in terms of cos².
See `integral_sin_mul_cos₁` above for the integral given in terms of sin². -/
theorem integral_sin_mul_cos₂ : (∫x in a..b, sin x*cos x) = ((cos a^2) - (cos b^2)) / 2 :=
  by 
    simpa using integral_sin_pow_odd_mul_cos_pow 0 1

@[simp]
theorem integral_sin_mul_cos_sq : (∫x in a..b, sin x*cos x^2) = ((cos a^3) - (cos b^3)) / 3 :=
  by 
    simpa using integral_sin_pow_odd_mul_cos_pow 0 2

@[simp]
theorem integral_sin_pow_three : (∫x in a..b, sin x^3) = cos a - cos b - ((cos a^3) - (cos b^3)) / 3 :=
  by 
    simpa using integral_sin_pow_odd_mul_cos_pow 1 0

/-- Simplification of the integral of `sin x ^ m * cos x ^ n`, case `m` and `n` are both even. -/
theorem integral_sin_pow_even_mul_cos_pow_even (m n : ℕ) :
  (∫x in a..b, (sin x^2*m)*cos x^2*n) = ∫x in a..b, ((1 - cos (2*x)) / 2^m)*(1+cos (2*x)) / 2^n :=
  by 
    fieldSimp [pow_mulₓ, sin_sq, cos_sq, ←sub_sub,
      (by 
        ring :
      (2 : ℝ) - 1 = 1)]

-- error in Analysis.SpecialFunctions.Integrals: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem integral_sin_sq_mul_cos_sq : «expr = »(«expr∫ in .. , »((x), a, b, «expr * »(«expr ^ »(sin x, 2), «expr ^ »(cos x, 2))), «expr - »(«expr / »(«expr - »(b, a), 8), «expr / »(«expr - »(sin «expr * »(4, b), sin «expr * »(4, a)), 32))) :=
begin
  convert [] [expr integral_sin_pow_even_mul_cos_pow_even 1 1] ["using", 1],
  have [ident h1] [":", expr ∀
   c : exprℝ(), «expr = »(«expr * »(«expr / »(«expr - »(1, c), 2), «expr / »(«expr + »(1, c), 2)), «expr / »(«expr - »(1, «expr ^ »(c, 2)), 4))] [":=", expr λ
   c, by ring []],
  have [ident h2] [":", expr continuous (λ x, «expr ^ »(cos «expr * »(2, x), 2))] [":=", expr by continuity [] []],
  have [ident h3] [":", expr ∀ x, «expr = »(«expr * »(cos x, sin x), «expr / »(sin «expr * »(2, x), 2))] [],
  { intro [],
    rw [expr sin_two_mul] [],
    ring [] },
  have [ident h4] [":", expr ∀
   d : exprℝ(), «expr = »(«expr * »(2, «expr * »(2, d)), «expr * »(4, d))] [":=", expr λ d, by ring []],
  simp [] [] [] ["[", expr h1, ",", expr h2.interval_integrable, ",", expr integral_comp_mul_left (λ
    x, «expr ^ »(cos x, 2)), ",", expr h3, ",", expr h4, "]"] [] [],
  ring []
end

