import Mathbin.Analysis.SpecificLimits 
import Mathbin.Analysis.Analytic.Basic 
import Mathbin.Analysis.Complex.Basic 
import Mathbin.Data.Nat.Choose.Cast

/-!
# Exponential in a Banach algebra

In this file, we define `exp 𝕂 𝔸`, the exponential map in a normed algebra `𝔸` over a nondiscrete
normed field `𝕂`. Although the definition doesn't require `𝔸` to be complete, we need to assume it
for most results.

We then prove some basic results, but we avoid importing derivatives here to minimize dependencies.
Results involving derivatives and comparisons with `real.exp` and `complex.exp` can be found in
`analysis/special_functions/exponential`.

## Main results

We prove most result for an arbitrary field `𝕂`, and then specialize to `𝕂 = ℝ` or `𝕂 = ℂ`.

### General case

- `exp_add_of_commute_of_lt_radius` : if `𝕂` has characteristic zero, then given two commuting
  elements `x` and `y` in the disk of convergence, we have
  `exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`
- `exp_add_of_lt_radius` : if `𝕂` has characteristic zero and `𝔸` is commutative, then given two
  elements `x` and `y` in the disk of convergence, we have
  `exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`

### `𝕂 = ℝ` or `𝕂 = ℂ`

- `exp_series_radius_eq_top` : the `formal_multilinear_series` defining `exp 𝕂 𝔸` has infinite
  radius of convergence
- `exp_add_of_commute` : given two commuting elements `x` and `y`, we have
  `exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`
- `exp_add` : if `𝔸` is commutative, then we have `exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`
  for any `x` and `y`

### Other useful compatibility results

- `exp_eq_exp` : if `𝔸` is a normed algebra over two fields `𝕂` and `𝕂'`, then `exp 𝕂 𝔸 = exp 𝕂' 𝔸`

-/


open Filter IsROrC ContinuousMultilinearMap NormedField Asymptotics

open_locale Nat TopologicalSpace BigOperators Ennreal

section AnyFieldAnyAlgebra

variable(𝕂 𝔸 : Type _)[NondiscreteNormedField 𝕂][NormedRing 𝔸][NormedAlgebra 𝕂 𝔸]

/-- In a Banach algebra `𝔸` over a normed field `𝕂`, `exp_series 𝕂 𝔸` is the
`formal_multilinear_series` whose `n`-th term is the map `(xᵢ) : 𝔸ⁿ ↦ (1/n! : 𝕂) • ∏ xᵢ`.
Its sum is the exponential map `exp 𝕂 𝔸 : 𝔸 → 𝔸`. -/
def expSeries : FormalMultilinearSeries 𝕂 𝔸 𝔸 :=
  fun n => (1 / n ! : 𝕂) • ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸

/-- In a Banach algebra `𝔸` over a normed field `𝕂`, `exp 𝕂 𝔸 : 𝔸 → 𝔸` is the exponential map
determined by the action of `𝕂` on `𝔸`.
It is defined as the sum of the `formal_multilinear_series` `exp_series 𝕂 𝔸`. -/
noncomputable def exp (x : 𝔸) : 𝔸 :=
  (expSeries 𝕂 𝔸).Sum x

variable{𝕂 𝔸}

theorem exp_series_apply_eq (x : 𝔸) (n : ℕ) : (expSeries 𝕂 𝔸 n fun _ => x) = (1 / n ! : 𝕂) • (x^n) :=
  by 
    simp [expSeries]

theorem exp_series_apply_eq' (x : 𝔸) : (fun n => expSeries 𝕂 𝔸 n fun _ => x) = fun n => (1 / n ! : 𝕂) • (x^n) :=
  funext (exp_series_apply_eq x)

theorem exp_series_apply_eq_field (x : 𝕂) (n : ℕ) : (expSeries 𝕂 𝕂 n fun _ => x) = (x^n) / n ! :=
  by 
    rw [div_eq_inv_mul, ←smul_eq_mul, inv_eq_one_div]
    exact exp_series_apply_eq x n

theorem exp_series_apply_eq_field' (x : 𝕂) : (fun n => expSeries 𝕂 𝕂 n fun _ => x) = fun n => (x^n) / n ! :=
  funext (exp_series_apply_eq_field x)

theorem exp_series_sum_eq (x : 𝔸) : (expSeries 𝕂 𝔸).Sum x = ∑'n : ℕ, (1 / n ! : 𝕂) • (x^n) :=
  tsum_congr fun n => exp_series_apply_eq x n

theorem exp_series_sum_eq_field (x : 𝕂) : (expSeries 𝕂 𝕂).Sum x = ∑'n : ℕ, (x^n) / n ! :=
  tsum_congr fun n => exp_series_apply_eq_field x n

theorem exp_eq_tsum : exp 𝕂 𝔸 = fun x : 𝔸 => ∑'n : ℕ, (1 / n ! : 𝕂) • (x^n) :=
  funext exp_series_sum_eq

theorem exp_eq_tsum_field : exp 𝕂 𝕂 = fun x : 𝕂 => ∑'n : ℕ, (x^n) / n ! :=
  funext exp_series_sum_eq_field

-- error in Analysis.NormedSpace.Exponential: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exp_zero : «expr = »(exp 𝕂 𝔸 0, 1) :=
begin
  suffices [] [":", expr «expr = »(λ
    x : 𝔸, «expr∑' , »((n : exprℕ()), «expr • »((«expr / »(1, «expr !»(n)) : 𝕂), «expr ^ »(x, n))) 0, «expr∑' , »((n : exprℕ()), if «expr = »(n, 0) then 1 else 0))],
  { have [ident key] [":", expr ∀
     n «expr ∉ » ({0} : finset exprℕ()), «expr = »(if «expr = »(n, 0) then (1 : 𝔸) else 0, 0)] [],
    from [expr λ n hn, if_neg (finset.not_mem_singleton.mp hn)],
    rw ["[", expr exp_eq_tsum, ",", expr this, ",", expr tsum_eq_sum key, ",", expr finset.sum_singleton, "]"] [],
    simp [] [] [] [] [] [] },
  refine [expr tsum_congr (λ n, _)],
  split_ifs [] ["with", ident h, ident h]; simp [] [] [] ["[", expr h, "]"] [] []
end

theorem norm_exp_series_summable_of_mem_ball (x : 𝔸) (hx : x ∈ Emetric.Ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
  Summable fun n => ∥expSeries 𝕂 𝔸 n fun _ => x∥ :=
  (expSeries 𝕂 𝔸).summable_norm_apply hx

theorem norm_exp_series_summable_of_mem_ball' (x : 𝔸) (hx : x ∈ Emetric.Ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
  Summable fun n => ∥(1 / n ! : 𝕂) • (x^n)∥ :=
  by 
    change Summable (norm ∘ _)
    rw [←exp_series_apply_eq']
    exact norm_exp_series_summable_of_mem_ball x hx

theorem norm_exp_series_field_summable_of_mem_ball (x : 𝕂) (hx : x ∈ Emetric.Ball (0 : 𝕂) (expSeries 𝕂 𝕂).radius) :
  Summable fun n => ∥(x^n) / n !∥ :=
  by 
    change Summable (norm ∘ _)
    rw [←exp_series_apply_eq_field']
    exact norm_exp_series_summable_of_mem_ball x hx

section CompleteAlgebra

variable[CompleteSpace 𝔸]

theorem exp_series_summable_of_mem_ball (x : 𝔸) (hx : x ∈ Emetric.Ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
  Summable fun n => expSeries 𝕂 𝔸 n fun _ => x :=
  summable_of_summable_norm (norm_exp_series_summable_of_mem_ball x hx)

theorem exp_series_summable_of_mem_ball' (x : 𝔸) (hx : x ∈ Emetric.Ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
  Summable fun n => (1 / n ! : 𝕂) • (x^n) :=
  summable_of_summable_norm (norm_exp_series_summable_of_mem_ball' x hx)

theorem exp_series_field_summable_of_mem_ball [CompleteSpace 𝕂] (x : 𝕂)
  (hx : x ∈ Emetric.Ball (0 : 𝕂) (expSeries 𝕂 𝕂).radius) : Summable fun n => (x^n) / n ! :=
  summable_of_summable_norm (norm_exp_series_field_summable_of_mem_ball x hx)

theorem exp_series_has_sum_exp_of_mem_ball (x : 𝔸) (hx : x ∈ Emetric.Ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
  HasSum (fun n => expSeries 𝕂 𝔸 n fun _ => x) (exp 𝕂 𝔸 x) :=
  FormalMultilinearSeries.has_sum (expSeries 𝕂 𝔸) hx

theorem exp_series_has_sum_exp_of_mem_ball' (x : 𝔸) (hx : x ∈ Emetric.Ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
  HasSum (fun n => (1 / n ! : 𝕂) • (x^n)) (exp 𝕂 𝔸 x) :=
  by 
    rw [←exp_series_apply_eq']
    exact exp_series_has_sum_exp_of_mem_ball x hx

theorem exp_series_field_has_sum_exp_of_mem_ball [CompleteSpace 𝕂] (x : 𝕂)
  (hx : x ∈ Emetric.Ball (0 : 𝕂) (expSeries 𝕂 𝕂).radius) : HasSum (fun n => (x^n) / n !) (exp 𝕂 𝕂 x) :=
  by 
    rw [←exp_series_apply_eq_field']
    exact exp_series_has_sum_exp_of_mem_ball x hx

theorem has_fpower_series_on_ball_exp_of_radius_pos (h : 0 < (expSeries 𝕂 𝔸).radius) :
  HasFpowerSeriesOnBall (exp 𝕂 𝔸) (expSeries 𝕂 𝔸) 0 (expSeries 𝕂 𝔸).radius :=
  (expSeries 𝕂 𝔸).HasFpowerSeriesOnBall h

theorem has_fpower_series_at_exp_zero_of_radius_pos (h : 0 < (expSeries 𝕂 𝔸).radius) :
  HasFpowerSeriesAt (exp 𝕂 𝔸) (expSeries 𝕂 𝔸) 0 :=
  (has_fpower_series_on_ball_exp_of_radius_pos h).HasFpowerSeriesAt

theorem continuous_on_exp : ContinuousOn (exp 𝕂 𝔸) (Emetric.Ball 0 (expSeries 𝕂 𝔸).radius) :=
  FormalMultilinearSeries.continuous_on

-- error in Analysis.NormedSpace.Exponential: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem analytic_at_exp_of_mem_ball
(x : 𝔸)
(hx : «expr ∈ »(x, emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius)) : analytic_at 𝕂 (exp 𝕂 𝔸) x :=
begin
  by_cases [expr h, ":", expr «expr = »((exp_series 𝕂 𝔸).radius, 0)],
  { rw [expr h] ["at", ident hx],
    exact [expr (ennreal.not_lt_zero hx).elim] },
  { have [ident h] [] [":=", expr pos_iff_ne_zero.mpr h],
    exact [expr (has_fpower_series_on_ball_exp_of_radius_pos h).analytic_at_of_mem hx] }
end

-- error in Analysis.NormedSpace.Exponential: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- In a Banach-algebra `𝔸` over a normed field `𝕂` of characteristic zero, if `x` and `y` are
in the disk of convergence and commute, then `exp 𝕂 𝔸 (x + y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`. -/
theorem exp_add_of_commute_of_mem_ball
[char_zero 𝕂]
{x y : 𝔸}
(hxy : commute x y)
(hx : «expr ∈ »(x, emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius))
(hy : «expr ∈ »(y, emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius)) : «expr = »(exp 𝕂 𝔸 «expr + »(x, y), «expr * »(exp 𝕂 𝔸 x, exp 𝕂 𝔸 y)) :=
begin
  rw ["[", expr exp_eq_tsum, ",", expr tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (norm_exp_series_summable_of_mem_ball' x hx) (norm_exp_series_summable_of_mem_ball' y hy), "]"] [],
  dsimp ["only"] [] [] [],
  conv_lhs [] [] { congr,
    funext,
    rw ["[", expr hxy.add_pow' _, ",", expr finset.smul_sum, "]"] },
  refine [expr tsum_congr (λ n, «expr $ »(finset.sum_congr rfl, λ kl hkl, _))],
  rw ["[", expr nsmul_eq_smul_cast 𝕂, ",", expr smul_smul, ",", expr smul_mul_smul, ",", "<-", expr finset.nat.mem_antidiagonal.mp hkl, ",", expr nat.cast_add_choose, ",", expr finset.nat.mem_antidiagonal.mp hkl, "]"] [],
  congr' [1] [],
  have [] [":", expr «expr ≠ »((«expr !»(n) : 𝕂), 0)] [":=", expr nat.cast_ne_zero.mpr n.factorial_ne_zero],
  field_simp [] ["[", expr this, "]"] [] []
end

end CompleteAlgebra

end AnyFieldAnyAlgebra

section AnyFieldCommAlgebra

variable{𝕂 𝔸 : Type _}[NondiscreteNormedField 𝕂][NormedCommRing 𝔸][NormedAlgebra 𝕂 𝔸][CompleteSpace 𝔸]

/-- In a commutative Banach-algebra `𝔸` over a normed field `𝕂` of characteristic zero,
`exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)` for all `x`, `y` in the disk of convergence. -/
theorem exp_add_of_mem_ball [CharZero 𝕂] {x y : 𝔸} (hx : x ∈ Emetric.Ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius)
  (hy : y ∈ Emetric.Ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : exp 𝕂 𝔸 (x+y) = exp 𝕂 𝔸 x*exp 𝕂 𝔸 y :=
  exp_add_of_commute_of_mem_ball (Commute.all x y) hx hy

end AnyFieldCommAlgebra

section IsROrC

section AnyAlgebra

variable(𝕂 𝔸 : Type _)[IsROrC 𝕂][NormedRing 𝔸][NormedAlgebra 𝕂 𝔸]

-- error in Analysis.NormedSpace.Exponential: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- In a normed algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, the series defining the exponential map
has an infinite radius of convergence. -/
theorem exp_series_radius_eq_top : «expr = »((exp_series 𝕂 𝔸).radius, «expr∞»()) :=
begin
  refine [expr (exp_series 𝕂 𝔸).radius_eq_top_of_summable_norm (λ r, _)],
  refine [expr summable_of_norm_bounded_eventually _ (real.summable_pow_div_factorial r) _],
  filter_upwards ["[", expr eventually_cofinite_ne 0, "]"] [],
  intros [ident n, ident hn],
  rw ["[", expr norm_mul, ",", expr norm_norm (exp_series 𝕂 𝔸 n), ",", expr exp_series, ",", expr norm_smul, ",", expr norm_div, ",", expr norm_one, ",", expr norm_pow, ",", expr nnreal.norm_eq, ",", expr norm_eq_abs, ",", expr abs_cast_nat, ",", expr mul_comm, ",", "<-", expr mul_assoc, ",", "<-", expr mul_div_assoc, ",", expr mul_one, "]"] [],
  have [] [":", expr «expr ≤ »(«expr∥ ∥»(continuous_multilinear_map.mk_pi_algebra_fin 𝕂 n 𝔸), 1)] [":=", expr norm_mk_pi_algebra_fin_le_of_pos (nat.pos_of_ne_zero hn)],
  exact [expr mul_le_of_le_one_right (div_nonneg (pow_nonneg r.coe_nonneg n) «expr !»(n).cast_nonneg) this]
end

theorem exp_series_radius_pos : 0 < (expSeries 𝕂 𝔸).radius :=
  by 
    rw [exp_series_radius_eq_top]
    exact WithTop.zero_lt_top

variable{𝕂 𝔸}

section CompleteAlgebra

theorem norm_exp_series_summable (x : 𝔸) : Summable fun n => ∥expSeries 𝕂 𝔸 n fun _ => x∥ :=
  norm_exp_series_summable_of_mem_ball x ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

theorem norm_exp_series_summable' (x : 𝔸) : Summable fun n => ∥(1 / n ! : 𝕂) • (x^n)∥ :=
  norm_exp_series_summable_of_mem_ball' x ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

theorem norm_exp_series_field_summable (x : 𝕂) : Summable fun n => ∥(x^n) / n !∥ :=
  norm_exp_series_field_summable_of_mem_ball x ((exp_series_radius_eq_top 𝕂 𝕂).symm ▸ edist_lt_top _ _)

variable[CompleteSpace 𝔸]

theorem exp_series_summable (x : 𝔸) : Summable fun n => expSeries 𝕂 𝔸 n fun _ => x :=
  summable_of_summable_norm (norm_exp_series_summable x)

theorem exp_series_summable' (x : 𝔸) : Summable fun n => (1 / n ! : 𝕂) • (x^n) :=
  summable_of_summable_norm (norm_exp_series_summable' x)

theorem exp_series_field_summable (x : 𝕂) : Summable fun n => (x^n) / n ! :=
  summable_of_summable_norm (norm_exp_series_field_summable x)

theorem exp_series_has_sum_exp (x : 𝔸) : HasSum (fun n => expSeries 𝕂 𝔸 n fun _ => x) (exp 𝕂 𝔸 x) :=
  exp_series_has_sum_exp_of_mem_ball x ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

theorem exp_series_has_sum_exp' (x : 𝔸) : HasSum (fun n => (1 / n ! : 𝕂) • (x^n)) (exp 𝕂 𝔸 x) :=
  exp_series_has_sum_exp_of_mem_ball' x ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

theorem exp_series_field_has_sum_exp (x : 𝕂) : HasSum (fun n => (x^n) / n !) (exp 𝕂 𝕂 x) :=
  exp_series_field_has_sum_exp_of_mem_ball x ((exp_series_radius_eq_top 𝕂 𝕂).symm ▸ edist_lt_top _ _)

theorem exp_has_fpower_series_on_ball : HasFpowerSeriesOnBall (exp 𝕂 𝔸) (expSeries 𝕂 𝔸) 0 ∞ :=
  exp_series_radius_eq_top 𝕂 𝔸 ▸ has_fpower_series_on_ball_exp_of_radius_pos (exp_series_radius_pos _ _)

theorem exp_has_fpower_series_at_zero : HasFpowerSeriesAt (exp 𝕂 𝔸) (expSeries 𝕂 𝔸) 0 :=
  exp_has_fpower_series_on_ball.HasFpowerSeriesAt

theorem exp_continuous : Continuous (exp 𝕂 𝔸) :=
  by 
    rw [continuous_iff_continuous_on_univ, ←Metric.eball_top_eq_univ (0 : 𝔸), ←exp_series_radius_eq_top 𝕂 𝔸]
    exact continuous_on_exp

theorem exp_analytic (x : 𝔸) : AnalyticAt 𝕂 (exp 𝕂 𝔸) x :=
  analytic_at_exp_of_mem_ball x ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

end CompleteAlgebra

attribute [local instance] char_zero_R_or_C

/-- In a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, if `x` and `y` commute, then
`exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`. -/
theorem exp_add_of_commute [CompleteSpace 𝔸] {x y : 𝔸} (hxy : Commute x y) : exp 𝕂 𝔸 (x+y) = exp 𝕂 𝔸 x*exp 𝕂 𝔸 y :=
  exp_add_of_commute_of_mem_ball hxy ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
    ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

end AnyAlgebra

section CommAlgebra

variable{𝕂 𝔸 : Type _}[IsROrC 𝕂][NormedCommRing 𝔸][NormedAlgebra 𝕂 𝔸][CompleteSpace 𝔸]

attribute [local instance] char_zero_R_or_C

/-- In a comutative Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`,
`exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`. -/
theorem exp_add {x y : 𝔸} : exp 𝕂 𝔸 (x+y) = exp 𝕂 𝔸 x*exp 𝕂 𝔸 y :=
  exp_add_of_mem_ball ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
    ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

end CommAlgebra

end IsROrC

section ScalarTower

variable(𝕂 𝕂' 𝔸 :
    Type _)[NondiscreteNormedField 𝕂][NondiscreteNormedField 𝕂'][NormedRing 𝔸][NormedAlgebra 𝕂 𝔸][NormedAlgebra 𝕂' 𝔸]

/-- If a normed ring `𝔸` is a normed algebra over two fields, then they define the same
`exp_series` on `𝔸`. -/
theorem exp_series_eq_exp_series (n : ℕ) (x : 𝔸) : (expSeries 𝕂 𝔸 n fun _ => x) = expSeries 𝕂' 𝔸 n fun _ => x :=
  by 
    rw [expSeries, expSeries, smul_apply, mk_pi_algebra_fin_apply, List.of_fn_const, List.prod_repeat, smul_apply,
      mk_pi_algebra_fin_apply, List.of_fn_const, List.prod_repeat, one_div, one_div, inv_nat_cast_smul_eq 𝕂 𝕂']

/-- If a normed ring `𝔸` is a normed algebra over two fields, then they define the same
exponential function on `𝔸`. -/
theorem exp_eq_exp : exp 𝕂 𝔸 = exp 𝕂' 𝔸 :=
  by 
    ext 
    rw [exp, exp]
    refine' tsum_congr fun n => _ 
    rw [exp_series_eq_exp_series 𝕂 𝕂' 𝔸 n x]

theorem exp_ℝ_ℂ_eq_exp_ℂ_ℂ : exp ℝ ℂ = exp ℂ ℂ :=
  exp_eq_exp ℝ ℂ ℂ

end ScalarTower

