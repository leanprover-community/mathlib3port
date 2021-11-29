import Mathbin.Analysis.PSeries 
import Mathbin.NumberTheory.ArithmeticFunction 
import Mathbin.Topology.Algebra.InfiniteSum

/-!
# L-series

Given an arithmetic function, we define the corresponding L-series.

## Main Definitions
 * `nat.arithmetic_function.l_series` is the `l_series` with a given arithmetic function as its
  coefficients. This is not the analytic continuation, just the infinite series.
 * `nat.arithmetic_function.l_series_summable` indicates that the `l_series`
  converges at a given point.

## Main Results
 * `nat.arithmetic_function.l_series_summable_of_bounded_of_one_lt_re`: the `l_series` of a bounded
  arithmetic function converges when `1 < z.re`.
 * `nat.arithmetic_function.zeta_l_series_summable_iff_one_lt_re`: the `l_series` of `ζ`
  (whose analytic continuation is the Riemann ζ) converges iff `1 < z.re`.

-/


noncomputable theory

open_locale BigOperators

namespace Nat

namespace ArithmeticFunction

/-- The L-series of an `arithmetic_function`. -/
def l_series (f : arithmetic_function ℂ) (z : ℂ) : ℂ :=
  ∑'n, f n / (n^z)

/-- `f.l_series_summable z` indicates that the L-series of `f` converges at `z`. -/
def l_series_summable (f : arithmetic_function ℂ) (z : ℂ) : Prop :=
  Summable fun n => f n / (n^z)

theorem l_series_eq_zero_of_not_l_series_summable (f : arithmetic_function ℂ) (z : ℂ) :
  ¬f.l_series_summable z → f.l_series z = 0 :=
  tsum_eq_zero_of_not_summable

@[simp]
theorem l_series_summable_zero {z : ℂ} : l_series_summable 0 z :=
  by 
    simp [l_series_summable, summable_zero]

-- error in NumberTheory.LSeries: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem l_series_summable_of_bounded_of_one_lt_real
{f : arithmetic_function exprℂ()}
{m : exprℝ()}
(h : ∀ n : exprℕ(), «expr ≤ »(complex.abs (f n), m))
{z : exprℝ()}
(hz : «expr < »(1, z)) : f.l_series_summable z :=
begin
  by_cases [expr h0, ":", expr «expr = »(m, 0)],
  { subst [expr h0],
    have [ident hf] [":", expr «expr = »(f, 0)] [":=", expr arithmetic_function.ext (λ
      n, complex.abs_eq_zero.1 (le_antisymm (h n) (complex.abs_nonneg _)))],
    simp [] [] [] ["[", expr hf, "]"] [] [] },
  refine [expr summable_of_norm_bounded (λ n : exprℕ(), «expr / »(m, «expr ^ »(n, z))) _ _],
  { simp_rw ["[", expr div_eq_mul_inv, "]"] [],
    exact [expr (summable_mul_left_iff h0).1 (real.summable_nat_rpow_inv.2 hz)] },
  { intro [ident n],
    have [ident hm] [":", expr «expr ≤ »(0, m)] [":=", expr le_trans (complex.abs_nonneg _) (h 0)],
    cases [expr n] [],
    { simp [] [] [] ["[", expr hm, ",", expr real.zero_rpow (ne_of_gt (lt_trans real.zero_lt_one hz)), "]"] [] [] },
    simp [] [] ["only"] ["[", expr complex.abs_div, ",", expr complex.norm_eq_abs, "]"] [] [],
    apply [expr div_le_div hm (h _) (real.rpow_pos_of_pos (nat.cast_pos.2 n.succ_pos) _) (le_of_eq _)],
    rw ["[", expr complex.abs_cpow_real, ",", expr complex.abs_cast_nat, "]"] [] }
end

-- error in NumberTheory.LSeries: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem l_series_summable_iff_of_re_eq_re
{f : arithmetic_function exprℂ()}
{w z : exprℂ()}
(h : «expr = »(w.re, z.re)) : «expr ↔ »(f.l_series_summable w, f.l_series_summable z) :=
begin
  suffices [ident h] [":", expr ∀
   n : exprℕ(), «expr = »(«expr / »(complex.abs (f n), complex.abs «expr ^ »(«expr↑ »(n), w)), «expr / »(complex.abs (f n), complex.abs «expr ^ »(«expr↑ »(n), z)))],
  { simp [] [] [] ["[", expr l_series_summable, ",", "<-", expr summable_norm_iff, ",", expr h, ",", expr complex.norm_eq_abs, "]"] [] [] },
  intro [ident n],
  cases [expr n] [],
  { simp [] [] [] [] [] [] },
  apply [expr congr rfl],
  have [ident h0] [":", expr «expr ≠ »((n.succ : exprℂ()), 0)] [],
  { rw ["[", expr ne.def, ",", expr nat.cast_eq_zero, "]"] [],
    apply [expr n.succ_ne_zero] },
  rw ["[", expr complex.cpow_def, ",", expr complex.cpow_def, ",", expr if_neg h0, ",", expr if_neg h0, ",", expr complex.abs_exp_eq_iff_re_eq, "]"] [],
  simp [] [] ["only"] ["[", expr h, ",", expr complex.mul_re, ",", expr mul_eq_mul_left_iff, ",", expr sub_right_inj, "]"] [] [],
  right,
  rw ["[", expr complex.log_im, ",", "<-", expr complex.of_real_nat_cast, "]"] [],
  exact [expr complex.arg_of_real_of_nonneg (le_of_lt (cast_pos.2 n.succ_pos))]
end

theorem l_series_summable_of_bounded_of_one_lt_re {f : arithmetic_function ℂ} {m : ℝ}
  (h : ∀ (n : ℕ), Complex.abs (f n) ≤ m) {z : ℂ} (hz : 1 < z.re) : f.l_series_summable z :=
  by 
    rw [←l_series_summable_iff_of_re_eq_re (Complex.of_real_re z.re)]
    apply l_series_summable_of_bounded_of_one_lt_real h 
    exact hz

open_locale ArithmeticFunction

theorem zeta_l_series_summable_iff_one_lt_re {z : ℂ} : l_series_summable ζ z ↔ 1 < z.re :=
  by 
    rw [←l_series_summable_iff_of_re_eq_re (Complex.of_real_re z.re), l_series_summable, ←summable_norm_iff,
      ←Real.summable_one_div_nat_rpow, iff_iff_eq]
    byCases' h0 : z.re = 0
    ·
      rw [h0, ←summable_nat_add_iff 1]
      swap
      ·
        infer_instance 
      apply congr rfl 
      ext n 
      simp [n.succ_ne_zero]
    ·
      apply congr rfl 
      ext n 
      cases n
      ·
        simp [h0]
      simp only [n.succ_ne_zero, one_div, cast_one, nat_coe_apply, Complex.abs_cpow_real, inv_inj₀, Complex.abs_inv,
        if_false, zeta_apply, Complex.norm_eq_abs, Complex.abs_of_nat]

@[simp]
theorem l_series_add {f g : arithmetic_function ℂ} {z : ℂ} (hf : f.l_series_summable z) (hg : g.l_series_summable z) :
  (f+g).lSeries z = f.l_series z+g.l_series z :=
  by 
    simp only [l_series, add_apply]
    rw [←tsum_add hf hg]
    apply congr rfl (funext fun n => _)
    apply _root_.add_div

end ArithmeticFunction

end Nat

