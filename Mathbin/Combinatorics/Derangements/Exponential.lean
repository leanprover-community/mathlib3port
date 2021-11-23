import Mathbin.Analysis.SpecialFunctions.Exponential 
import Mathbin.Combinatorics.Derangements.Finite 
import Mathbin.Order.Filter.Basic

/-!
# Derangement exponential series

This file proves that the probability of a permutation on n elements being a derangement is 1/e.
The specific lemma is `num_derangements_tendsto_inv_e`.
-/


open Filter

open_locale BigOperators

open_locale TopologicalSpace

-- error in Combinatorics.Derangements.Exponential: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem num_derangements_tendsto_inv_e : tendsto (λ
 n, «expr / »((num_derangements n : exprℝ()), n.factorial)) at_top (expr𝓝() (real.exp «expr- »(1))) :=
begin
  let [ident s] [":", expr exprℕ() → exprℝ()] [":=", expr λ
   n, «expr∑ in , »((k), finset.range n, «expr / »(«expr ^ »((«expr- »(1) : exprℝ()), k), k.factorial))],
  suffices [] [":", expr ∀
   n : exprℕ(), «expr = »(«expr / »((num_derangements n : exprℝ()), n.factorial), s «expr + »(n, 1))],
  { simp_rw [expr this] [],
    rw [expr tendsto_add_at_top_iff_nat 1] [],
    apply [expr has_sum.tendsto_sum_nat],
    rw [expr real.exp_eq_exp_ℝ_ℝ] [],
    exact [expr exp_series_field_has_sum_exp («expr- »(1) : exprℝ())] },
  intro [ident n],
  rw ["[", "<-", expr int.cast_coe_nat, ",", expr num_derangements_sum, "]"] [],
  push_cast [] [],
  rw [expr finset.sum_div] [],
  refine [expr finset.sum_congr (refl _) _],
  intros [ident k, ident hk],
  have [ident h_le] [":", expr «expr ≤ »(k, n)] [":=", expr finset.mem_range_succ_iff.mp hk],
  rw ["[", expr nat.asc_factorial_eq_div, ",", expr add_tsub_cancel_of_le h_le, "]"] [],
  push_cast ["[", expr nat.factorial_dvd_factorial h_le, "]"] [],
  field_simp [] ["[", expr nat.factorial_ne_zero, "]"] [] [],
  ring []
end

