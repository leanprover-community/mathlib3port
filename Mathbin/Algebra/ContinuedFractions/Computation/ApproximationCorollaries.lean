import Mathbin.Algebra.ContinuedFractions.Computation.Approximations 
import Mathbin.Algebra.ContinuedFractions.ConvergentsEquiv 
import Mathbin.Topology.Algebra.Ordered.Basic

/-!
# Corollaries From Approximation Lemmas (`algebra.continued_fractions.computation.approximations`)

## Summary

We show that the generalized_continued_fraction given by `generalized_continued_fraction.of` in fact
is a (regular) continued fraction. Using the equivalence of the convergents computations
(`generalized_continued_fraction.convergents` and `generalized_continued_fraction.convergents'`) for
continued fractions (see `algebra.continued_fractions.convergents_equiv`), it follows that the
convergents computations for `generalized_continued_fraction.of` are equivalent.

Moreover, we show the convergence of the continued fractions computations, that is
`(generalized_continued_fraction.of v).convergents` indeed computes `v` in the limit.

## Main Definitions

- `continued_fraction.of` returns the (regular) continued fraction of a value.

## Main Theorems

- `generalized_continued_fraction.of_convergents_eq_convergents'` shows that the convergents
  computations for `generalized_continued_fraction.of` are equivalent.
- `generalized_continued_fraction.of_convergence` shows that
  `(generalized_continued_fraction.of v).convergents` converges to `v`.

## Tags

convergence, fractions
-/


variable{K : Type _}(v : K)[LinearOrderedField K][FloorRing K]

open generalized_continued_fraction(of)

open GeneralizedContinuedFraction

theorem GeneralizedContinuedFraction.of_is_simple_continued_fraction : (of v).IsSimpleContinuedFraction :=
  fun _ _ nth_part_num_eq => of_part_num_eq_one nth_part_num_eq

/-- Creates the simple continued fraction of a value. -/
def SimpleContinuedFraction.of : SimpleContinuedFraction K :=
  ⟨of v, GeneralizedContinuedFraction.of_is_simple_continued_fraction v⟩

theorem SimpleContinuedFraction.of_is_continued_fraction : (SimpleContinuedFraction.of v).IsContinuedFraction :=
  fun _ denom nth_part_denom_eq => lt_of_lt_of_leₓ zero_lt_one (of_one_le_nth_part_denom nth_part_denom_eq)

/-- Creates the continued fraction of a value. -/
def ContinuedFraction.of : ContinuedFraction K :=
  ⟨SimpleContinuedFraction.of v, SimpleContinuedFraction.of_is_continued_fraction v⟩

namespace GeneralizedContinuedFraction

theorem of_convergents_eq_convergents' : (of v).convergents = (of v).convergents' :=
  @ContinuedFraction.convergents_eq_convergents' _ _ (ContinuedFraction.of v)

section Convergence

/-!
### Convergence

We next show that `(generalized_continued_fraction.of v).convergents v` converges to `v`.
-/


variable[Archimedean K]

open Nat

-- error in Algebra.ContinuedFractions.Computation.ApproximationCorollaries: ././Mathport/Syntax/Translate/Basic.lean:176:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Meta.solveByElim'
theorem of_convergence_epsilon : ∀
ε «expr > » (0 : K), «expr∃ , »((N : exprℕ()), ∀
 n «expr ≥ » N, «expr < »(«expr| |»(«expr - »(v, (of v).convergents n)), ε)) :=
begin
  assume [binders (ε ε_pos)],
  rcases [expr (exists_nat_gt «expr / »(1, ε) : «expr∃ , »((N' : exprℕ()), «expr < »(«expr / »(1, ε), N'))), "with", "⟨", ident N', ",", ident one_div_ε_lt_N', "⟩"],
  let [ident N] [] [":=", expr max N' 5],
  existsi [expr N],
  assume [binders (n n_ge_N)],
  let [ident g] [] [":=", expr of v],
  cases [expr decidable.em (g.terminated_at n)] ["with", ident terminated_at_n, ident not_terminated_at_n],
  { have [] [":", expr «expr = »(v, g.convergents n)] [],
    from [expr of_correctness_of_terminated_at terminated_at_n],
    have [] [":", expr «expr = »(«expr - »(v, g.convergents n), 0)] [],
    from [expr sub_eq_zero.elim_right this],
    rw ["[", expr this, "]"] [],
    exact_mod_cast [expr ε_pos] },
  { let [ident B] [] [":=", expr g.denominators n],
    let [ident nB] [] [":=", expr g.denominators «expr + »(n, 1)],
    have [ident abs_v_sub_conv_le] [":", expr «expr ≤ »(«expr| |»(«expr - »(v, g.convergents n)), «expr / »(1, «expr * »(B, nB)))] [],
    from [expr abs_sub_convergents_le not_terminated_at_n],
    suffices [] [":", expr «expr < »(«expr / »(1, «expr * »(B, nB)), ε)],
    from [expr lt_of_le_of_lt abs_v_sub_conv_le this],
    have [ident nB_ineq] [":", expr «expr ≤ »((fib «expr + »(n, 2) : K), nB)] [],
    by { have [] [":", expr «expr¬ »(g.terminated_at «expr - »(«expr + »(n, 1), 1))] [],
      from [expr not_terminated_at_n],
      exact [expr succ_nth_fib_le_of_nth_denom (or.inr this)] },
    have [ident B_ineq] [":", expr «expr ≤ »((fib «expr + »(n, 1) : K), B)] [],
    by { have [] [":", expr «expr¬ »(g.terminated_at «expr - »(n, 1))] [],
      from [expr mt (terminated_stable n.pred_le) not_terminated_at_n],
      exact [expr succ_nth_fib_le_of_nth_denom (or.inr this)] },
    have [ident zero_lt_B] [":", expr «expr < »(0, B)] [],
    by { have [] [":", expr «expr < »((0 : K), fib «expr + »(n, 1))] [],
      by exact_mod_cast [expr fib_pos n.zero_lt_succ],
      exact [expr lt_of_lt_of_le this B_ineq] },
    have [ident zero_lt_mul_conts] [":", expr «expr < »(0, «expr * »(B, nB))] [],
    by { have [] [":", expr «expr < »(0, nB)] [],
      by { have [] [":", expr «expr < »((0 : K), fib «expr + »(n, 2))] [],
        by exact_mod_cast [expr fib_pos «expr + »(n, 1).zero_lt_succ],
        exact [expr lt_of_lt_of_le this nB_ineq] },
      solve_by_elim [] [] ["[", expr mul_pos, "]"] [] },
    suffices [] [":", expr «expr < »(1, «expr * »(ε, «expr * »(B, nB)))],
    from [expr (div_lt_iff zero_lt_mul_conts).elim_right this],
    have [ident one_lt_ε_mul_N] [":", expr «expr < »(1, «expr * »(ε, n))] [],
    by { have [ident one_lt_ε_mul_N'] [":", expr «expr < »(1, «expr * »(ε, (N' : K)))] [],
      from [expr (div_lt_iff' ε_pos).elim_left one_div_ε_lt_N'],
      have [] [":", expr «expr ≤ »((N' : K), N)] [],
      by exact_mod_cast [expr le_max_left _ _],
      have [] [":", expr «expr ≤ »(«expr * »(ε, N'), «expr * »(ε, n))] [],
      from [expr (mul_le_mul_left ε_pos).elim_right (le_trans this (by exact_mod_cast [expr n_ge_N]))],
      exact [expr lt_of_lt_of_le one_lt_ε_mul_N' this] },
    suffices [] [":", expr «expr ≤ »(«expr * »(ε, n), «expr * »(ε, «expr * »(B, nB)))],
    from [expr lt_of_lt_of_le one_lt_ε_mul_N this],
    suffices [] [":", expr «expr ≤ »((n : K), «expr * »(B, nB))],
    from [expr (mul_le_mul_left ε_pos).elim_right this],
    show [expr «expr ≤ »((n : K), «expr * »(B, nB))],
    calc
      «expr ≤ »((n : K), fib n) : by exact_mod_cast [expr «expr $ »(le_fib_self, le_trans (le_max_right N' 5) n_ge_N)]
      «expr ≤ »(..., fib «expr + »(n, 1)) : by exact_mod_cast [expr fib_le_fib_succ]
      «expr ≤ »(..., «expr * »(fib «expr + »(n, 1), fib «expr + »(n, 1))) : by exact_mod_cast [expr (fib «expr + »(n, 1)).le_mul_self]
      «expr ≤ »(..., «expr * »(fib «expr + »(n, 1), fib «expr + »(n, 2))) : mul_le_mul_of_nonneg_left (by exact_mod_cast [expr fib_le_fib_succ]) (by exact_mod_cast [expr (fib «expr + »(n, 1)).zero_le])
      «expr ≤ »(..., «expr * »(B, nB)) : mul_le_mul B_ineq nB_ineq (by exact_mod_cast [expr (fib «expr + »(n, 2)).zero_le]) (le_of_lt zero_lt_B) }
end

attribute [local instance] Preorderₓ.topology

theorem of_convergence [OrderTopology K] : Filter.Tendsto (of v).convergents Filter.atTop$ nhds v :=
  by 
    simpa [LinearOrderedAddCommGroup.tendsto_nhds, abs_sub_comm] using of_convergence_epsilon v

end Convergence

end GeneralizedContinuedFraction

