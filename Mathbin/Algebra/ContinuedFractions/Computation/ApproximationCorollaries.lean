/-
Copyright (c) 2021 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Algebra.ContinuedFractions.Computation.Approximations
import Algebra.ContinuedFractions.ConvergentsEquiv
import Algebra.Order.Archimedean
import Algebra.Algebra.Defs
import Topology.Order.Basic

#align_import algebra.continued_fractions.computation.approximation_corollaries from "leanprover-community/mathlib"@"2a0ce625dbb0ffbc7d1316597de0b25c1ec75303"

/-!
# Corollaries From Approximation Lemmas (`algebra.continued_fractions.computation.approximations`)

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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


variable {K : Type _} (v : K) [LinearOrderedField K] [FloorRing K]

open GenContFract (of)

open GenContFract

#print GenContFract.of_isSimpContFract /-
theorem GenContFract.of_isSimpContFract : (of v).IsSimpContFract := fun _ _ nth_part_num_eq =>
  of_partNum_eq_one nth_part_num_eq
#align generalized_continued_fraction.of_is_simple_continued_fraction GenContFract.of_isSimpContFract
-/

#print SimpContFract.of /-
/-- Creates the simple continued fraction of a value. -/
def SimpContFract.of : SimpContFract K :=
  ⟨of v, GenContFract.of_isSimpContFract v⟩
#align simple_continued_fraction.of SimpContFract.of
-/

#print SimpContFract.of_isContFract /-
theorem SimpContFract.of_isContFract : (SimpContFract.of v).IsContFract :=
  fun _ denom nth_part_denom_eq =>
  lt_of_lt_of_le zero_lt_one (of_one_le_get?_partDen nth_part_denom_eq)
#align simple_continued_fraction.of_is_continued_fraction SimpContFract.of_isContFract
-/

#print ContFract.of /-
/-- Creates the continued fraction of a value. -/
def ContFract.of : ContFract K :=
  ⟨SimpContFract.of v, SimpContFract.of_isContFract v⟩
#align continued_fraction.of ContFract.of
-/

namespace GenContFract

#print GenContFract.of_convs_eq_convs' /-
theorem of_convs_eq_convs' : (of v).convs = (of v).convs' :=
  @ContFract.convs_eq_convs' _ _ (ContFract.of v)
#align generalized_continued_fraction.of_convergents_eq_convergents' GenContFract.of_convs_eq_convs'
-/

#print GenContFract.convs_succ /-
/-- The recurrence relation for the `convergents` of the continued fraction expansion
of an element `v` of `K` in terms of the convergents of the inverse of its fractional part.
-/
theorem convs_succ (n : ℕ) : (of v).convs (n + 1) = ⌊v⌋ + 1 / (of (Int.fract v)⁻¹).convs n := by
  rw [of_convergents_eq_convergents', convergents'_succ, of_convergents_eq_convergents']
#align generalized_continued_fraction.convergents_succ GenContFract.convs_succ
-/

section Convergence

/-!
### Convergence

We next show that `(generalized_continued_fraction.of v).convergents v` converges to `v`.
-/


variable [Archimedean K]

open Nat

#print GenContFract.of_convergence_epsilon /-
theorem of_convergence_epsilon : ∀ ε > (0 : K), ∃ N : ℕ, ∀ n ≥ N, |v - (of v).convs n| < ε :=
  by
  intro ε ε_pos
  -- use the archimedean property to obtian a suitable N
  rcases(exists_nat_gt (1 / ε) : ∃ N' : ℕ, 1 / ε < N') with ⟨N', one_div_ε_lt_N'⟩
  let N := max N' 5
  -- set minimum to 5 to have N ≤ fib N work
  exists N
  intro n n_ge_N
  let g := of v
  cases' Decidable.em (g.terminated_at n) with terminated_at_n not_terminated_at_n
  · have : v = g.convergents n := of_correctness_of_terminated_at terminated_at_n
    have : v - g.convergents n = 0 := sub_eq_zero.elim_right this
    rw [this]
    exact_mod_cast ε_pos
  · let B := g.denominators n
    let nB := g.denominators (n + 1)
    have abs_v_sub_conv_le : |v - g.convergents n| ≤ 1 / (B * nB) :=
      abs_sub_convergents_le not_terminated_at_n
    suffices : 1 / (B * nB) < ε; exact lt_of_le_of_lt abs_v_sub_conv_le this
    -- show that `0 < (B * nB)` and then multiply by `B * nB` to get rid of the division
    have nB_ineq : (fib (n + 2) : K) ≤ nB :=
      haveI : ¬g.terminated_at (n + 1 - 1) := not_terminated_at_n
      succ_nth_fib_le_of_nth_denom (Or.inr this)
    have B_ineq : (fib (n + 1) : K) ≤ B :=
      haveI : ¬g.terminated_at (n - 1) := mt (terminated_stable n.pred_le) not_terminated_at_n
      succ_nth_fib_le_of_nth_denom (Or.inr this)
    have zero_lt_B : 0 < B :=
      haveI : (0 : K) < fib (n + 1) := by exact_mod_cast fib_pos n.zero_lt_succ
      lt_of_lt_of_le this B_ineq
    have zero_lt_mul_conts : 0 < B * nB :=
      by
      have : 0 < nB :=
        haveI : (0 : K) < fib (n + 2) := by exact_mod_cast fib_pos (n + 1).zero_lt_succ
        lt_of_lt_of_le this nB_ineq
      solve_by_elim [mul_pos]
    suffices : 1 < ε * (B * nB); exact (div_lt_iff zero_lt_mul_conts).right this
    -- use that `N ≥ n` was obtained from the archimedean property to show the following
    have one_lt_ε_mul_N : 1 < ε * n :=
      by
      have one_lt_ε_mul_N' : 1 < ε * (N' : K) := (div_lt_iff' ε_pos).left one_div_ε_lt_N'
      have : (N' : K) ≤ N := by exact_mod_cast le_max_left _ _
      have : ε * N' ≤ ε * n :=
        (mul_le_mul_left ε_pos).right (le_trans this (by exact_mod_cast n_ge_N))
      exact lt_of_lt_of_le one_lt_ε_mul_N' this
    suffices : ε * n ≤ ε * (B * nB); exact lt_of_lt_of_le one_lt_ε_mul_N this
    -- cancel `ε`
    suffices : (n : K) ≤ B * nB;
    exact (mul_le_mul_left ε_pos).right this
    show (n : K) ≤ B * nB
    calc
      (n : K) ≤ fib n := by exact_mod_cast le_fib_self <| le_trans (le_max_right N' 5) n_ge_N
      _ ≤ fib (n + 1) := by exact_mod_cast fib_le_fib_succ
      _ ≤ fib (n + 1) * fib (n + 1) := by exact_mod_cast (fib (n + 1)).le_mul_self
      _ ≤ fib (n + 1) * fib (n + 2) :=
        (mul_le_mul_of_nonneg_left (by exact_mod_cast fib_le_fib_succ)
          (by exact_mod_cast (fib (n + 1)).zero_le))
      _ ≤ B * nB :=
        mul_le_mul B_ineq nB_ineq (by exact_mod_cast (fib (n + 2)).zero_le) (le_of_lt zero_lt_B)
#align generalized_continued_fraction.of_convergence_epsilon GenContFract.of_convergence_epsilon
-/

attribute [local instance] Preorder.topology

#print GenContFract.of_convergence /-
theorem of_convergence [OrderTopology K] : Filter.Tendsto (of v).convs Filter.atTop <| nhds v := by
  simpa [LinearOrderedAddCommGroup.tendsto_nhds, abs_sub_comm] using of_convergence_epsilon v
#align generalized_continued_fraction.of_convergence GenContFract.of_convergence
-/

end Convergence

end GenContFract

