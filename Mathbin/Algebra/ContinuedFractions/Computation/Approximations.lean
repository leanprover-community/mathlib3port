import Mathbin.Algebra.ContinuedFractions.Computation.CorrectnessTerminating 
import Mathbin.Data.Nat.Fib 
import Mathbin.Tactic.SolveByElim

/-!
# Approximations for Continued Fraction Computations (`generalized_continued_fraction.of`)

## Summary

This file contains useful approximations for the values involved in the continued fractions
computation `generalized_continued_fraction.of`. In particular, we derive the so-called
*determinant formula* for `generalized_continued_fraction.of`:
`Aₙ * Bₙ₊₁ - Bₙ * Aₙ₊₁ = (-1)^(n + 1)`.

Moreover, we derive some upper bounds for the error term when computing a continued fraction up a
given position, i.e. bounds for the term
`|v - (generalized_continued_fraction.of v).convergents n|`. The derived bounds will show us that
the error term indeed gets smaller. As a corollary, we will be able to show that
`(generalized_continued_fraction.of v).convergents` converges to `v` in
`algebra.continued_fractions.computation.approximation_corollaries`.

## Main Theorems

- `generalized_continued_fraction.of_part_num_eq_one`: shows that all partial numerators `aᵢ` are
  equal to one.
- `generalized_continued_fraction.exists_int_eq_of_part_denom`: shows that all partial denominators
  `bᵢ` correspond to an integer.
- `generalized_continued_fraction.one_le_of_nth_part_denom`: shows that `1 ≤ bᵢ`.
- `generalized_continued_fraction.succ_nth_fib_le_of_nth_denom`: shows that the `n`th denominator
  `Bₙ` is greater than or equal to the `n + 1`th fibonacci number `nat.fib (n + 1)`.
- `generalized_continued_fraction.le_of_succ_nth_denom`: shows that `bₙ * Bₙ ≤ Bₙ₊₁`, where `bₙ` is
  the `n`th partial denominator of the continued fraction.
- `generalized_continued_fraction.abs_sub_convergents_le`: shows that
  `|v - Aₙ / Bₙ| ≤ 1 / (Bₙ * Bₙ₊₁)`, where `Aₙ` is the nth partial numerator.

## References

- [*Hardy, GH and Wright, EM and Heath-Brown, Roger and Silverman, Joseph*][hardy2008introduction]
- https://en.wikipedia.org/wiki/Generalized_continued_fraction#The_determinant_formula

-/


namespace GeneralizedContinuedFraction

open generalized_continued_fraction(of)

open Int

variable {K : Type _} {v : K} {n : ℕ} [LinearOrderedField K] [FloorRing K]

namespace IntFractPair

/-!
We begin with some lemmas about the stream of `int_fract_pair`s, which presumably are not
of great interest for the end user.
-/


-- error in Algebra.ContinuedFractions.Computation.Approximations: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Shows that the fractional parts of the stream are in `[0,1)`. -/
theorem nth_stream_fr_nonneg_lt_one
{ifp_n : int_fract_pair K}
(nth_stream_eq : «expr = »(int_fract_pair.stream v n, some ifp_n)) : «expr ∧ »(«expr ≤ »(0, ifp_n.fr), «expr < »(ifp_n.fr, 1)) :=
begin
  cases [expr n] [],
  case [ident nat.zero] { have [] [":", expr «expr = »(int_fract_pair.of v, ifp_n)] [],
    by injection [expr nth_stream_eq] [],
    rw ["[", "<-", expr this, ",", expr int_fract_pair.of, "]"] [],
    exact [expr ⟨fract_nonneg _, fract_lt_one _⟩] },
  case [ident nat.succ] { rcases [expr succ_nth_stream_eq_some_iff.elim_left nth_stream_eq, "with", "⟨", "_", ",", "_", ",", "_", ",", ident ifp_of_eq_ifp_n, "⟩"],
    rw ["[", "<-", expr ifp_of_eq_ifp_n, ",", expr int_fract_pair.of, "]"] [],
    exact [expr ⟨fract_nonneg _, fract_lt_one _⟩] }
end

/-- Shows that the fractional parts of the stream are nonnegative. -/
theorem nth_stream_fr_nonneg {ifp_n : int_fract_pair K} (nth_stream_eq : int_fract_pair.stream v n = some ifp_n) :
  0 ≤ ifp_n.fr :=
  (nth_stream_fr_nonneg_lt_one nth_stream_eq).left

/-- Shows that the fractional parts of the stream are smaller than one. -/
theorem nth_stream_fr_lt_one {ifp_n : int_fract_pair K} (nth_stream_eq : int_fract_pair.stream v n = some ifp_n) :
  ifp_n.fr < 1 :=
  (nth_stream_fr_nonneg_lt_one nth_stream_eq).right

-- error in Algebra.ContinuedFractions.Computation.Approximations: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Shows that the integer parts of the stream are at least one. -/
theorem one_le_succ_nth_stream_b
{ifp_succ_n : int_fract_pair K}
(succ_nth_stream_eq : «expr = »(int_fract_pair.stream v «expr + »(n, 1), some ifp_succ_n)) : «expr ≤ »(1, ifp_succ_n.b) :=
begin
  obtain ["⟨", ident ifp_n, ",", ident nth_stream_eq, ",", ident stream_nth_fr_ne_zero, ",", "⟨", "-", "⟩", "⟩", ":", expr «expr∃ , »((ifp_n), «expr ∧ »(«expr = »(int_fract_pair.stream v n, some ifp_n), «expr ∧ »(«expr ≠ »(ifp_n.fr, 0), «expr = »(int_fract_pair.of «expr ⁻¹»(ifp_n.fr), ifp_succ_n))))],
  from [expr succ_nth_stream_eq_some_iff.elim_left succ_nth_stream_eq],
  suffices [] [":", expr «expr ≤ »(1, «expr ⁻¹»(ifp_n.fr))],
  { rw_mod_cast ["[", expr le_floor, "]"] [],
    assumption },
  suffices [] [":", expr «expr ≤ »(ifp_n.fr, 1)],
  { have [ident h] [":", expr «expr < »(0, ifp_n.fr)] [],
    from [expr lt_of_le_of_ne (nth_stream_fr_nonneg nth_stream_eq) stream_nth_fr_ne_zero.symm],
    apply [expr one_le_inv h this] },
  simp [] [] ["only"] ["[", expr le_of_lt (nth_stream_fr_lt_one nth_stream_eq), "]"] [] []
end

-- error in Algebra.ContinuedFractions.Computation.Approximations: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Shows that the `n + 1`th integer part `bₙ₊₁` of the stream is smaller or equal than the inverse of
the `n`th fractional part `frₙ` of the stream.
This result is straight-forward as `bₙ₊₁` is defined as the floor of `1 / frₙ`
-/
theorem succ_nth_stream_b_le_nth_stream_fr_inv
{ifp_n ifp_succ_n : int_fract_pair K}
(nth_stream_eq : «expr = »(int_fract_pair.stream v n, some ifp_n))
(succ_nth_stream_eq : «expr = »(int_fract_pair.stream v «expr + »(n, 1), some ifp_succ_n)) : «expr ≤ »((ifp_succ_n.b : K), «expr ⁻¹»(ifp_n.fr)) :=
begin
  suffices [] [":", expr «expr ≤ »((«expr⌊ ⌋»(«expr ⁻¹»(ifp_n.fr)) : K), «expr ⁻¹»(ifp_n.fr))],
  { cases [expr ifp_n] ["with", "_", ident ifp_n_fr],
    have [] [":", expr «expr ≠ »(ifp_n_fr, 0)] [],
    { intro [ident h],
      simpa [] [] [] ["[", expr h, ",", expr int_fract_pair.stream, ",", expr nth_stream_eq, "]"] [] ["using", expr succ_nth_stream_eq] },
    have [] [":", expr «expr = »(int_fract_pair.of «expr ⁻¹»(ifp_n_fr), ifp_succ_n)] [],
    { simpa [] [] [] ["[", expr this, ",", expr int_fract_pair.stream, ",", expr nth_stream_eq, ",", expr option.coe_def, "]"] [] ["using", expr succ_nth_stream_eq] },
    rwa ["<-", expr this] [] },
  exact [expr floor_le «expr ⁻¹»(ifp_n.fr)]
end

end IntFractPair

/-!
Next we translate above results about the stream of `int_fract_pair`s to the computed continued
fraction `generalized_continued_fraction.of`.
-/


/-- Shows that the integer parts of the continued fraction are at least one. -/
theorem of_one_le_nth_part_denom {b : K} (nth_part_denom_eq : (of v).partialDenominators.nth n = some b) : 1 ≤ b :=
  by 
    obtain ⟨gp_n, nth_s_eq, ⟨-⟩⟩ : ∃ gp_n, (of v).s.nth n = some gp_n ∧ gp_n.b = b 
    exact exists_s_b_of_part_denom nth_part_denom_eq 
    obtain ⟨ifp_n, succ_nth_stream_eq, ifp_n_b_eq_gp_n_b⟩ :
      ∃ ifp, int_fract_pair.stream v (n+1) = some ifp ∧ (ifp.b : K) = gp_n.b 
    exact int_fract_pair.exists_succ_nth_stream_of_gcf_of_nth_eq_some nth_s_eq 
    rw [←ifp_n_b_eq_gp_n_b]
    exactModCast int_fract_pair.one_le_succ_nth_stream_b succ_nth_stream_eq

-- error in Algebra.ContinuedFractions.Computation.Approximations: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Shows that the partial numerators `aᵢ` of the continued fraction are equal to one and the partial
denominators `bᵢ` correspond to integers.
-/
theorem of_part_num_eq_one_and_exists_int_part_denom_eq
{gp : generalized_continued_fraction.pair K}
(nth_s_eq : «expr = »((of v).s.nth n, some gp)) : «expr ∧ »(«expr = »(gp.a, 1), «expr∃ , »((z : exprℤ()), «expr = »(gp.b, (z : K)))) :=
begin
  obtain ["⟨", ident ifp, ",", ident stream_succ_nth_eq, ",", "-", "⟩", ":", expr «expr∃ , »((ifp), «expr ∧ »(«expr = »(int_fract_pair.stream v «expr + »(n, 1), some ifp), _))],
  from [expr int_fract_pair.exists_succ_nth_stream_of_gcf_of_nth_eq_some nth_s_eq],
  have [] [":", expr «expr = »(gp, ⟨1, ifp.b⟩)] [],
  by { have [] [":", expr «expr = »((of v).s.nth n, some ⟨1, ifp.b⟩)] [],
    from [expr nth_of_eq_some_of_succ_nth_int_fract_pair_stream stream_succ_nth_eq],
    have [] [":", expr «expr = »(some gp, some ⟨1, ifp.b⟩)] [],
    by rwa [expr nth_s_eq] ["at", ident this],
    injection [expr this] [] },
  finish [] []
end

-- error in Algebra.ContinuedFractions.Computation.Approximations: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Shows that the partial numerators `aᵢ` are equal to one. -/
theorem of_part_num_eq_one
{a : K}
(nth_part_num_eq : «expr = »((of v).partial_numerators.nth n, some a)) : «expr = »(a, 1) :=
begin
  obtain ["⟨", ident gp, ",", ident nth_s_eq, ",", ident gp_a_eq_a_n, "⟩", ":", expr «expr∃ , »((gp), «expr ∧ »(«expr = »((of v).s.nth n, some gp), «expr = »(gp.a, a)))],
  from [expr exists_s_a_of_part_num nth_part_num_eq],
  have [] [":", expr «expr = »(gp.a, 1)] [],
  from [expr (of_part_num_eq_one_and_exists_int_part_denom_eq nth_s_eq).left],
  rwa [expr gp_a_eq_a_n] ["at", ident this]
end

-- error in Algebra.ContinuedFractions.Computation.Approximations: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Shows that the partial denominators `bᵢ` correspond to an integer. -/
theorem exists_int_eq_of_part_denom
{b : K}
(nth_part_denom_eq : «expr = »((of v).partial_denominators.nth n, some b)) : «expr∃ , »((z : exprℤ()), «expr = »(b, (z : K))) :=
begin
  obtain ["⟨", ident gp, ",", ident nth_s_eq, ",", ident gp_b_eq_b_n, "⟩", ":", expr «expr∃ , »((gp), «expr ∧ »(«expr = »((of v).s.nth n, some gp), «expr = »(gp.b, b)))],
  from [expr exists_s_b_of_part_denom nth_part_denom_eq],
  have [] [":", expr «expr∃ , »((z : exprℤ()), «expr = »(gp.b, (z : K)))] [],
  from [expr (of_part_num_eq_one_and_exists_int_part_denom_eq nth_s_eq).right],
  rwa [expr gp_b_eq_b_n] ["at", ident this]
end

/-!
One of our next goals is to show that `bₙ * Bₙ ≤ Bₙ₊₁`. For this, we first show that the partial
denominators `Bₙ` are bounded from below by the fibonacci sequence `nat.fib`. This then implies that
`0 ≤ Bₙ` and hence `Bₙ₊₂ = bₙ₊₁ * Bₙ₊₁ + Bₙ ≥ bₙ₊₁ * Bₙ₊₁ + 0 = bₙ₊₁ * Bₙ₊₁`.
-/


open Nat

-- error in Algebra.ContinuedFractions.Computation.Approximations: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem fib_le_of_continuants_aux_b : «expr ∨ »(«expr ≤ »(n, 1), «expr¬ »((of v).terminated_at «expr - »(n, 2))) → «expr ≤ »((fib n : K), ((of v).continuants_aux n).b) :=
nat.strong_induction_on n (begin
   clear [ident n],
   assume [binders (n IH hyp)],
   rcases [expr n, "with", "_", "|", "_", "|", ident n],
   { simp [] [] [] ["[", expr fib_succ_succ, ",", expr continuants_aux, "]"] [] [] },
   { simp [] [] [] ["[", expr fib_succ_succ, ",", expr continuants_aux, "]"] [] [] },
   { let [ident g] [] [":=", expr of v],
     have [] [":", expr «expr¬ »(«expr ≤ »(«expr + »(n, 2), 1))] [],
     by linarith [] [] [],
     have [ident not_terminated_at_n] [":", expr «expr¬ »(g.terminated_at n)] [],
     from [expr or.resolve_left hyp this],
     obtain ["⟨", ident gp, ",", ident s_ppred_nth_eq, "⟩", ":", expr «expr∃ , »((gp), «expr = »(g.s.nth n, some gp))],
     from [expr option.ne_none_iff_exists'.mp not_terminated_at_n],
     set [] [ident pconts] [] [":="] [expr g.continuants_aux «expr + »(n, 1)] ["with", ident pconts_eq],
     set [] [ident ppconts] [] [":="] [expr g.continuants_aux n] ["with", ident ppconts_eq],
     suffices [] [":", expr «expr ≤ »(«expr + »((fib n : K), fib «expr + »(n, 1)), «expr + »(«expr * »(gp.a, ppconts.b), «expr * »(gp.b, pconts.b)))],
     by simpa [] [] [] ["[", expr fib_succ_succ, ",", expr add_comm, ",", expr continuants_aux_recurrence s_ppred_nth_eq ppconts_eq pconts_eq, "]"] [] [],
     suffices [] [":", expr «expr ≤ »(«expr + »((fib n : K), fib «expr + »(n, 1)), «expr + »(ppconts.b, «expr * »(gp.b, pconts.b)))],
     by simpa [] [] [] ["[", expr «expr $ »(of_part_num_eq_one, part_num_eq_s_a s_ppred_nth_eq), "]"] [] [],
     have [ident not_terminated_at_pred_n] [":", expr «expr¬ »(g.terminated_at «expr - »(n, 1))] [],
     from [expr mt «expr $ »(terminated_stable, nat.sub_le n 1) not_terminated_at_n],
     have [ident not_terminated_at_ppred_n] [":", expr «expr¬ »(terminated_at g «expr - »(n, 2))] [],
     from [expr mt (terminated_stable «expr - »(n, 1).pred_le) not_terminated_at_pred_n],
     have [] [":", expr «expr ≤ »((fib «expr + »(n, 1) : K), pconts.b)] [],
     from [expr IH _ «expr $ »(nat.lt.base, «expr + »(n, 1)) (or.inr not_terminated_at_pred_n)],
     have [ident ppred_nth_fib_le_ppconts_B] [":", expr «expr ≤ »((fib n : K), ppconts.b)] [],
     from [expr IH n «expr $ »(lt_trans (nat.lt.base n), «expr $ »(nat.lt.base, «expr + »(n, 1))) (or.inr not_terminated_at_ppred_n)],
     suffices [] [":", expr «expr ≤ »((fib «expr + »(n, 1) : K), «expr * »(gp.b, pconts.b))],
     solve_by_elim [] [] ["[", expr add_le_add ppred_nth_fib_le_ppconts_B, "]"] [],
     suffices [] [":", expr «expr ≤ »(«expr * »(1, (fib «expr + »(n, 1) : K)), «expr * »(gp.b, pconts.b))],
     by rwa ["[", expr one_mul, "]"] ["at", ident this],
     have [ident one_le_gp_b] [":", expr «expr ≤ »((1 : K), gp.b)] [],
     from [expr of_one_le_nth_part_denom (part_denom_eq_s_b s_ppred_nth_eq)],
     have [] [":", expr «expr ≤ »((0 : K), fib «expr + »(n, 1))] [],
     by exact_mod_cast [expr (fib «expr + »(n, 1)).zero_le],
     have [] [":", expr «expr ≤ »((0 : K), gp.b)] [],
     from [expr le_trans zero_le_one one_le_gp_b],
     mono [] [] [] [] }
 end)

-- error in Algebra.ContinuedFractions.Computation.Approximations: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Shows that the `n`th denominator is greater than or equal to the `n + 1`th fibonacci number,
that is `nat.fib (n + 1) ≤ Bₙ`. -/
theorem succ_nth_fib_le_of_nth_denom
(hyp : «expr ∨ »(«expr = »(n, 0), «expr¬ »((of v).terminated_at «expr - »(n, 1)))) : «expr ≤ »((fib «expr + »(n, 1) : K), (of v).denominators n) :=
begin
  rw ["[", expr denom_eq_conts_b, ",", expr nth_cont_eq_succ_nth_cont_aux, "]"] [],
  have [] [":", expr «expr ∨ »(«expr ≤ »(«expr + »(n, 1), 1), «expr¬ »((of v).terminated_at «expr - »(n, 1)))] [],
  by { cases [expr n] [],
    case [ident nat.zero, ":"] { exact [expr «expr $ »(or.inl, le_refl 1)] },
    case [ident nat.succ, ":"] { exact [expr or.inr (or.resolve_left hyp n.succ_ne_zero)] } },
  exact [expr fib_le_of_continuants_aux_b this]
end

/-! As a simple consequence, we can now derive that all denominators are nonnegative. -/


-- error in Algebra.ContinuedFractions.Computation.Approximations: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem zero_le_of_continuants_aux_b : «expr ≤ »(0, ((of v).continuants_aux n).b) :=
begin
  let [ident g] [] [":=", expr of v],
  induction [expr n] [] ["with", ident n, ident IH] [],
  case [ident nat.zero, ":"] { refl },
  case [ident nat.succ, ":"] { cases [expr «expr $ »(decidable.em, g.terminated_at «expr - »(n, 1))] ["with", ident terminated, ident not_terminated],
    { cases [expr n] [],
      { simp [] [] [] ["[", expr zero_le_one, "]"] [] [] },
      { have [] [":", expr «expr = »(g.continuants_aux «expr + »(n, 2), g.continuants_aux «expr + »(n, 1))] [],
        from [expr continuants_aux_stable_step_of_terminated terminated],
        simp [] [] ["only"] ["[", expr this, ",", expr IH, "]"] [] [] } },
    { calc
        «expr ≤ »((0 : K), fib «expr + »(n, 1)) : by exact_mod_cast [expr «expr + »(n, 1).fib.zero_le]
        «expr ≤ »(..., ((of v).continuants_aux «expr + »(n, 1)).b) : fib_le_of_continuants_aux_b (or.inr not_terminated) } }
end

/-- Shows that all denominators are nonnegative. -/
theorem zero_le_of_denom : 0 ≤ (of v).denominators n :=
  by 
    rw [denom_eq_conts_b, nth_cont_eq_succ_nth_cont_aux]
    exact zero_le_of_continuants_aux_b

-- error in Algebra.ContinuedFractions.Computation.Approximations: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Meta.solveByElim'
theorem le_of_succ_succ_nth_continuants_aux_b
{b : K}
(nth_part_denom_eq : «expr = »((of v).partial_denominators.nth n, some b)) : «expr ≤ »(«expr * »(b, «expr $ »((of v).continuants_aux, «expr + »(n, 1)).b), «expr $ »((of v).continuants_aux, «expr + »(n, 2)).b) :=
begin
  set [] [ident g] [] [":="] [expr of v] ["with", ident g_eq],
  obtain ["⟨", ident gp_n, ",", ident nth_s_eq, ",", ident gpnb_eq_b, "⟩", ":", expr «expr∃ , »((gp_n), «expr ∧ »(«expr = »(g.s.nth n, some gp_n), «expr = »(gp_n.b, b)))],
  from [expr exists_s_b_of_part_denom nth_part_denom_eq],
  let [ident conts] [] [":=", expr g.continuants_aux «expr + »(n, 2)],
  set [] [ident pconts] [] [":="] [expr g.continuants_aux «expr + »(n, 1)] ["with", ident pconts_eq],
  set [] [ident ppconts] [] [":="] [expr g.continuants_aux n] ["with", ident ppconts_eq],
  suffices [] [":", expr «expr ≤ »(«expr * »(gp_n.b, pconts.b), «expr + »(ppconts.b, «expr * »(gp_n.b, pconts.b)))],
  by { have [] [":", expr «expr = »(gp_n.a, 1)] [],
    from [expr of_part_num_eq_one (part_num_eq_s_a nth_s_eq)],
    finish ["[", expr generalized_continued_fraction.continuants_aux_recurrence nth_s_eq ppconts_eq pconts_eq, "]"] [] },
  have [] [":", expr «expr ≤ »(0, ppconts.b)] [],
  from [expr zero_le_of_continuants_aux_b],
  solve_by_elim [] [] ["[", expr le_add_of_nonneg_of_le, ",", expr le_refl, "]"] []
end

/-- Shows that `bₙ * Bₙ ≤ Bₙ₊₁`, where `bₙ` is the `n`th partial denominator and `Bₙ₊₁` and `Bₙ` are
the `n + 1`th and `n`th denominator of the continued fraction. -/
theorem le_of_succ_nth_denom {b : K} (nth_part_denom_eq : (of v).partialDenominators.nth n = some b) :
  (b*(of v).denominators n) ≤ (of v).denominators (n+1) :=
  by 
    rw [denom_eq_conts_b, nth_cont_eq_succ_nth_cont_aux]
    exact le_of_succ_succ_nth_continuants_aux_b nth_part_denom_eq

-- error in Algebra.ContinuedFractions.Computation.Approximations: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Shows that the sequence of denominators is monotone, that is `Bₙ ≤ Bₙ₊₁`. -/
theorem of_denom_mono : «expr ≤ »((of v).denominators n, (of v).denominators «expr + »(n, 1)) :=
begin
  let [ident g] [] [":=", expr of v],
  cases [expr «expr $ »(decidable.em, g.partial_denominators.terminated_at n)] ["with", ident terminated, ident not_terminated],
  { have [] [":", expr «expr = »(g.partial_denominators.nth n, none)] [],
    by rwa [expr seq.terminated_at] ["at", ident terminated],
    have [] [":", expr g.terminated_at n] [],
    from [expr terminated_at_iff_part_denom_none.elim_right (by rwa [expr seq.terminated_at] ["at", ident terminated])],
    have [] [":", expr «expr = »(g.denominators «expr + »(n, 1), g.denominators n)] [],
    from [expr denominators_stable_of_terminated n.le_succ this],
    rw [expr this] [] },
  { obtain ["⟨", ident b, ",", ident nth_part_denom_eq, "⟩", ":", expr «expr∃ , »((b), «expr = »(g.partial_denominators.nth n, some b))],
    from [expr option.ne_none_iff_exists'.mp not_terminated],
    have [] [":", expr «expr ≤ »(1, b)] [],
    from [expr of_one_le_nth_part_denom nth_part_denom_eq],
    calc
      «expr ≤ »(g.denominators n, «expr * »(b, g.denominators n)) : by simpa [] [] [] [] [] ["using", expr mul_le_mul_of_nonneg_right this zero_le_of_denom]
      «expr ≤ »(..., g.denominators «expr + »(n, 1)) : le_of_succ_nth_denom nth_part_denom_eq }
end

section Determinant

/-!
### Determinant Formula

Next we prove the so-called *determinant formula* for `generalized_continued_fraction.of`:
`Aₙ * Bₙ₊₁ - Bₙ * Aₙ₊₁ = (-1)^(n + 1)`.
-/


-- error in Algebra.ContinuedFractions.Computation.Approximations: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem determinant_aux
(hyp : «expr ∨ »(«expr = »(n, 0), «expr¬ »((of v).terminated_at «expr - »(n, 1)))) : «expr = »(«expr - »(«expr * »(((of v).continuants_aux n).a, ((of v).continuants_aux «expr + »(n, 1)).b), «expr * »(((of v).continuants_aux n).b, ((of v).continuants_aux «expr + »(n, 1)).a)), «expr ^ »(«expr- »(1), n)) :=
begin
  induction [expr n] [] ["with", ident n, ident IH] [],
  case [ident nat.zero] { simp [] [] [] ["[", expr continuants_aux, "]"] [] [] },
  case [ident nat.succ] { let [ident g] [] [":=", expr of v],
    let [ident conts] [] [":=", expr continuants_aux g «expr + »(n, 2)],
    set [] [ident pred_conts] [] [":="] [expr continuants_aux g «expr + »(n, 1)] ["with", ident pred_conts_eq],
    set [] [ident ppred_conts] [] [":="] [expr continuants_aux g n] ["with", ident ppred_conts_eq],
    let [ident pA] [] [":=", expr pred_conts.a],
    let [ident pB] [] [":=", expr pred_conts.b],
    let [ident ppA] [] [":=", expr ppred_conts.a],
    let [ident ppB] [] [":=", expr ppred_conts.b],
    change [expr «expr = »(«expr - »(«expr * »(pA, conts.b), «expr * »(pB, conts.a)), «expr ^ »(«expr- »(1), «expr + »(n, 1)))] [] [],
    have [ident not_terminated_at_n] [":", expr «expr¬ »(terminated_at g n)] [],
    from [expr or.resolve_left hyp n.succ_ne_zero],
    obtain ["⟨", ident gp, ",", ident s_nth_eq, "⟩", ":", expr «expr∃ , »((gp), «expr = »(g.s.nth n, some gp))],
    from [expr option.ne_none_iff_exists'.elim_left not_terminated_at_n],
    suffices [] [":", expr «expr = »(«expr - »(«expr * »(pA, «expr + »(ppB, «expr * »(gp.b, pB))), «expr * »(pB, «expr + »(ppA, «expr * »(gp.b, pA)))), «expr ^ »(«expr- »(1), «expr + »(n, 1)))],
    by { simp [] [] ["only"] ["[", expr conts, ",", expr continuants_aux_recurrence s_nth_eq ppred_conts_eq pred_conts_eq, "]"] [] [],
      have [ident gp_a_eq_one] [":", expr «expr = »(gp.a, 1)] [],
      from [expr of_part_num_eq_one (part_num_eq_s_a s_nth_eq)],
      rw ["[", expr gp_a_eq_one, ",", expr this.symm, "]"] [],
      ring [] },
    suffices [] [":", expr «expr = »(«expr - »(«expr * »(pA, ppB), «expr * »(pB, ppA)), «expr ^ »(«expr- »(1), «expr + »(n, 1)))],
    calc
      «expr = »(«expr - »(«expr * »(pA, «expr + »(ppB, «expr * »(gp.b, pB))), «expr * »(pB, «expr + »(ppA, «expr * »(gp.b, pA)))), «expr - »(«expr - »(«expr + »(«expr * »(pA, ppB), «expr * »(«expr * »(pA, gp.b), pB)), «expr * »(pB, ppA)), «expr * »(«expr * »(pB, gp.b), pA))) : by ring []
      «expr = »(..., «expr - »(«expr * »(pA, ppB), «expr * »(pB, ppA))) : by ring []
      «expr = »(..., «expr ^ »(«expr- »(1), «expr + »(n, 1))) : by assumption,
    suffices [] [":", expr «expr = »(«expr - »(«expr * »(ppA, pB), «expr * »(ppB, pA)), «expr ^ »(«expr- »(1), n))],
    by { have [ident pow_succ_n] [":", expr «expr = »(«expr ^ »((«expr- »(1) : K), «expr + »(n, 1)), «expr * »(«expr- »(1), «expr ^ »(«expr- »(1), n)))] [],
      from [expr pow_succ «expr- »(1) n],
      rw ["[", expr pow_succ_n, ",", "<-", expr this, "]"] [],
      ring [] },
    exact [expr «expr $ »(IH, «expr $ »(or.inr, mt «expr $ »(terminated_stable, n.sub_le 1) not_terminated_at_n))] }
end

/-- The determinant formula `Aₙ * Bₙ₊₁ - Bₙ * Aₙ₊₁ = (-1)^(n + 1)` -/
theorem determinant (not_terminated_at_n : ¬(of v).TerminatedAt n) :
  (((of v).numerators n*(of v).denominators (n+1)) - (of v).denominators n*(of v).numerators (n+1)) = -1 ^ n+1 :=
  determinant_aux$ Or.inr$ not_terminated_at_n

end Determinant

section ErrorTerm

/-!
### Approximation of Error Term

Next we derive some approximations for the error term when computing a continued fraction up a given
position, i.e. bounds for the term `|v - (generalized_continued_fraction.of v).convergents n|`.
-/


-- error in Algebra.ContinuedFractions.Computation.Approximations: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- This lemma follows from the finite correctness proof, the determinant equality, and
by simplifying the difference. -/
theorem sub_convergents_eq
{ifp : int_fract_pair K}
(stream_nth_eq : «expr = »(int_fract_pair.stream v n, some ifp)) : let g := of v in
let B := (g.continuants_aux «expr + »(n, 1)).b in
let pB := (g.continuants_aux n).b in
«expr = »(«expr - »(v, g.convergents n), if «expr = »(ifp.fr, 0) then 0 else «expr / »(«expr ^ »(«expr- »(1), n), «expr * »(B, «expr + »(«expr * »(«expr ⁻¹»(ifp.fr), B), pB)))) :=
begin
  let [ident g] [] [":=", expr of v],
  let [ident conts] [] [":=", expr g.continuants_aux «expr + »(n, 1)],
  let [ident pred_conts] [] [":=", expr g.continuants_aux n],
  have [ident g_finite_correctness] [":", expr «expr = »(v, generalized_continued_fraction.comp_exact_value pred_conts conts ifp.fr)] [],
  from [expr comp_exact_value_correctness_of_stream_eq_some stream_nth_eq],
  cases [expr decidable.em «expr = »(ifp.fr, 0)] ["with", ident ifp_fr_eq_zero, ident ifp_fr_ne_zero],
  { suffices [] [":", expr «expr = »(«expr - »(v, g.convergents n), 0)],
    by simpa [] [] [] ["[", expr ifp_fr_eq_zero, "]"] [] [],
    replace [ident g_finite_correctness] [":", expr «expr = »(v, g.convergents n)] [],
    by simpa [] [] [] ["[", expr generalized_continued_fraction.comp_exact_value, ",", expr ifp_fr_eq_zero, "]"] [] ["using", expr g_finite_correctness],
    exact [expr sub_eq_zero.elim_right g_finite_correctness] },
  { let [ident A] [] [":=", expr conts.a],
    let [ident B] [] [":=", expr conts.b],
    let [ident pA] [] [":=", expr pred_conts.a],
    let [ident pB] [] [":=", expr pred_conts.b],
    suffices [] [":", expr «expr = »(«expr - »(v, «expr / »(A, B)), «expr / »(«expr ^ »(«expr- »(1), n), «expr * »(B, «expr + »(«expr * »(«expr ⁻¹»(ifp.fr), B), pB))))],
    by simpa [] [] [] ["[", expr ifp_fr_ne_zero, "]"] [] [],
    replace [ident g_finite_correctness] [":", expr «expr = »(v, «expr / »(«expr + »(pA, «expr * »(«expr ⁻¹»(ifp.fr), A)), «expr + »(pB, «expr * »(«expr ⁻¹»(ifp.fr), B))))] [],
    by simpa [] [] [] ["[", expr generalized_continued_fraction.comp_exact_value, ",", expr ifp_fr_ne_zero, ",", expr next_continuants, ",", expr next_numerator, ",", expr next_denominator, ",", expr add_comm, "]"] [] ["using", expr g_finite_correctness],
    suffices [] [":", expr «expr = »(«expr - »(«expr / »(«expr + »(pA, «expr * »(«expr ⁻¹»(ifp.fr), A)), «expr + »(pB, «expr * »(«expr ⁻¹»(ifp.fr), B))), «expr / »(A, B)), «expr / »(«expr ^ »(«expr- »(1), n), «expr * »(B, «expr + »(«expr * »(«expr ⁻¹»(ifp.fr), B), pB))))],
    by rwa [expr g_finite_correctness] [],
    have [ident n_eq_zero_or_not_terminated_at_pred_n] [":", expr «expr ∨ »(«expr = »(n, 0), «expr¬ »(g.terminated_at «expr - »(n, 1)))] [],
    by { cases [expr n] ["with", ident n'],
      { simp [] [] [] [] [] [] },
      { have [] [":", expr «expr ≠ »(int_fract_pair.stream v «expr + »(n', 1), none)] [],
        by simp [] [] [] ["[", expr stream_nth_eq, "]"] [] [],
        have [] [":", expr «expr¬ »(g.terminated_at n')] [],
        from [expr (not_iff_not_of_iff of_terminated_at_n_iff_succ_nth_int_fract_pair_stream_eq_none).elim_right this],
        exact [expr or.inr this] } },
    have [ident determinant_eq] [":", expr «expr = »(«expr - »(«expr * »(pA, B), «expr * »(pB, A)), «expr ^ »(«expr- »(1), n))] [],
    from [expr determinant_aux n_eq_zero_or_not_terminated_at_pred_n],
    have [ident pB_ineq] [":", expr «expr ≤ »((fib n : K), pB)] [],
    by { have [] [":", expr «expr ∨ »(«expr ≤ »(n, 1), «expr¬ »(g.terminated_at «expr - »(n, 2)))] [],
      by { cases [expr n_eq_zero_or_not_terminated_at_pred_n] ["with", ident n_eq_zero, ident not_terminated_at_pred_n],
        { simp [] [] [] ["[", expr n_eq_zero, "]"] [] [] },
        { exact [expr «expr $ »(or.inr, mt (terminated_stable «expr - »(n, 1).pred_le) not_terminated_at_pred_n)] } },
      exact [expr fib_le_of_continuants_aux_b this] },
    have [ident B_ineq] [":", expr «expr ≤ »((fib «expr + »(n, 1) : K), B)] [],
    by { have [] [":", expr «expr ∨ »(«expr ≤ »(«expr + »(n, 1), 1), «expr¬ »(g.terminated_at «expr - »(«expr + »(n, 1), 2)))] [],
      by { cases [expr n_eq_zero_or_not_terminated_at_pred_n] ["with", ident n_eq_zero, ident not_terminated_at_pred_n],
        { simp [] [] [] ["[", expr n_eq_zero, ",", expr le_refl, "]"] [] [] },
        { exact [expr or.inr not_terminated_at_pred_n] } },
      exact [expr fib_le_of_continuants_aux_b this] },
    have [ident zero_lt_B] [":", expr «expr < »(0, B)] [],
    { have [] [":", expr «expr ≤ »(1, B)] [],
      from [expr le_trans (by exact_mod_cast [expr fib_pos (lt_of_le_of_ne n.succ.zero_le n.succ_ne_zero.symm)]) B_ineq],
      exact [expr lt_of_lt_of_le zero_lt_one this] },
    have [ident zero_ne_B] [":", expr «expr ≠ »(0, B)] [],
    from [expr ne_of_lt zero_lt_B],
    have [] [":", expr «expr ≠ »(0, «expr + »(pB, «expr * »(«expr ⁻¹»(ifp.fr), B)))] [],
    by { have [] [":", expr «expr ≤ »((0 : K), fib n)] [],
      by exact_mod_cast [expr (fib n).zero_le],
      have [ident zero_le_pB] [":", expr «expr ≤ »(0, pB)] [],
      from [expr le_trans this pB_ineq],
      have [] [":", expr «expr < »(0, «expr ⁻¹»(ifp.fr))] [],
      by { suffices [] [":", expr «expr < »(0, ifp.fr)],
        by rwa [expr inv_pos] [],
        have [] [":", expr «expr ≤ »(0, ifp.fr)] [],
        from [expr int_fract_pair.nth_stream_fr_nonneg stream_nth_eq],
        change [expr «expr ≠ »(ifp.fr, 0)] [] ["at", ident ifp_fr_ne_zero],
        exact [expr lt_of_le_of_ne this ifp_fr_ne_zero.symm] },
      have [] [":", expr «expr < »(0, «expr * »(«expr ⁻¹»(ifp.fr), B))] [],
      from [expr mul_pos this zero_lt_B],
      have [] [":", expr «expr < »(0, «expr + »(pB, «expr * »(«expr ⁻¹»(ifp.fr), B)))] [],
      from [expr add_pos_of_nonneg_of_pos zero_le_pB this],
      exact [expr ne_of_lt this] },
    calc
      «expr = »(«expr - »(«expr / »(«expr + »(pA, «expr * »(«expr ⁻¹»(ifp.fr), A)), «expr + »(pB, «expr * »(«expr ⁻¹»(ifp.fr), B))), «expr / »(A, B)), «expr / »(«expr - »(«expr * »(«expr + »(pA, «expr * »(«expr ⁻¹»(ifp.fr), A)), B), «expr * »(«expr + »(pB, «expr * »(«expr ⁻¹»(ifp.fr), B)), A)), «expr * »(«expr + »(pB, «expr * »(«expr ⁻¹»(ifp.fr), B)), B))) : by rw [expr div_sub_div _ _ this.symm zero_ne_B.symm] []
      «expr = »(..., «expr / »(«expr - »(«expr + »(«expr * »(pA, B), «expr * »(«expr * »(«expr ⁻¹»(ifp.fr), A), B)), «expr + »(«expr * »(pB, A), «expr * »(«expr * »(«expr ⁻¹»(ifp.fr), B), A))), _)) : by repeat { rw ["[", expr add_mul, "]"] [] }
      «expr = »(..., «expr / »(«expr - »(«expr * »(pA, B), «expr * »(pB, A)), «expr * »(«expr + »(pB, «expr * »(«expr ⁻¹»(ifp.fr), B)), B))) : by ring []
      «expr = »(..., «expr / »(«expr ^ »(«expr- »(1), n), «expr * »(«expr + »(pB, «expr * »(«expr ⁻¹»(ifp.fr), B)), B))) : by rw [expr determinant_eq] []
      «expr = »(..., «expr / »(«expr ^ »(«expr- »(1), n), «expr * »(B, «expr + »(«expr * »(«expr ⁻¹»(ifp.fr), B), pB)))) : by ac_refl }
end

-- error in Algebra.ContinuedFractions.Computation.Approximations: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Shows that `|v - Aₙ / Bₙ| ≤ 1 / (Bₙ * Bₙ₊₁)` -/
theorem abs_sub_convergents_le
(not_terminated_at_n : «expr¬ »((of v).terminated_at n)) : «expr ≤ »(«expr| |»(«expr - »(v, (of v).convergents n)), «expr / »(1, «expr * »((of v).denominators n, «expr $ »((of v).denominators, «expr + »(n, 1))))) :=
begin
  let [ident g] [] [":=", expr of v],
  let [ident nextConts] [] [":=", expr g.continuants_aux «expr + »(n, 2)],
  set [] [ident conts] [] [":="] [expr continuants_aux g «expr + »(n, 1)] ["with", ident conts_eq],
  set [] [ident pred_conts] [] [":="] [expr continuants_aux g n] ["with", ident pred_conts_eq],
  change [expr «expr ≤ »(«expr| |»(«expr - »(v, convergents g n)), «expr / »(1, «expr * »(conts.b, nextConts.b)))] [] [],
  obtain ["⟨", ident gp, ",", ident s_nth_eq, "⟩", ":", expr «expr∃ , »((gp), «expr = »(g.s.nth n, some gp))],
  from [expr option.ne_none_iff_exists'.elim_left not_terminated_at_n],
  have [ident gp_a_eq_one] [":", expr «expr = »(gp.a, 1)] [],
  from [expr of_part_num_eq_one (part_num_eq_s_a s_nth_eq)],
  have [ident nextConts_b_eq] [":", expr «expr = »(nextConts.b, «expr + »(pred_conts.b, «expr * »(gp.b, conts.b)))] [],
  by simp [] [] [] ["[", expr nextConts, ",", expr continuants_aux_recurrence s_nth_eq pred_conts_eq conts_eq, ",", expr gp_a_eq_one, ",", expr pred_conts_eq.symm, ",", expr conts_eq.symm, ",", expr add_comm, "]"] [] [],
  let [ident denom] [] [":=", expr «expr * »(conts.b, «expr + »(pred_conts.b, «expr * »(gp.b, conts.b)))],
  suffices [] [":", expr «expr ≤ »(«expr| |»(«expr - »(v, g.convergents n)), «expr / »(1, denom))],
  by { rw ["[", expr nextConts_b_eq, "]"] [],
    congr' [1] [] },
  obtain ["⟨", ident ifp_succ_n, ",", ident succ_nth_stream_eq, ",", ident ifp_succ_n_b_eq_gp_b, "⟩", ":", expr «expr∃ , »((ifp_succ_n), «expr ∧ »(«expr = »(int_fract_pair.stream v «expr + »(n, 1), some ifp_succ_n), «expr = »((ifp_succ_n.b : K), gp.b)))],
  from [expr int_fract_pair.exists_succ_nth_stream_of_gcf_of_nth_eq_some s_nth_eq],
  obtain ["⟨", ident ifp_n, ",", ident stream_nth_eq, ",", ident stream_nth_fr_ne_zero, ",", ident if_of_eq_ifp_succ_n, "⟩", ":", expr «expr∃ , »((ifp_n), «expr ∧ »(«expr = »(int_fract_pair.stream v n, some ifp_n), «expr ∧ »(«expr ≠ »(ifp_n.fr, 0), «expr = »(int_fract_pair.of «expr ⁻¹»(ifp_n.fr), ifp_succ_n))))],
  from [expr int_fract_pair.succ_nth_stream_eq_some_iff.elim_left succ_nth_stream_eq],
  let [ident denom'] [] [":=", expr «expr * »(conts.b, «expr + »(pred_conts.b, «expr * »(«expr ⁻¹»(ifp_n.fr), conts.b)))],
  suffices [] [":", expr «expr ≤ »(«expr| |»(«expr / »(«expr ^ »(«expr- »(1), n), denom')), «expr / »(1, denom))],
  by { have [] [":", expr «expr = »(«expr - »(v, g.convergents n), «expr / »(«expr ^ »(«expr- »(1), n), denom'))] [],
    by { have [ident tmp] [] [],
      from [expr sub_convergents_eq stream_nth_eq],
      delta [] ["at", ident tmp],
      simp [] [] ["only"] ["[", expr stream_nth_fr_ne_zero, ",", expr conts_eq.symm, ",", expr pred_conts_eq.symm, "]"] [] ["at", ident tmp],
      rw [expr tmp] [],
      simp [] [] ["only"] ["[", expr denom', "]"] [] [],
      ring_nf [] [] [],
      ac_refl },
    rwa [expr this] [] },
  have [ident nextConts_b_ineq] [":", expr «expr ≤ »((fib «expr + »(n, 2) : K), «expr + »(pred_conts.b, «expr * »(gp.b, conts.b)))] [],
  by { have [] [":", expr «expr ≤ »((fib «expr + »(n, 2) : K), nextConts.b)] [],
    from [expr fib_le_of_continuants_aux_b (or.inr not_terminated_at_n)],
    rwa ["[", expr nextConts_b_eq, "]"] ["at", ident this] },
  have [ident conts_b_ineq] [":", expr «expr ≤ »((fib «expr + »(n, 1) : K), conts.b)] [],
  by { have [] [":", expr «expr¬ »(g.terminated_at «expr - »(n, 1))] [],
    from [expr mt (terminated_stable n.pred_le) not_terminated_at_n],
    exact [expr «expr $ »(fib_le_of_continuants_aux_b, or.inr this)] },
  have [ident zero_lt_conts_b] [":", expr «expr < »(0, conts.b)] [],
  by { have [] [":", expr «expr < »((0 : K), fib «expr + »(n, 1))] [],
    by exact_mod_cast [expr fib_pos (lt_of_le_of_ne n.succ.zero_le n.succ_ne_zero.symm)],
    exact [expr lt_of_lt_of_le this conts_b_ineq] },
  suffices [] [":", expr «expr ≤ »(«expr / »(1, denom'), «expr / »(1, denom))],
  by { have [] [":", expr «expr = »(«expr| |»(«expr / »(«expr ^ »(«expr- »(1), n), denom')), «expr / »(1, denom'))] [],
    by { suffices [] [":", expr «expr = »(«expr / »(1, «expr| |»(denom')), «expr / »(1, denom'))],
      by rwa ["[", expr abs_div, ",", expr abs_neg_one_pow n, "]"] [],
      have [] [":", expr «expr < »(0, denom')] [],
      by { have [] [":", expr «expr ≤ »(0, pred_conts.b)] [],
        by { have [] [":", expr «expr ≤ »((fib n : K), pred_conts.b)] [],
          by { have [] [":", expr «expr¬ »(g.terminated_at «expr - »(n, 2))] [],
            from [expr mt (terminated_stable (n.sub_le 2)) not_terminated_at_n],
            exact [expr «expr $ »(fib_le_of_continuants_aux_b, or.inr this)] },
          exact [expr le_trans (by exact_mod_cast [expr (fib n).zero_le]) this] },
        have [] [":", expr «expr < »(0, «expr ⁻¹»(ifp_n.fr))] [],
        by { have [ident zero_le_ifp_n_fract] [":", expr «expr ≤ »(0, ifp_n.fr)] [],
          from [expr int_fract_pair.nth_stream_fr_nonneg stream_nth_eq],
          exact [expr inv_pos.elim_right (lt_of_le_of_ne zero_le_ifp_n_fract stream_nth_fr_ne_zero.symm)] },
        any_goals { repeat { apply [expr mul_pos] <|> apply [expr add_pos_of_nonneg_of_pos] } }; assumption },
      rwa [expr abs_of_pos this] [] },
    rwa [expr this] [] },
  suffices [] [":", expr «expr ∧ »(«expr < »(0, denom), «expr ≤ »(denom, denom'))],
  from [expr div_le_div_of_le_left zero_le_one this.left this.right],
  split,
  { have [] [":", expr «expr < »(0, «expr + »(pred_conts.b, «expr * »(gp.b, conts.b)))] [],
    from [expr lt_of_lt_of_le (by exact_mod_cast [expr fib_pos (lt_of_le_of_ne n.succ.succ.zero_le n.succ.succ_ne_zero.symm)]) nextConts_b_ineq],
    solve_by_elim [] [] ["[", expr mul_pos, "]"] [] },
  { suffices [] [":", expr «expr ≤ »(«expr * »(gp.b, conts.b), «expr * »(«expr ⁻¹»(ifp_n.fr), conts.b))],
    from [expr «expr $ »((mul_le_mul_left zero_lt_conts_b).elim_right, (add_le_add_iff_left pred_conts.b).elim_right this)],
    suffices [] [":", expr «expr ≤ »(«expr * »((ifp_succ_n.b : K), conts.b), «expr * »(«expr ⁻¹»(ifp_n.fr), conts.b))],
    by rwa ["[", "<-", expr ifp_succ_n_b_eq_gp_b, "]"] [],
    have [] [":", expr «expr ≤ »((ifp_succ_n.b : K), «expr ⁻¹»(ifp_n.fr))] [],
    from [expr int_fract_pair.succ_nth_stream_b_le_nth_stream_fr_inv stream_nth_eq succ_nth_stream_eq],
    have [] [":", expr «expr ≤ »(0, conts.b)] [],
    from [expr le_of_lt zero_lt_conts_b],
    mono [] [] [] [] }
end

-- error in Algebra.ContinuedFractions.Computation.Approximations: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Shows that `|v - Aₙ / Bₙ| ≤ 1 / (bₙ * Bₙ * Bₙ)`. This bound is worse than the one shown in
`gcf.abs_sub_convergents_le`, but sometimes it is easier to apply and sufficient for one's use case.
 -/
theorem abs_sub_convergents_le'
{b : K}
(nth_part_denom_eq : «expr = »((of v).partial_denominators.nth n, some b)) : «expr ≤ »(«expr| |»(«expr - »(v, (of v).convergents n)), «expr / »(1, «expr * »(«expr * »(b, (of v).denominators n), (of v).denominators n))) :=
begin
  let [ident g] [] [":=", expr of v],
  let [ident B] [] [":=", expr g.denominators n],
  let [ident nB] [] [":=", expr g.denominators «expr + »(n, 1)],
  have [ident not_terminated_at_n] [":", expr «expr¬ »(g.terminated_at n)] [],
  by { have [] [":", expr «expr ≠ »(g.partial_denominators.nth n, none)] [],
    by simp [] [] [] ["[", expr nth_part_denom_eq, "]"] [] [],
    exact [expr (not_iff_not_of_iff terminated_at_iff_part_denom_none).elim_right this] },
  suffices [] [":", expr «expr ≤ »(«expr / »(1, «expr * »(B, nB)), «expr / »((1 : K), «expr * »(«expr * »(b, B), B)))],
  by { have [] [":", expr «expr ≤ »(«expr| |»(«expr - »(v, g.convergents n)), «expr / »(1, «expr * »(B, nB)))] [],
    from [expr abs_sub_convergents_le not_terminated_at_n],
    transitivity []; assumption },
  have [ident zero_lt_B] [":", expr «expr < »(0, B)] [],
  by { have [] [":", expr «expr ≤ »((fib «expr + »(n, 1) : K), B)] [],
    from [expr succ_nth_fib_le_of_nth_denom «expr $ »(or.inr, mt (terminated_stable n.pred_le) not_terminated_at_n)],
    exact [expr lt_of_lt_of_le (by exact_mod_cast [expr fib_pos (lt_of_le_of_ne n.succ.zero_le n.succ_ne_zero.symm)]) this] },
  have [ident denoms_ineq] [":", expr «expr ≤ »(«expr * »(«expr * »(b, B), B), «expr * »(B, nB))] [],
  by { have [] [":", expr «expr ≤ »(«expr * »(b, B), nB)] [],
    from [expr le_of_succ_nth_denom nth_part_denom_eq],
    rwa ["[", expr mul_comm B nB, ",", expr mul_le_mul_right zero_lt_B, "]"] [] },
  have [] [":", expr «expr < »((0 : K), «expr * »(«expr * »(b, B), B))] [],
  by { have [] [":", expr «expr < »(0, b)] [],
    from [expr lt_of_lt_of_le zero_lt_one (of_one_le_nth_part_denom nth_part_denom_eq)],
    any_goals { repeat { apply [expr mul_pos] } }; assumption },
  exact [expr div_le_div_of_le_left zero_le_one this denoms_ineq]
end

end ErrorTerm

end GeneralizedContinuedFraction

