import Mathbin.Algebra.ContinuedFractions.Computation.Translations 
import Mathbin.Algebra.ContinuedFractions.TerminatedStable 
import Mathbin.Algebra.ContinuedFractions.ContinuantsRecurrence 
import Mathbin.Order.Filter.AtTopBot 
import Mathbin.Tactic.FieldSimp

/-!
# Correctness of Terminating Continued Fraction Computations (`generalized_continued_fraction.of`)

## Summary

We show the correctness of the
algorithm computing continued fractions (`generalized_continued_fraction.of`) in case of termination
in the following sense:

At every step `n : ℕ`, we can obtain the value `v` by adding a specific residual term to the last
denominator of the fraction described by `(generalized_continued_fraction.of v).convergents' n`.
The residual term will be zero exactly when the continued fraction terminated; otherwise, the
residual term will be given by the fractional part stored in
`generalized_continued_fraction.int_fract_pair.stream v n`.

For an example, refer to
`generalized_continued_fraction.comp_exact_value_correctness_of_stream_eq_some` and for more
information about the computation process, refer to `algebra.continued_fraction.computation.basic`.

## Main definitions

- `generalized_continued_fraction.comp_exact_value` can be used to compute the exact value
  approximated by the continued fraction `generalized_continued_fraction.of v` by adding a residual
  term as described in the summary.

## Main Theorems

- `generalized_continued_fraction.comp_exact_value_correctness_of_stream_eq_some` shows that
  `generalized_continued_fraction.comp_exact_value` indeed returns the value `v` when given the
  convergent and fractional part as described in the summary.
- `generalized_continued_fraction.of_correctness_of_terminated_at` shows the equality
  `v = (generalized_continued_fraction.of v).convergents n` if `generalized_continued_fraction.of v`
  terminated at position `n`.
-/


namespace GeneralizedContinuedFraction

open generalized_continued_fraction(of)

variable {K : Type _} [LinearOrderedField K] {v : K} {n : ℕ}

/--
Given two continuants `pconts` and `conts` and a value `fr`, this function returns
- `conts.a / conts.b` if `fr = 0`
- `exact_conts.a / exact_conts.b` where `exact_conts = next_continuants 1 fr⁻¹ pconts conts`
  otherwise.

This function can be used to compute the exact value approxmated by a continued fraction
`generalized_continued_fraction.of v` as described in lemma
`comp_exact_value_correctness_of_stream_eq_some`.
-/
protected def comp_exact_value (pconts conts : pair K) (fr : K) : K :=
  if fr = 0 then conts.a / conts.b else
    let exact_conts := next_continuants 1 (fr⁻¹) pconts conts 
    exact_conts.a / exact_conts.b

variable [FloorRing K]

/-- Just a computational lemma we need for the next main proof. -/
protected theorem comp_exact_value_correctness_of_stream_eq_some_aux_comp {a : K} (b c : K)
  (fract_a_ne_zero : Int.fract a ≠ 0) : (((((⌊a⌋ : K)*b)+c) / Int.fract a)+b) = ((b*a)+c) / Int.fract a :=
  by 
    fieldSimp [fract_a_ne_zero]
    rw [Int.fract]
    ring

open generalized_continued_fraction(compExactValue comp_exact_value_correctness_of_stream_eq_some_aux_comp)

-- error in Algebra.ContinuedFractions.Computation.CorrectnessTerminating: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Shows the correctness of `comp_exact_value` in case the continued fraction
`generalized_continued_fraction.of v` did not terminate at position `n`. That is, we obtain the
value `v` if we pass the two successive (auxiliary) continuants at positions `n` and `n + 1` as well
as the fractional part at `int_fract_pair.stream n` to `comp_exact_value`.

The correctness might be seen more readily if one uses `convergents'` to evaluate the continued
fraction. Here is an example to illustrate the idea:

Let `(v : ℚ) := 3.4`. We have
- `generalized_continued_fraction.int_fract_pair.stream v 0 = some ⟨3, 0.4⟩`, and
- `generalized_continued_fraction.int_fract_pair.stream v 1 = some ⟨2, 0.5⟩`.
Now `(generalized_continued_fraction.of v).convergents' 1 = 3 + 1/2`, and our fractional term at
position `2` is `0.5`. We hence have `v = 3 + 1/(2 + 0.5) = 3 + 1/2.5 = 3.4`. This computation
corresponds exactly to the one using the recurrence equation in `comp_exact_value`.
-/
theorem comp_exact_value_correctness_of_stream_eq_some : ∀
{ifp_n : int_fract_pair K}, «expr = »(int_fract_pair.stream v n, some ifp_n) → «expr = »(v, comp_exact_value ((of v).continuants_aux n) «expr $ »((of v).continuants_aux, «expr + »(n, 1)) ifp_n.fr) :=
begin
  let [ident g] [] [":=", expr of v],
  induction [expr n] [] ["with", ident n, ident IH] [],
  { assume [binders (ifp_zero stream_zero_eq)],
    have [] [":", expr «expr = »(int_fract_pair.of v, ifp_zero)] [],
    by { have [] [":", expr «expr = »(int_fract_pair.stream v 0, some (int_fract_pair.of v))] [],
      from [expr rfl],
      simpa [] [] ["only"] ["[", expr this, "]"] [] ["using", expr stream_zero_eq] },
    cases [expr this] [],
    cases [expr decidable.em «expr = »(int.fract v, 0)] ["with", ident fract_eq_zero, ident fract_ne_zero],
    { suffices [] [":", expr «expr = »(v, «expr⌊ ⌋»(v))],
      by simpa [] [] [] ["[", expr continuants_aux, ",", expr fract_eq_zero, ",", expr comp_exact_value, "]"] [] [],
      calc
        «expr = »(v, «expr + »(int.fract v, «expr⌊ ⌋»(v))) : by rw [expr int.fract_add_floor] []
        «expr = »(..., «expr⌊ ⌋»(v)) : by simp [] [] [] ["[", expr fract_eq_zero, "]"] [] [] },
    { field_simp [] ["[", expr continuants_aux, ",", expr next_continuants, ",", expr next_numerator, ",", expr next_denominator, ",", expr of_h_eq_floor, ",", expr comp_exact_value, ",", expr fract_ne_zero, "]"] [] [] } },
  { assume [binders (ifp_succ_n succ_nth_stream_eq)],
    obtain ["⟨", ident ifp_n, ",", ident nth_stream_eq, ",", ident nth_fract_ne_zero, ",", "-", "⟩", ":", expr «expr∃ , »((ifp_n), «expr ∧ »(«expr = »(int_fract_pair.stream v n, some ifp_n), «expr ∧ »(«expr ≠ »(ifp_n.fr, 0), «expr = »(int_fract_pair.of «expr ⁻¹»(ifp_n.fr), ifp_succ_n))))],
    from [expr int_fract_pair.succ_nth_stream_eq_some_iff.elim_left succ_nth_stream_eq],
    let [ident conts] [] [":=", expr g.continuants_aux «expr + »(n, 2)],
    set [] [ident pconts] [] [":="] [expr g.continuants_aux «expr + »(n, 1)] ["with", ident pconts_eq],
    set [] [ident ppconts] [] [":="] [expr g.continuants_aux n] ["with", ident ppconts_eq],
    cases [expr decidable.em «expr = »(ifp_succ_n.fr, 0)] ["with", ident ifp_succ_n_fr_eq_zero, ident ifp_succ_n_fr_ne_zero],
    { suffices [] [":", expr «expr = »(v, «expr / »(conts.a, conts.b))],
      by simpa [] [] [] ["[", expr comp_exact_value, ",", expr ifp_succ_n_fr_eq_zero, "]"] [] [],
      obtain ["⟨", ident ifp_n', ",", ident nth_stream_eq', ",", ident ifp_n_fract_inv_eq_floor, "⟩", ":", expr «expr∃ , »((ifp_n), «expr ∧ »(«expr = »(int_fract_pair.stream v n, some ifp_n), «expr = »(«expr ⁻¹»(ifp_n.fr), «expr⌊ ⌋»(«expr ⁻¹»(ifp_n.fr)))))],
      from [expr int_fract_pair.exists_succ_nth_stream_of_fr_zero succ_nth_stream_eq ifp_succ_n_fr_eq_zero],
      have [] [":", expr «expr = »(ifp_n', ifp_n)] [],
      by injection [expr eq.trans nth_stream_eq'.symm nth_stream_eq] [],
      cases [expr this] [],
      have [ident s_nth_eq] [":", expr «expr = »(g.s.nth n, some ⟨1, «expr⌊ ⌋»(«expr ⁻¹»(ifp_n.fr))⟩)] [],
      from [expr nth_of_eq_some_of_nth_int_fract_pair_stream_fr_ne_zero nth_stream_eq nth_fract_ne_zero],
      rw ["[", "<-", expr ifp_n_fract_inv_eq_floor, "]"] ["at", ident s_nth_eq],
      suffices [] [":", expr «expr = »(v, comp_exact_value ppconts pconts ifp_n.fr)],
      by simpa [] [] [] ["[", expr conts, ",", expr continuants_aux, ",", expr s_nth_eq, ",", expr comp_exact_value, ",", expr nth_fract_ne_zero, "]"] [] ["using", expr this],
      exact [expr IH nth_stream_eq] },
    { suffices [] [":", expr «expr = »(comp_exact_value ppconts pconts ifp_n.fr, comp_exact_value pconts conts ifp_succ_n.fr)],
      by { have [] [":", expr «expr = »(v, comp_exact_value ppconts pconts ifp_n.fr)] [],
        from [expr IH nth_stream_eq],
        conv_lhs [] [] { rw [expr this] },
        assumption },
      obtain ["⟨", ident ifp_n', ",", ident nth_stream_eq', ",", ident ifp_n_fract_ne_zero, ",", "⟨", ident refl, "⟩", "⟩", ":", expr «expr∃ , »((ifp_n), «expr ∧ »(«expr = »(int_fract_pair.stream v n, some ifp_n), «expr ∧ »(«expr ≠ »(ifp_n.fr, 0), «expr = »(int_fract_pair.of «expr ⁻¹»(ifp_n.fr), ifp_succ_n))))],
      from [expr int_fract_pair.succ_nth_stream_eq_some_iff.elim_left succ_nth_stream_eq],
      have [] [":", expr «expr = »(ifp_n', ifp_n)] [],
      by injection [expr eq.trans nth_stream_eq'.symm nth_stream_eq] [],
      cases [expr this] [],
      have [ident s_nth_eq] [":", expr «expr = »(g.s.nth n, some ⟨1, («expr⌊ ⌋»(«expr ⁻¹»(ifp_n.fr)) : K)⟩)] [],
      from [expr nth_of_eq_some_of_nth_int_fract_pair_stream_fr_ne_zero nth_stream_eq ifp_n_fract_ne_zero],
      let [ident ppA] [] [":=", expr ppconts.a],
      let [ident ppB] [] [":=", expr ppconts.b],
      let [ident pA] [] [":=", expr pconts.a],
      let [ident pB] [] [":=", expr pconts.b],
      have [] [":", expr «expr = »(comp_exact_value ppconts pconts ifp_n.fr, «expr / »(«expr + »(ppA, «expr * »(«expr ⁻¹»(ifp_n.fr), pA)), «expr + »(ppB, «expr * »(«expr ⁻¹»(ifp_n.fr), pB))))] [],
      by { field_simp [] ["[", expr ifp_n_fract_ne_zero, ",", expr comp_exact_value, ",", expr next_continuants, ",", expr next_numerator, ",", expr next_denominator, "]"] [] [],
        ac_refl },
      rw [expr this] [],
      have [ident tmp_calc] [] [":=", expr comp_exact_value_correctness_of_stream_eq_some_aux_comp pA ppA ifp_succ_n_fr_ne_zero],
      have [ident tmp_calc'] [] [":=", expr comp_exact_value_correctness_of_stream_eq_some_aux_comp pB ppB ifp_succ_n_fr_ne_zero],
      rw [expr inv_eq_one_div] ["at", ident tmp_calc, ident tmp_calc'],
      have [] [":", expr «expr ≠ »(int.fract «expr / »(1, ifp_n.fr), 0)] [],
      by simpa [] [] [] [] [] ["using", expr ifp_succ_n_fr_ne_zero],
      field_simp [] ["[", expr conts, ",", expr comp_exact_value, ",", expr continuants_aux_recurrence s_nth_eq ppconts_eq pconts_eq, ",", expr next_continuants, ",", expr next_numerator, ",", expr next_denominator, ",", expr this, ",", expr tmp_calc, ",", expr tmp_calc', "]"] [] [],
      ac_refl } }
end

open generalized_continued_fraction(of_terminated_at_n_iff_succ_nth_int_fract_pair_stream_eq_none)

-- error in Algebra.ContinuedFractions.Computation.CorrectnessTerminating: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The convergent of `generalized_continued_fraction.of v` at step `n - 1` is exactly `v` if the
`int_fract_pair.stream` of the corresponding continued fraction terminated at step `n`. -/
theorem of_correctness_of_nth_stream_eq_none
(nth_stream_eq_none : «expr = »(int_fract_pair.stream v n, none)) : «expr = »(v, (of v).convergents «expr - »(n, 1)) :=
begin
  induction [expr n] [] ["with", ident n, ident IH] [],
  case [ident nat.zero] { contradiction },
  case [ident nat.succ] { rename [ident nth_stream_eq_none, ident succ_nth_stream_eq_none],
    let [ident g] [] [":=", expr of v],
    change [expr «expr = »(v, g.convergents n)] [] [],
    have [] [":", expr «expr ∨ »(«expr = »(int_fract_pair.stream v n, none), «expr∃ , »((ifp), «expr ∧ »(«expr = »(int_fract_pair.stream v n, some ifp), «expr = »(ifp.fr, 0))))] [],
    from [expr int_fract_pair.succ_nth_stream_eq_none_iff.elim_left succ_nth_stream_eq_none],
    rcases [expr this, "with", "⟨", ident nth_stream_eq_none, "⟩", "|", "⟨", ident ifp_n, ",", ident nth_stream_eq, ",", ident nth_stream_fr_eq_zero, "⟩"],
    { cases [expr n] ["with", ident n'],
      { contradiction },
      { have [] [":", expr g.terminated_at n'] [],
        from [expr of_terminated_at_n_iff_succ_nth_int_fract_pair_stream_eq_none.elim_right nth_stream_eq_none],
        have [] [":", expr «expr = »(g.convergents «expr + »(n', 1), g.convergents n')] [],
        from [expr convergents_stable_of_terminated n'.le_succ this],
        rw [expr this] [],
        exact [expr IH nth_stream_eq_none] } },
    { simpa [] [] [] ["[", expr nth_stream_fr_eq_zero, ",", expr comp_exact_value, "]"] [] ["using", expr comp_exact_value_correctness_of_stream_eq_some nth_stream_eq] } }
end

/--
If `generalized_continued_fraction.of v` terminated at step `n`, then the `n`th convergent is
exactly `v`.
-/
theorem of_correctness_of_terminated_at (terminated_at_n : (of v).TerminatedAt n) : v = (of v).convergents n :=
  have  : int_fract_pair.stream v (n+1) = none :=
    of_terminated_at_n_iff_succ_nth_int_fract_pair_stream_eq_none.elim_left terminated_at_n 
  of_correctness_of_nth_stream_eq_none this

/--
If `generalized_continued_fraction.of v` terminates, then there is `n : ℕ` such that the `n`th
convergent is exactly `v`.
-/
theorem of_correctness_of_terminates (terminates : (of v).Terminates) : ∃ n : ℕ, v = (of v).convergents n :=
  Exists.elim terminates fun n terminated_at_n => Exists.introₓ n (of_correctness_of_terminated_at terminated_at_n)

open Filter

/--
If `generalized_continued_fraction.of v` terminates, then its convergents will eventually always
be `v`.
-/
theorem of_correctness_at_top_of_terminates (terminates : (of v).Terminates) :
  ∀ᶠn in at_top, v = (of v).convergents n :=
  by 
    rw [eventually_at_top]
    obtain ⟨n, terminated_at_n⟩ : ∃ n, (of v).TerminatedAt n 
    exact terminates 
    use n 
    intro m m_geq_n 
    rw [convergents_stable_of_terminated m_geq_n terminated_at_n]
    exact of_correctness_of_terminated_at terminated_at_n

end GeneralizedContinuedFraction

