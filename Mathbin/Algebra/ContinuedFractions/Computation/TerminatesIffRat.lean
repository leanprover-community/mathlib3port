import Mathbin.Algebra.ContinuedFractions.Computation.Approximations 
import Mathbin.Algebra.ContinuedFractions.Computation.CorrectnessTerminating 
import Mathbin.Algebra.Order.Archimedean 
import Mathbin.Data.Rat.Floor

/-!
# Termination of Continued Fraction Computations (`gcf.of`)

## Summary
We show that the continued fraction for a value `v`, as defined in
`algebra.continued_fractions.computation.basic`, terminates if and only if `v` corresponds to a
rational number, that is `↑v = q` for some `q : ℚ`.

## Main Theorems

- `generalized_continued_fraction.coe_of_rat` shows that
  `generalized_continued_fraction.of v = generalized_continued_fraction.of q` for `v : α` given that
  `↑v = q` and `q : ℚ`.
- `generalized_continued_fraction.terminates_iff_rat` shows that
  `generalized_continued_fraction.of v` terminates if and only if `↑v = q` for some `q : ℚ`.

## Tags

rational, continued fraction, termination
-/


namespace GeneralizedContinuedFraction

open generalized_continued_fraction(of)

variable{K : Type _}[LinearOrderedField K][FloorRing K]

attribute [local simp] pair.map int_fract_pair.mapFr

section RatOfTerminates

/-!
### Terminating Continued Fractions Are Rational

We want to show that the computation of a continued fraction `generalized_continued_fraction.of v`
terminates if and only if `v ∈ ℚ`. In this section, we show the implication from left to right.

We first show that every finite convergent corresponds to a rational number `q` and then use the
finite correctness proof (`of_correctness_of_terminates`) of `generalized_continued_fraction.of` to
show that `v = ↑q`.
-/


variable(v : K)(n : ℕ)

-- error in Algebra.ContinuedFractions.Computation.TerminatesIffRat: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_gcf_pair_rat_eq_of_nth_conts_aux : «expr∃ , »((conts : pair exprℚ()), «expr = »((of v).continuants_aux n, (conts.map coe : pair K))) :=
nat.strong_induction_on n (begin
   clear [ident n],
   let [ident g] [] [":=", expr of v],
   assume [binders (n IH)],
   rcases [expr n, "with", "_", "|", "_", "|", ident n],
   { suffices [] [":", expr «expr∃ , »((gp : pair exprℚ()), «expr = »(pair.mk (1 : K) 0, gp.map coe))],
     by simpa [] [] [] ["[", expr continuants_aux, "]"] [] [],
     use [expr pair.mk 1 0],
     simp [] [] [] [] [] [] },
   { suffices [] [":", expr «expr∃ , »((conts : pair exprℚ()), «expr = »(pair.mk g.h 1, conts.map coe))],
     by simpa [] [] [] ["[", expr continuants_aux, "]"] [] [],
     use [expr pair.mk «expr⌊ ⌋»(v) 1],
     simp [] [] [] [] [] [] },
   { cases [expr «expr $ »(IH «expr + »(n, 1), lt_add_one «expr + »(n, 1))] ["with", ident pred_conts, ident pred_conts_eq],
     cases [expr s_ppred_nth_eq, ":", expr g.s.nth n] ["with", ident gp_n],
     { use [expr pred_conts],
       have [] [":", expr «expr = »(g.continuants_aux «expr + »(n, 2), g.continuants_aux «expr + »(n, 1))] [],
       from [expr continuants_aux_stable_of_terminated «expr + »(n, 1).le_succ s_ppred_nth_eq],
       simp [] [] ["only"] ["[", expr this, ",", expr pred_conts_eq, "]"] [] [] },
     { cases [expr «expr $ »(IH n, «expr $ »(lt_of_le_of_lt n.le_succ, «expr $ »(lt_add_one, «expr + »(n, 1))))] ["with", ident ppred_conts, ident ppred_conts_eq],
       obtain ["⟨", ident a_eq_one, ",", ident z, ",", ident b_eq_z, "⟩", ":", expr «expr ∧ »(«expr = »(gp_n.a, 1), «expr∃ , »((z : exprℤ()), «expr = »(gp_n.b, (z : K))))],
       from [expr of_part_num_eq_one_and_exists_int_part_denom_eq s_ppred_nth_eq],
       simp [] [] ["only"] ["[", expr a_eq_one, ",", expr b_eq_z, ",", expr continuants_aux_recurrence s_ppred_nth_eq ppred_conts_eq pred_conts_eq, "]"] [] [],
       use [expr next_continuants 1 (z : exprℚ()) ppred_conts pred_conts],
       cases [expr ppred_conts] [],
       cases [expr pred_conts] [],
       simp [] [] [] ["[", expr next_continuants, ",", expr next_numerator, ",", expr next_denominator, "]"] [] [] } }
 end)

theorem exists_gcf_pair_rat_eq_nth_conts : ∃ conts : pair ℚ, (of v).continuants n = (conts.map coeₓ : pair K) :=
  by 
    rw [nth_cont_eq_succ_nth_cont_aux]
    exact exists_gcf_pair_rat_eq_of_nth_conts_aux v$ n+1

theorem exists_rat_eq_nth_numerator : ∃ q : ℚ, (of v).numerators n = (q : K) :=
  by 
    rcases exists_gcf_pair_rat_eq_nth_conts v n with ⟨⟨a, _⟩, nth_cont_eq⟩
    use a 
    simp [num_eq_conts_a, nth_cont_eq]

theorem exists_rat_eq_nth_denominator : ∃ q : ℚ, (of v).denominators n = (q : K) :=
  by 
    rcases exists_gcf_pair_rat_eq_nth_conts v n with ⟨⟨_, b⟩, nth_cont_eq⟩
    use b 
    simp [denom_eq_conts_b, nth_cont_eq]

/-- Every finite convergent corresponds to a rational number. -/
theorem exists_rat_eq_nth_convergent : ∃ q : ℚ, (of v).convergents n = (q : K) :=
  by 
    rcases exists_rat_eq_nth_numerator v n with ⟨Aₙ, nth_num_eq⟩
    rcases exists_rat_eq_nth_denominator v n with ⟨Bₙ, nth_denom_eq⟩
    use Aₙ / Bₙ 
    simp [nth_num_eq, nth_denom_eq, convergent_eq_num_div_denom]

variable{v}

-- error in Algebra.ContinuedFractions.Computation.TerminatesIffRat: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Every terminating continued fraction corresponds to a rational number. -/
theorem exists_rat_eq_of_terminates
(terminates : (of v).terminates) : «expr∃ , »((q : exprℚ()), «expr = »(v, «expr↑ »(q))) :=
begin
  obtain ["⟨", ident n, ",", ident v_eq_conv, "⟩", ":", expr «expr∃ , »((n), «expr = »(v, (of v).convergents n))],
  from [expr of_correctness_of_terminates terminates],
  obtain ["⟨", ident q, ",", ident conv_eq_q, "⟩", ":", expr «expr∃ , »((q : exprℚ()), «expr = »((of v).convergents n, («expr↑ »(q) : K)))],
  from [expr exists_rat_eq_nth_convergent v n],
  have [] [":", expr «expr = »(v, («expr↑ »(q) : K))] [],
  from [expr eq.trans v_eq_conv conv_eq_q],
  use ["[", expr q, ",", expr this, "]"]
end

end RatOfTerminates

section RatTranslation

/-!
### Technical Translation Lemmas

Before we can show that the continued fraction of a rational number terminates, we have to prove
some technical translation lemmas. More precisely, in this section, we show that, given a rational
number `q : ℚ` and value `v : K` with `v = ↑q`, the continued fraction of `q` and `v` coincide.
In particular, we show that
```lean
    (↑(generalized_continued_fraction.of q : generalized_continued_fraction ℚ)
      : generalized_continued_fraction K)
  = generalized_continued_fraction.of v`
```
in `generalized_continued_fraction.coe_of_rat`.

To do this, we proceed bottom-up, showing the correspondence between the basic functions involved in
the computation first and then lift the results step-by-step.
-/


variable{v : K}{q : ℚ}(v_eq_q : v = («expr↑ » q : K))(n : ℕ)

include v_eq_q

/-! First, we show the correspondence for the very basic functions in
`generalized_continued_fraction.int_fract_pair`. -/


namespace IntFractPair

theorem coe_of_rat_eq : ((int_fract_pair.of q).mapFr coeₓ : int_fract_pair K) = int_fract_pair.of v :=
  by 
    simp [int_fract_pair.of, v_eq_q]

-- error in Algebra.ContinuedFractions.Computation.TerminatesIffRat: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem coe_stream_nth_rat_eq : «expr = »(((int_fract_pair.stream q n).map (mapFr coe) : «expr $ »(option, int_fract_pair K)), int_fract_pair.stream v n) :=
begin
  induction [expr n] [] ["with", ident n, ident IH] [],
  case [ident nat.zero, ":"] { simp [] [] [] ["[", expr int_fract_pair.stream, ",", expr coe_of_rat_eq v_eq_q, "]"] [] [] },
  case [ident nat.succ, ":"] { rw [expr v_eq_q] ["at", ident IH],
    cases [expr stream_q_nth_eq, ":", expr int_fract_pair.stream q n] ["with", ident ifp_n],
    case [ident option.none, ":"] { simp [] [] [] ["[", expr int_fract_pair.stream, ",", expr IH.symm, ",", expr v_eq_q, ",", expr stream_q_nth_eq, "]"] [] [] },
    case [ident option.some, ":"] { cases [expr ifp_n] ["with", ident b, ident fr],
      cases [expr decidable.em «expr = »(fr, 0)] ["with", ident fr_zero, ident fr_ne_zero],
      { simp [] [] [] ["[", expr int_fract_pair.stream, ",", expr IH.symm, ",", expr v_eq_q, ",", expr stream_q_nth_eq, ",", expr fr_zero, "]"] [] [] },
      { replace [ident IH] [":", expr «expr = »(some (int_fract_pair.mk b «expr↑ »(fr)), int_fract_pair.stream «expr↑ »(q) n)] [],
        by rwa ["[", expr stream_q_nth_eq, "]"] ["at", ident IH],
        have [] [":", expr «expr = »(«expr ⁻¹»((fr : K)), ((«expr ⁻¹»(fr) : exprℚ()) : K))] [],
        by norm_cast [],
        have [ident coe_of_fr] [] [":=", expr coe_of_rat_eq this],
        simp [] [] [] ["[", expr int_fract_pair.stream, ",", expr IH.symm, ",", expr v_eq_q, ",", expr stream_q_nth_eq, ",", expr fr_ne_zero, "]"] [] [],
        unfold_coes [],
        simpa [] [] [] ["[", expr coe_of_fr, "]"] [] [] } } }
end

theorem coe_stream_rat_eq :
  ((int_fract_pair.stream q).map (Option.map (mapFr coeₓ)) : Streamₓ$ Option$ int_fract_pair K) =
    int_fract_pair.stream v :=
  by 
    funext n 
    exact int_fract_pair.coe_stream_nth_rat_eq v_eq_q n

end IntFractPair

/-! Now we lift the coercion results to the continued fraction computation. -/


theorem coe_of_h_rat_eq : («expr↑ » ((of q).h : ℚ) : K) = (of v).h :=
  by 
    unfold of int_fract_pair.seq1 
    rw [←int_fract_pair.coe_of_rat_eq v_eq_q]
    simp 

theorem coe_of_s_nth_rat_eq : (((of q).s.nth n).map (pair.map coeₓ) : Option$ pair K) = (of v).s.nth n :=
  by 
    simp only [of, int_fract_pair.seq1, Seqₓₓ.map_nth, Seqₓₓ.nth_tail]
    simp only [Seqₓₓ.nth]
    rw [←int_fract_pair.coe_stream_rat_eq v_eq_q]
    rcases succ_nth_stream_eq : int_fract_pair.stream q (n+1) with (_ | ⟨_, _⟩) <;>
      simp [Streamₓ.map, Streamₓ.nth, succ_nth_stream_eq]

theorem coe_of_s_rat_eq : ((of q).s.map (pair.map coeₓ) : Seqₓₓ$ pair K) = (of v).s :=
  by 
    ext n 
    rw [←coe_of_s_nth_rat_eq v_eq_q]
    rfl

/-- Given `(v : K), (q : ℚ), and v = q`, we have that `gcf.of q = gcf.of v` -/
theorem coe_of_rat_eq : (⟨(of q).h, (of q).s.map (pair.map coeₓ)⟩ : GeneralizedContinuedFraction K) = of v :=
  by 
    cases' gcf_v_eq : of v with h s 
    subst v 
    obtain rfl : «expr↑ » ⌊«expr↑ » q⌋ = h
    ·
      ·
        injection gcf_v_eq 
    simp [coe_of_h_rat_eq rfl, coe_of_s_rat_eq rfl, gcf_v_eq]

theorem of_terminates_iff_of_rat_terminates {v : K} {q : ℚ} (v_eq_q : v = (q : K)) :
  (of v).Terminates ↔ (of q).Terminates :=
  by 
    split  <;>
      intro h <;>
        cases' h with n h <;>
          use n <;>
            simp only [Seqₓₓ.TerminatedAt, (coe_of_s_nth_rat_eq v_eq_q n).symm] at h⊢ <;>
              cases (of q).s.nth n <;> trivial

end RatTranslation

section TerminatesOfRat

/-!
### Continued Fractions of Rationals Terminate

Finally, we show that the continued fraction of a rational number terminates.

The crucial insight is that, given any `q : ℚ` with `0 < q < 1`, the numerator of `int.fract q` is
smaller than the numerator of `q`. As the continued fraction computation recursively operates on
the fractional part of a value `v` and `0 ≤ int.fract v < 1`, we infer that the numerator of the
fractional part in the computation decreases by at least one in each step. As `0 ≤ int.fract v`,
this process must stop after finite number of steps, and the computation hence terminates.
-/


namespace IntFractPair

variable{q : ℚ}{n : ℕ}

/--
Shows that for any `q : ℚ` with `0 < q < 1`, the numerator of the fractional part of
`int_fract_pair.of q⁻¹` is smaller than the numerator of `q`.
-/
theorem of_inv_fr_num_lt_num_of_pos (q_pos : 0 < q) : (int_fract_pair.of (q⁻¹)).fr.num < q.num :=
  Rat.fract_inv_num_lt_num_of_pos q_pos

-- error in Algebra.ContinuedFractions.Computation.TerminatesIffRat: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Shows that the sequence of numerators of the fractional parts of the stream is strictly
antitone. -/
theorem stream_succ_nth_fr_num_lt_nth_fr_num_rat
{ifp_n ifp_succ_n : int_fract_pair exprℚ()}
(stream_nth_eq : «expr = »(int_fract_pair.stream q n, some ifp_n))
(stream_succ_nth_eq : «expr = »(int_fract_pair.stream q «expr + »(n, 1), some ifp_succ_n)) : «expr < »(ifp_succ_n.fr.num, ifp_n.fr.num) :=
begin
  obtain ["⟨", ident ifp_n', ",", ident stream_nth_eq', ",", ident ifp_n_fract_ne_zero, ",", ident int_fract_pair.of_eq_ifp_succ_n, "⟩", ":", expr «expr∃ , »((ifp_n'), «expr ∧ »(«expr = »(int_fract_pair.stream q n, some ifp_n'), «expr ∧ »(«expr ≠ »(ifp_n'.fr, 0), «expr = »(int_fract_pair.of «expr ⁻¹»(ifp_n'.fr), ifp_succ_n))))],
  from [expr succ_nth_stream_eq_some_iff.elim_left stream_succ_nth_eq],
  have [] [":", expr «expr = »(ifp_n, ifp_n')] [],
  by injection [expr eq.trans stream_nth_eq.symm stream_nth_eq'] [],
  cases [expr this] [],
  rw ["[", "<-", expr int_fract_pair.of_eq_ifp_succ_n, "]"] [],
  cases [expr nth_stream_fr_nonneg_lt_one stream_nth_eq] ["with", ident zero_le_ifp_n_fract, ident ifp_n_fract_lt_one],
  have [] [":", expr «expr < »(0, ifp_n.fr)] [],
  from [expr «expr $ »(lt_of_le_of_ne zero_le_ifp_n_fract, ifp_n_fract_ne_zero.symm)],
  exact [expr of_inv_fr_num_lt_num_of_pos this]
end

-- error in Algebra.ContinuedFractions.Computation.TerminatesIffRat: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem stream_nth_fr_num_le_fr_num_sub_n_rat : ∀
{ifp_n : int_fract_pair exprℚ()}, «expr = »(int_fract_pair.stream q n, some ifp_n) → «expr ≤ »(ifp_n.fr.num, «expr - »((int_fract_pair.of q).fr.num, n)) :=
begin
  induction [expr n] [] ["with", ident n, ident IH] [],
  case [ident nat.zero] { assume [binders (ifp_zero stream_zero_eq)],
    have [] [":", expr «expr = »(int_fract_pair.of q, ifp_zero)] [],
    by injection [expr stream_zero_eq] [],
    simp [] [] [] ["[", expr le_refl, ",", expr this.symm, "]"] [] [] },
  case [ident nat.succ] { assume [binders (ifp_succ_n stream_succ_nth_eq)],
    suffices [] [":", expr «expr ≤ »(«expr + »(ifp_succ_n.fr.num, 1), «expr - »((int_fract_pair.of q).fr.num, n))],
    by { rw ["[", expr int.coe_nat_succ, ",", expr sub_add_eq_sub_sub, "]"] [],
      solve_by_elim [] [] ["[", expr le_sub_right_of_add_le, "]"] [] },
    rcases [expr succ_nth_stream_eq_some_iff.elim_left stream_succ_nth_eq, "with", "⟨", ident ifp_n, ",", ident stream_nth_eq, ",", "-", "⟩"],
    have [] [":", expr «expr < »(ifp_succ_n.fr.num, ifp_n.fr.num)] [],
    from [expr stream_succ_nth_fr_num_lt_nth_fr_num_rat stream_nth_eq stream_succ_nth_eq],
    have [] [":", expr «expr ≤ »(«expr + »(ifp_succ_n.fr.num, 1), ifp_n.fr.num)] [],
    from [expr int.add_one_le_of_lt this],
    exact [expr le_trans this (IH stream_nth_eq)] }
end

-- error in Algebra.ContinuedFractions.Computation.TerminatesIffRat: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_nth_stream_eq_none_of_rat
(q : exprℚ()) : «expr∃ , »((n : exprℕ()), «expr = »(int_fract_pair.stream q n, none)) :=
begin
  let [ident fract_q_num] [] [":=", expr (int.fract q).num],
  let [ident n] [] [":=", expr «expr + »(fract_q_num.nat_abs, 1)],
  cases [expr stream_nth_eq, ":", expr int_fract_pair.stream q n] ["with", ident ifp],
  { use [expr n],
    exact [expr stream_nth_eq] },
  { have [ident ifp_fr_num_le_q_fr_num_sub_n] [":", expr «expr ≤ »(ifp.fr.num, «expr - »(fract_q_num, n))] [],
    from [expr stream_nth_fr_num_le_fr_num_sub_n_rat stream_nth_eq],
    have [] [":", expr «expr = »(«expr - »(fract_q_num, n), «expr- »(1))] [],
    by { have [] [":", expr «expr ≤ »(0, fract_q_num)] [],
      from [expr rat.num_nonneg_iff_zero_le.elim_right (int.fract_nonneg q)],
      simp [] [] [] ["[", expr int.nat_abs_of_nonneg this, ",", expr sub_add_eq_sub_sub_swap, ",", expr sub_right_comm, "]"] [] [] },
    have [] [":", expr «expr ≤ »(ifp.fr.num, «expr- »(1))] [],
    by rwa [expr this] ["at", ident ifp_fr_num_le_q_fr_num_sub_n],
    have [] [":", expr «expr ≤ »(0, ifp.fr)] [],
    from [expr (nth_stream_fr_nonneg_lt_one stream_nth_eq).left],
    have [] [":", expr «expr ≤ »(0, ifp.fr.num)] [],
    from [expr rat.num_nonneg_iff_zero_le.elim_right this],
    linarith [] [] [] }
end

end IntFractPair

/-- The continued fraction of a rational number terminates. -/
theorem terminates_of_rat (q : ℚ) : (of q).Terminates :=
  Exists.elim (int_fract_pair.exists_nth_stream_eq_none_of_rat q)
    fun n stream_nth_eq_none =>
      Exists.introₓ n
        (have  : int_fract_pair.stream q (n+1) = none := int_fract_pair.stream_is_seq q stream_nth_eq_none 
        of_terminated_at_n_iff_succ_nth_int_fract_pair_stream_eq_none.elim_right this)

end TerminatesOfRat

/--
The continued fraction `generalized_continued_fraction.of v` terminates if and only if `v ∈ ℚ`.
-/
theorem terminates_iff_rat (v : K) : (of v).Terminates ↔ ∃ q : ℚ, v = (q : K) :=
  Iff.intro
    (fun terminates_v : (of v).Terminates => show ∃ q : ℚ, v = (q : K) from exists_rat_eq_of_terminates terminates_v)
    fun exists_q_eq_v : ∃ q : ℚ, v = («expr↑ » q : K) =>
      Exists.elim exists_q_eq_v
        fun q =>
          fun v_eq_q : v = «expr↑ » q =>
            have  : (of q).Terminates := terminates_of_rat q
            (of_terminates_iff_of_rat_terminates v_eq_q).elim_right this

end GeneralizedContinuedFraction

