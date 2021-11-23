import Mathbin.Algebra.ContinuedFractions.Translations

/-!
# Stabilisation of gcf Computations Under Termination

## Summary

We show that the continuants and convergents of a gcf stabilise once the gcf terminates.
-/


namespace GeneralizedContinuedFraction

variable{K : Type _}{g : GeneralizedContinuedFraction K}{n m : ℕ}

/-- If a gcf terminated at position `n`, it also terminated at `m ≥ n`.-/
theorem terminated_stable (n_le_m : n ≤ m) (terminated_at_n : g.terminated_at n) : g.terminated_at m :=
  g.s.terminated_stable n_le_m terminated_at_n

variable[DivisionRing K]

theorem continuants_aux_stable_step_of_terminated (terminated_at_n : g.terminated_at n) :
  g.continuants_aux (n+2) = g.continuants_aux (n+1) :=
  by 
    rw [terminated_at_iff_s_none] at terminated_at_n 
    simp only [terminated_at_n, continuants_aux]

-- error in Algebra.ContinuedFractions.TerminatedStable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem continuants_aux_stable_of_terminated
(succ_n_le_m : «expr ≤ »(«expr + »(n, 1), m))
(terminated_at_n : g.terminated_at n) : «expr = »(g.continuants_aux m, g.continuants_aux «expr + »(n, 1)) :=
begin
  induction [expr succ_n_le_m] [] ["with", ident m, ident succ_n_le_m, ident IH] [],
  { refl },
  { have [] [":", expr «expr = »(g.continuants_aux «expr + »(m, 1), g.continuants_aux m)] [],
    by { have [] [":", expr «expr ≤ »(n, «expr - »(m, 1))] [],
      from [expr nat.le_pred_of_lt succ_n_le_m],
      have [] [":", expr g.terminated_at «expr - »(m, 1)] [],
      from [expr terminated_stable this terminated_at_n],
      have [ident stable_step] [":", expr «expr = »(g.continuants_aux «expr + »(«expr - »(m, 1), 2), g.continuants_aux «expr + »(«expr - »(m, 1), 1))] [],
      from [expr continuants_aux_stable_step_of_terminated this],
      have [ident one_le_m] [":", expr «expr ≤ »(1, m)] [],
      from [expr nat.one_le_of_lt succ_n_le_m],
      have [] [":", expr «expr = »(«expr + »(«expr - »(m, 1), 2), «expr - »(«expr + »(m, 2), 1))] [],
      from [expr tsub_add_eq_add_tsub one_le_m],
      have [] [":", expr «expr = »(«expr + »(«expr - »(m, 1), 1), «expr - »(«expr + »(m, 1), 1))] [],
      from [expr tsub_add_eq_add_tsub one_le_m],
      simpa [] [] [] ["[", "*", "]"] [] ["using", expr stable_step] },
    exact [expr eq.trans this IH] }
end

-- error in Algebra.ContinuedFractions.TerminatedStable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem convergents'_aux_stable_step_of_terminated
{s : «expr $ »(seq, pair K)}
(terminated_at_n : s.terminated_at n) : «expr = »(convergents'_aux s «expr + »(n, 1), convergents'_aux s n) :=
begin
  change [expr «expr = »(s.nth n, none)] [] ["at", ident terminated_at_n],
  induction [expr n] [] ["with", ident n, ident IH] ["generalizing", ident s],
  case [ident nat.zero] { simp [] [] ["only"] ["[", expr convergents'_aux, ",", expr terminated_at_n, ",", expr seq.head, "]"] [] [] },
  case [ident nat.succ] { cases [expr s_head_eq, ":", expr s.head] ["with", ident gp_head],
    case [ident option.none] { simp [] [] ["only"] ["[", expr convergents'_aux, ",", expr s_head_eq, "]"] [] [] },
    case [ident option.some] { have [] [":", expr s.tail.terminated_at n] [],
      by simp [] [] ["only"] ["[", expr seq.terminated_at, ",", expr s.nth_tail, ",", expr terminated_at_n, "]"] [] [],
      simp [] [] ["only"] ["[", expr convergents'_aux, ",", expr s_head_eq, ",", expr IH this, "]"] [] [] } }
end

-- error in Algebra.ContinuedFractions.TerminatedStable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem convergents'_aux_stable_of_terminated
{s : «expr $ »(seq, pair K)}
(n_le_m : «expr ≤ »(n, m))
(terminated_at_n : s.terminated_at n) : «expr = »(convergents'_aux s m, convergents'_aux s n) :=
begin
  induction [expr n_le_m] [] ["with", ident m, ident n_le_m, ident IH] ["generalizing", ident s],
  { refl },
  { cases [expr s_head_eq, ":", expr s.head] ["with", ident gp_head],
    case [ident option.none] { cases [expr n] []; simp [] [] ["only"] ["[", expr convergents'_aux, ",", expr s_head_eq, "]"] [] [] },
    case [ident option.some] { have [] [":", expr «expr = »(convergents'_aux s «expr + »(n, 1), convergents'_aux s n)] [],
      from [expr convergents'_aux_stable_step_of_terminated terminated_at_n],
      rw ["[", "<-", expr this, "]"] [],
      have [] [":", expr s.tail.terminated_at n] [],
      by simpa [] [] ["only"] ["[", expr seq.terminated_at, ",", expr seq.nth_tail, "]"] [] ["using", expr s.le_stable n.le_succ terminated_at_n],
      have [] [":", expr «expr = »(convergents'_aux s.tail m, convergents'_aux s.tail n)] [],
      from [expr IH this],
      simp [] [] ["only"] ["[", expr convergents'_aux, ",", expr s_head_eq, ",", expr this, "]"] [] [] } }
end

theorem continuants_stable_of_terminated (n_le_m : n ≤ m) (terminated_at_n : g.terminated_at n) :
  g.continuants m = g.continuants n :=
  by 
    simp only [nth_cont_eq_succ_nth_cont_aux,
      continuants_aux_stable_of_terminated (nat.pred_le_iff.elim_left n_le_m) terminated_at_n]

theorem numerators_stable_of_terminated (n_le_m : n ≤ m) (terminated_at_n : g.terminated_at n) :
  g.numerators m = g.numerators n :=
  by 
    simp only [num_eq_conts_a, continuants_stable_of_terminated n_le_m terminated_at_n]

theorem denominators_stable_of_terminated (n_le_m : n ≤ m) (terminated_at_n : g.terminated_at n) :
  g.denominators m = g.denominators n :=
  by 
    simp only [denom_eq_conts_b, continuants_stable_of_terminated n_le_m terminated_at_n]

theorem convergents_stable_of_terminated (n_le_m : n ≤ m) (terminated_at_n : g.terminated_at n) :
  g.convergents m = g.convergents n :=
  by 
    simp only [convergents, denominators_stable_of_terminated n_le_m terminated_at_n,
      numerators_stable_of_terminated n_le_m terminated_at_n]

theorem convergents'_stable_of_terminated (n_le_m : n ≤ m) (terminated_at_n : g.terminated_at n) :
  g.convergents' m = g.convergents' n :=
  by 
    simp only [convergents', convergents'_aux_stable_of_terminated n_le_m terminated_at_n]

end GeneralizedContinuedFraction

