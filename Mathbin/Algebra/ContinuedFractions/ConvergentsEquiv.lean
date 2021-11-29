import Mathbin.Algebra.ContinuedFractions.ContinuantsRecurrence 
import Mathbin.Algebra.ContinuedFractions.TerminatedStable 
import Mathbin.Tactic.Linarith.Default 
import Mathbin.Tactic.FieldSimp

/-!
# Equivalence of Recursive and Direct Computations of `gcf` Convergents

## Summary

We show the equivalence of two computations of convergents (recurrence relation (`convergents`) vs.
direct evaluation (`convergents'`)) for `gcf`s on linear ordered fields. We follow the proof from
[hardy2008introduction], Chapter 10. Here's a sketch:

Let `c` be a continued fraction `[h; (a₀, b₀), (a₁, b₁), (a₂, b₂),...]`, visually:
                                a₀
                h + ---------------------------
                                  a₁
                      b₀ + --------------------
                                    a₂
                            b₁ + --------------
                                        a₃
                                  b₂ + --------
                                      b₃ + ...

One can compute the convergents of `c` in two ways:
1. Directly evaluating the fraction described by `c` up to a given `n` (`convergents'`)
2. Using the recurrence (`convergents`):
  - `A₋₁ = 1,  A₀ = h,  Aₙ = bₙ₋₁ * Aₙ₋₁ + aₙ₋₁ * Aₙ₋₂`, and
  - `B₋₁ = 0,  B₀ = 1,  Bₙ = bₙ₋₁ * Bₙ₋₁ + aₙ₋₁ * Bₙ₋₂`.

To show the equivalence of the computations in the main theorem of this file
`convergents_eq_convergents'`, we proceed by induction. The case `n = 0` is trivial.

For `n + 1`, we first "squash" the `n + 1`th position of `c` into the `n`th position to obtain
another continued fraction
  `c' := [h; (a₀, b₀),..., (aₙ-₁, bₙ-₁), (aₙ, bₙ + aₙ₊₁ / bₙ₊₁), (aₙ₊₁, bₙ₊₁),...]`.
This squashing process is formalised in section `squash`. Note that directly evaluating `c` up to
position `n + 1` is equal to evaluating `c'` up to `n`. This is shown in lemma
`succ_nth_convergent'_eq_squash_gcf_nth_convergent'`.

By the inductive hypothesis, the two computations for the `n`th convergent of `c` coincide.
So all that is left to show is that the recurrence relation for `c` at `n + 1` and and `c'` at
`n` coincide. This can be shown by another induction.
The corresponding lemma in this file is `succ_nth_convergent_eq_squash_gcf_nth_convergent`.

## Main Theorems

- `generalized_continued_fraction.convergents_eq_convergents'` shows the equivalence under a strict
positivity restriction on the sequence.
- `continued_fractions.convergents_eq_convergents'` shows the equivalence for (regular) continued
fractions.

## References

- https://en.wikipedia.org/wiki/Generalized_continued_fraction
- [*Hardy, GH and Wright, EM and Heath-Brown, Roger and Silverman, Joseph*][hardy2008introduction]

## Tags

fractions, recurrence, equivalence
-/


variable {K : Type _} {n : ℕ}

namespace GeneralizedContinuedFraction

variable {g : GeneralizedContinuedFraction K} {s : Seqₓₓ$ pair K}

section Squash

/-!
We will show the equivalence of the computations by induction. To make the induction work, we need
to be able to *squash* the nth and (n + 1)th value of a sequence. This squashing itself and the
lemmas about it are not very interesting. As a reader, you hence might want to skip this section.
-/


section WithDivisionRing

variable [DivisionRing K]

/--
Given a sequence of gcf.pairs `s = [(a₀, bₒ), (a₁, b₁), ...]`, `squash_seq s n`
combines `⟨aₙ, bₙ⟩` and `⟨aₙ₊₁, bₙ₊₁⟩` at position `n` to `⟨aₙ, bₙ + aₙ₊₁ / bₙ₊₁⟩`. For example,
`squash_seq s 0 = [(a₀, bₒ + a₁ / b₁), (a₁, b₁),...]`.
If `s.terminated_at (n + 1)`, then `squash_seq s n = s`.
-/
def squash_seq (s : Seqₓₓ$ pair K) (n : ℕ) : Seqₓₓ (pair K) :=
  match Prod.mk (s.nth n) (s.nth (n+1)) with 
  | ⟨some gp_n, some gp_succ_n⟩ =>
    Seqₓₓ.nats.zipWith (fun n' gp => if n' = n then ⟨gp_n.a, gp_n.b+gp_succ_n.a / gp_succ_n.b⟩ else gp) s
  | _ => s

/-! We now prove some simple lemmas about the squashed sequence -/


/-- If the sequence already terminated at position `n + 1`, nothing gets squashed. -/
theorem squash_seq_eq_self_of_terminated (terminated_at_succ_n : s.terminated_at (n+1)) : squash_seq s n = s :=
  by 
    change s.nth (n+1) = none at terminated_at_succ_n 
    cases s_nth_eq : s.nth n <;> simp only [squash_seq]

/-- If the sequence has not terminated before position `n + 1`, the value at `n + 1` gets
squashed into position `n`. -/
theorem squash_seq_nth_of_not_terminated {gp_n gp_succ_n : pair K} (s_nth_eq : s.nth n = some gp_n)
  (s_succ_nth_eq : s.nth (n+1) = some gp_succ_n) :
  (squash_seq s n).nth n = some ⟨gp_n.a, gp_n.b+gp_succ_n.a / gp_succ_n.b⟩ :=
  by 
    simp [squash_seq, Seqₓₓ.zip_with_nth_some (Seqₓₓ.nats_nth n) s_nth_eq _]

/-- The values before the squashed position stay the same. -/
theorem squash_seq_nth_of_lt {m : ℕ} (m_lt_n : m < n) : (squash_seq s n).nth m = s.nth m :=
  by 
    cases s_succ_nth_eq : s.nth (n+1)
    case option.none => 
      rw [squash_seq_eq_self_of_terminated s_succ_nth_eq]
    case option.some => 
      obtain ⟨gp_n, s_nth_eq⟩ : ∃ gp_n, s.nth n = some gp_n 
      exact s.ge_stable n.le_succ s_succ_nth_eq 
      obtain ⟨gp_m, s_mth_eq⟩ : ∃ gp_m, s.nth m = some gp_m 
      exact s.ge_stable (le_of_ltₓ m_lt_n) s_nth_eq 
      simp [squash_seq, Seqₓₓ.zip_with_nth_some (Seqₓₓ.nats_nth m) s_mth_eq _, ne_of_ltₓ m_lt_n]

-- error in Algebra.ContinuedFractions.ConvergentsEquiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Squashing at position `n + 1` and taking the tail is the same as squashing the tail of the
sequence at position `n`. -/
theorem squash_seq_succ_n_tail_eq_squash_seq_tail_n : «expr = »((squash_seq s «expr + »(n, 1)).tail, squash_seq s.tail n) :=
begin
  cases [expr s_succ_succ_nth_eq, ":", expr s.nth «expr + »(n, 2)] ["with", ident gp_succ_succ_n],
  case [ident option.none] { have [] [":", expr «expr = »(squash_seq s «expr + »(n, 1), s)] [],
    from [expr squash_seq_eq_self_of_terminated s_succ_succ_nth_eq],
    cases [expr s_succ_nth_eq, ":", expr s.nth «expr + »(n, 1)] []; simp [] [] ["only"] ["[", expr squash_seq, ",", expr seq.nth_tail, ",", expr s_succ_nth_eq, ",", expr s_succ_succ_nth_eq, "]"] [] [] },
  case [ident option.some] { obtain ["⟨", ident gp_succ_n, ",", ident s_succ_nth_eq, "⟩", ":", expr «expr∃ , »((gp_succ_n), «expr = »(s.nth «expr + »(n, 1), some gp_succ_n))],
    from [expr s.ge_stable «expr + »(n, 1).le_succ s_succ_succ_nth_eq],
    ext [] [ident m] [],
    cases [expr decidable.em «expr = »(m, n)] ["with", ident m_eq_n, ident m_ne_n],
    { have [] [":", expr «expr = »(s.tail.nth n, some gp_succ_n)] [],
      from [expr (s.nth_tail n).trans s_succ_nth_eq],
      simp [] [] [] ["[", "*", ",", expr squash_seq, ",", expr seq.nth_tail, ",", expr seq.zip_with_nth_some (seq.nats_nth n) this, ",", expr seq.zip_with_nth_some (seq.nats_nth «expr + »(n, 1)) s_succ_nth_eq, "]"] [] [] },
    { have [] [":", expr «expr = »(s.tail.nth m, s.nth «expr + »(m, 1))] [],
      from [expr s.nth_tail m],
      cases [expr s_succ_mth_eq, ":", expr s.nth «expr + »(m, 1)] [],
      all_goals { have [ident s_tail_mth_eq] [] [],
        from [expr this.trans s_succ_mth_eq] },
      { simp [] [] ["only"] ["[", "*", ",", expr squash_seq, ",", expr seq.nth_tail, ",", expr seq.zip_with_nth_none' s_succ_mth_eq, ",", expr seq.zip_with_nth_none' s_tail_mth_eq, "]"] [] [] },
      { simp [] [] [] ["[", "*", ",", expr squash_seq, ",", expr seq.nth_tail, ",", expr seq.zip_with_nth_some (seq.nats_nth «expr + »(m, 1)) s_succ_mth_eq, ",", expr seq.zip_with_nth_some (seq.nats_nth m) s_tail_mth_eq, "]"] [] [] } } }
end

-- error in Algebra.ContinuedFractions.ConvergentsEquiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The auxiliary function `convergents'_aux` returns the same value for a sequence and the
corresponding squashed sequence at the squashed position. -/
theorem succ_succ_nth_convergent'_aux_eq_succ_nth_convergent'_aux_squash_seq : «expr = »(convergents'_aux s «expr + »(n, 2), convergents'_aux (squash_seq s n) «expr + »(n, 1)) :=
begin
  cases [expr s_succ_nth_eq, ":", expr «expr $ »(s.nth, «expr + »(n, 1))] ["with", ident gp_succ_n],
  case [ident option.none] { rw ["[", expr squash_seq_eq_self_of_terminated s_succ_nth_eq, ",", expr convergents'_aux_stable_step_of_terminated s_succ_nth_eq, "]"] [] },
  case [ident option.some] { induction [expr n] [] ["with", ident m, ident IH] ["generalizing", ident s, ident gp_succ_n],
    case [ident nat.zero] { obtain ["⟨", ident gp_head, ",", ident s_head_eq, "⟩", ":", expr «expr∃ , »((gp_head), «expr = »(s.head, some gp_head))],
      from [expr s.ge_stable zero_le_one s_succ_nth_eq],
      have [] [":", expr «expr = »((squash_seq s 0).head, some ⟨gp_head.a, «expr + »(gp_head.b, «expr / »(gp_succ_n.a, gp_succ_n.b))⟩)] [],
      from [expr squash_seq_nth_of_not_terminated s_head_eq s_succ_nth_eq],
      simp [] [] [] ["[", "*", ",", expr convergents'_aux, ",", expr seq.head, ",", expr seq.nth_tail, "]"] [] [] },
    case [ident nat.succ] { obtain ["⟨", ident gp_head, ",", ident s_head_eq, "⟩", ":", expr «expr∃ , »((gp_head), «expr = »(s.head, some gp_head))],
      from [expr s.ge_stable «expr + »(m, 2).zero_le s_succ_nth_eq],
      suffices [] [":", expr «expr = »(«expr / »(gp_head.a, «expr + »(gp_head.b, convergents'_aux s.tail «expr + »(m, 2))), convergents'_aux (squash_seq s «expr + »(m, 1)) «expr + »(m, 2))],
      by simpa [] [] ["only"] ["[", expr convergents'_aux, ",", expr s_head_eq, "]"] [] [],
      have [] [":", expr «expr = »(convergents'_aux s.tail «expr + »(m, 2), convergents'_aux (squash_seq s.tail m) «expr + »(m, 1))] [],
      by { refine [expr IH gp_succ_n _],
        simpa [] [] [] ["[", expr seq.nth_tail, "]"] [] ["using", expr s_succ_nth_eq] },
      have [] [":", expr «expr = »((squash_seq s «expr + »(m, 1)).head, some gp_head)] [],
      from [expr (squash_seq_nth_of_lt m.succ_pos).trans s_head_eq],
      simp [] [] ["only"] ["[", "*", ",", expr convergents'_aux, ",", expr squash_seq_succ_n_tail_eq_squash_seq_tail_n, "]"] [] [] } }
end

/-! Let us now lift the squashing operation to gcfs. -/


/--
Given a gcf `g = [h; (a₀, bₒ), (a₁, b₁), ...]`, we have
- `squash_nth.gcf g 0 = [h + a₀ / b₀); (a₀, bₒ), ...]`,
- `squash_nth.gcf g (n + 1) = ⟨g.h, squash_seq g.s n⟩`
-/
def squash_gcf (g : GeneralizedContinuedFraction K) : ℕ → GeneralizedContinuedFraction K
| 0 =>
  match g.s.nth 0 with 
  | none => g
  | some gp => ⟨g.h+gp.a / gp.b, g.s⟩
| n+1 => ⟨g.h, squash_seq g.s n⟩

/-! Again, we derive some simple lemmas that are not really of interest. This time for the
squashed gcf. -/


/-- If the gcf already terminated at position `n`, nothing gets squashed. -/
theorem squash_gcf_eq_self_of_terminated (terminated_at_n : terminated_at g n) : squash_gcf g n = g :=
  by 
    cases n 
    case nat.zero => 
      change g.s.nth 0 = none at terminated_at_n 
      simp only [convergents', squash_gcf, convergents'_aux, terminated_at_n]
    case nat.succ => 
      cases g 
      simp [squash_seq_eq_self_of_terminated terminated_at_n, squash_gcf]

/-- The values before the squashed position stay the same. -/
theorem squash_gcf_nth_of_lt {m : ℕ} (m_lt_n : m < n) : (squash_gcf g (n+1)).s.nth m = g.s.nth m :=
  by 
    simp only [squash_gcf, squash_seq_nth_of_lt m_lt_n]

/-- `convergents'` returns the same value for a gcf and the corresponding squashed gcf at the
squashed position. -/
theorem succ_nth_convergent'_eq_squash_gcf_nth_convergent' : g.convergents' (n+1) = (squash_gcf g n).convergents' n :=
  by 
    cases n 
    case nat.zero => 
      cases g_s_head_eq : g.s.nth 0 <;> simp [g_s_head_eq, squash_gcf, convergents', convergents'_aux, Seqₓₓ.head]
    case nat.succ => 
      simp only [succ_succ_nth_convergent'_aux_eq_succ_nth_convergent'_aux_squash_seq, convergents', squash_gcf]

-- error in Algebra.ContinuedFractions.ConvergentsEquiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The auxiliary continuants before the squashed position stay the same. -/
theorem continuants_aux_eq_continuants_aux_squash_gcf_of_le
{m : exprℕ()} : «expr ≤ »(m, n) → «expr = »(continuants_aux g m, (squash_gcf g n).continuants_aux m) :=
nat.strong_induction_on m (begin
   clear [ident m],
   assume [binders (m IH m_le_n)],
   cases [expr m] ["with", ident m'],
   { refl },
   { cases [expr n] ["with", ident n'],
     { exact [expr (m'.not_succ_le_zero m_le_n).elim] },
     { cases [expr m'] ["with", ident m''],
       { refl },
       { have [ident m'_lt_n] [":", expr «expr < »(«expr + »(m'', 1), «expr + »(n', 1))] [":=", expr m_le_n],
         have [ident succ_m''th_conts_aux_eq] [] [":=", expr IH «expr + »(m'', 1) (lt_add_one «expr + »(m'', 1)) m'_lt_n.le],
         have [] [":", expr «expr < »(m'', «expr + »(m'', 2))] [":=", expr lt_add_of_pos_right m'' zero_lt_two],
         have [ident m''th_conts_aux_eq] [] [":=", expr IH m'' this (le_trans this.le m_le_n)],
         have [] [":", expr «expr = »((squash_gcf g «expr + »(n', 1)).s.nth m'', g.s.nth m'')] [],
         from [expr squash_gcf_nth_of_lt (nat.succ_lt_succ_iff.mp m'_lt_n)],
         simp [] [] [] ["[", expr continuants_aux, ",", expr succ_m''th_conts_aux_eq, ",", expr m''th_conts_aux_eq, ",", expr this, "]"] [] [] } } }
 end)

end WithDivisionRing

-- error in Algebra.ContinuedFractions.ConvergentsEquiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The convergents coincide in the expected way at the squashed position if the partial denominator
at the squashed position is not zero. -/
theorem succ_nth_convergent_eq_squash_gcf_nth_convergent
[field K]
(nth_part_denom_ne_zero : ∀
 {b : K}, «expr = »(g.partial_denominators.nth n, some b) → «expr ≠ »(b, 0)) : «expr = »(g.convergents «expr + »(n, 1), (squash_gcf g n).convergents n) :=
begin
  cases [expr decidable.em (g.terminated_at n)] ["with", ident terminated_at_n, ident not_terminated_at_n],
  { have [] [":", expr «expr = »(squash_gcf g n, g)] [],
    from [expr squash_gcf_eq_self_of_terminated terminated_at_n],
    simp [] [] ["only"] ["[", expr this, ",", expr convergents_stable_of_terminated n.le_succ terminated_at_n, "]"] [] [] },
  { obtain ["⟨", "⟨", ident a, ",", ident b, "⟩", ",", ident s_nth_eq, "⟩", ":", expr «expr∃ , »((gp_n), «expr = »(g.s.nth n, some gp_n))],
    from [expr option.ne_none_iff_exists'.mp not_terminated_at_n],
    have [ident b_ne_zero] [":", expr «expr ≠ »(b, 0)] [],
    from [expr nth_part_denom_ne_zero (part_denom_eq_s_b s_nth_eq)],
    cases [expr n] ["with", ident n'],
    case [ident nat.zero] { suffices [] [":", expr «expr = »(«expr / »(«expr + »(«expr * »(b, g.h), a), b), «expr + »(g.h, «expr / »(a, b)))],
      by simpa [] [] [] ["[", expr squash_gcf, ",", expr s_nth_eq, ",", expr convergent_eq_conts_a_div_conts_b, ",", expr continuants_recurrence_aux s_nth_eq zeroth_continuant_aux_eq_one_zero first_continuant_aux_eq_h_one, "]"] [] [],
      calc
        «expr = »(«expr / »(«expr + »(«expr * »(b, g.h), a), b), «expr + »(«expr / »(«expr * »(b, g.h), b), «expr / »(a, b))) : by ring []
        «expr = »(..., «expr + »(g.h, «expr / »(a, b))) : by rw [expr mul_div_cancel_left _ b_ne_zero] [] },
    case [ident nat.succ] { obtain ["⟨", "⟨", ident pa, ",", ident pb, "⟩", ",", ident s_n'th_eq, "⟩", ":", expr «expr∃ , »((gp_n'), «expr = »(g.s.nth n', some gp_n')), ":=", expr g.s.ge_stable n'.le_succ s_nth_eq],
      let [ident g'] [] [":=", expr squash_gcf g «expr + »(n', 1)],
      set [] [ident pred_conts] [] [":="] [expr g.continuants_aux «expr + »(n', 1)] ["with", ident succ_n'th_conts_aux_eq],
      set [] [ident ppred_conts] [] [":="] [expr g.continuants_aux n'] ["with", ident n'th_conts_aux_eq],
      let [ident pA] [] [":=", expr pred_conts.a],
      let [ident pB] [] [":=", expr pred_conts.b],
      let [ident ppA] [] [":=", expr ppred_conts.a],
      let [ident ppB] [] [":=", expr ppred_conts.b],
      set [] [ident pred_conts'] [] [":="] [expr g'.continuants_aux «expr + »(n', 1)] ["with", ident succ_n'th_conts_aux_eq'],
      set [] [ident ppred_conts'] [] [":="] [expr g'.continuants_aux n'] ["with", ident n'th_conts_aux_eq'],
      let [ident pA'] [] [":=", expr pred_conts'.a],
      let [ident pB'] [] [":=", expr pred_conts'.b],
      let [ident ppA'] [] [":=", expr ppred_conts'.a],
      let [ident ppB'] [] [":=", expr ppred_conts'.b],
      have [] [":", expr «expr = »(g'.convergents «expr + »(n', 1), «expr / »(«expr + »(«expr * »(«expr + »(pb, «expr / »(a, b)), pA'), «expr * »(pa, ppA')), «expr + »(«expr * »(«expr + »(pb, «expr / »(a, b)), pB'), «expr * »(pa, ppB'))))] [],
      { have [] [":", expr «expr = »(g'.s.nth n', some ⟨pa, «expr + »(pb, «expr / »(a, b))⟩)] [":=", expr squash_seq_nth_of_not_terminated s_n'th_eq s_nth_eq],
        rw ["[", expr convergent_eq_conts_a_div_conts_b, ",", expr continuants_recurrence_aux this n'th_conts_aux_eq'.symm succ_n'th_conts_aux_eq'.symm, "]"] [] },
      rw [expr this] [],
      have [] [":", expr «expr = »(g.convergents «expr + »(n', 2), «expr / »(«expr + »(«expr * »(b, «expr + »(«expr * »(pb, pA), «expr * »(pa, ppA))), «expr * »(a, pA)), «expr + »(«expr * »(b, «expr + »(«expr * »(pb, pB), «expr * »(pa, ppB))), «expr * »(a, pB))))] [],
      { have [] [":", expr «expr = »(g.continuants_aux «expr + »(n', 2), ⟨«expr + »(«expr * »(pb, pA), «expr * »(pa, ppA)), «expr + »(«expr * »(pb, pB), «expr * »(pa, ppB))⟩)] [":=", expr continuants_aux_recurrence s_n'th_eq n'th_conts_aux_eq.symm succ_n'th_conts_aux_eq.symm],
        rw ["[", expr convergent_eq_conts_a_div_conts_b, ",", expr continuants_recurrence_aux s_nth_eq succ_n'th_conts_aux_eq.symm this, "]"] [] },
      rw [expr this] [],
      suffices [] [":", expr «expr = »(«expr / »(«expr + »(«expr * »(«expr + »(pb, «expr / »(a, b)), pA), «expr * »(pa, ppA)), «expr + »(«expr * »(«expr + »(pb, «expr / »(a, b)), pB), «expr * »(pa, ppB))), «expr / »(«expr + »(«expr * »(b, «expr + »(«expr * »(pb, pA), «expr * »(pa, ppA))), «expr * »(a, pA)), «expr + »(«expr * »(b, «expr + »(«expr * »(pb, pB), «expr * »(pa, ppB))), «expr * »(a, pB))))],
      { obtain ["⟨", ident eq1, ",", ident eq2, ",", ident eq3, ",", ident eq4, "⟩", ":", expr «expr ∧ »(«expr = »(pA', pA), «expr ∧ »(«expr = »(pB', pB), «expr ∧ »(«expr = »(ppA', ppA), «expr = »(ppB', ppB))))],
        { simp [] [] [] ["[", "*", ",", expr «expr $ »(continuants_aux_eq_continuants_aux_squash_gcf_of_le, «expr $ »(le_refl, «expr + »(n', 1))).symm, ",", expr (continuants_aux_eq_continuants_aux_squash_gcf_of_le n'.le_succ).symm, "]"] [] [] },
        symmetry,
        simpa [] [] ["only"] ["[", expr eq1, ",", expr eq2, ",", expr eq3, ",", expr eq4, ",", expr mul_div_cancel _ b_ne_zero, "]"] [] [] },
      field_simp [] [] [] [],
      congr' [1] []; ring [] } }
end

end Squash

-- error in Algebra.ContinuedFractions.ConvergentsEquiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Shows that the recurrence relation (`convergents`) and direct evaluation (`convergents'`) of the
gcf coincide at position `n` if the sequence of fractions contains strictly positive values only.
Requiring positivity of all values is just one possible condition to obtain this result.
For example, the dual - sequences with strictly negative values only - would also work.

In practice, one most commonly deals with (regular) continued fractions, which satisfy the
positivity criterion required here. The analogous result for them
(see `continued_fractions.convergents_eq_convergents`) hence follows directly from this theorem.
-/
theorem convergents_eq_convergents'
[linear_ordered_field K]
(s_pos : ∀
 {gp : pair K}
 {m : exprℕ()}, «expr < »(m, n) → «expr = »(g.s.nth m, some gp) → «expr ∧ »(«expr < »(0, gp.a), «expr < »(0, gp.b))) : «expr = »(g.convergents n, g.convergents' n) :=
begin
  induction [expr n] [] ["with", ident n, ident IH] ["generalizing", ident g],
  case [ident nat.zero] { simp [] [] [] [] [] [] },
  case [ident nat.succ] { let [ident g'] [] [":=", expr squash_gcf g n],
    suffices [] [":", expr «expr = »(g.convergents «expr + »(n, 1), g'.convergents' n)],
    by rwa ["[", expr succ_nth_convergent'_eq_squash_gcf_nth_convergent', "]"] [],
    cases [expr decidable.em (terminated_at g n)] ["with", ident terminated_at_n, ident not_terminated_at_n],
    { have [ident g'_eq_g] [":", expr «expr = »(g', g)] [],
      from [expr squash_gcf_eq_self_of_terminated terminated_at_n],
      rw ["[", expr convergents_stable_of_terminated n.le_succ terminated_at_n, ",", expr g'_eq_g, ",", expr IH _, "]"] [],
      assume [binders (_ _ m_lt_n s_mth_eq)],
      exact [expr s_pos (nat.lt.step m_lt_n) s_mth_eq] },
    { suffices [] [":", expr «expr = »(g.convergents «expr + »(n, 1), g'.convergents n)],
      by { rwa ["<-", expr IH] [],
        assume [binders (gp' m m_lt_n s_mth_eq')],
        cases [expr m_lt_n] ["with", ident n, ident succ_m_lt_n],
        { obtain ["⟨", ident gp_succ_m, ",", ident s_succ_mth_eq, "⟩", ":", expr «expr∃ , »((gp_succ_m), «expr = »(g.s.nth «expr + »(m, 1), some gp_succ_m))],
          from [expr option.ne_none_iff_exists'.mp not_terminated_at_n],
          obtain ["⟨", ident gp_m, ",", ident mth_s_eq, "⟩", ":", expr «expr∃ , »((gp_m), «expr = »(g.s.nth m, some gp_m))],
          from [expr g.s.ge_stable m.le_succ s_succ_mth_eq],
          suffices [] [":", expr «expr ∧ »(«expr < »(0, gp_m.a), «expr < »(0, «expr + »(gp_m.b, «expr / »(gp_succ_m.a, gp_succ_m.b))))],
          by { have [ident ot] [":", expr «expr = »(g'.s.nth m, some ⟨gp_m.a, «expr + »(gp_m.b, «expr / »(gp_succ_m.a, gp_succ_m.b))⟩)] [],
            from [expr squash_seq_nth_of_not_terminated mth_s_eq s_succ_mth_eq],
            have [] [":", expr «expr = »(gp', ⟨gp_m.a, «expr + »(gp_m.b, «expr / »(gp_succ_m.a, gp_succ_m.b))⟩)] [],
            by cc,
            rwa [expr this] [] },
          refine [expr ⟨(s_pos (nat.lt.step m_lt_n) mth_s_eq).left, _⟩],
          refine [expr add_pos (s_pos (nat.lt.step m_lt_n) mth_s_eq).right _],
          have [] [":", expr «expr ∧ »(«expr < »(0, gp_succ_m.a), «expr < »(0, gp_succ_m.b))] [":=", expr s_pos «expr $ »(lt_add_one, «expr + »(m, 1)) s_succ_mth_eq],
          exact [expr div_pos this.left this.right] },
        { refine [expr s_pos «expr $ »(nat.lt.step, nat.lt.step succ_m_lt_n) _],
          exact [expr eq.trans (squash_gcf_nth_of_lt succ_m_lt_n).symm s_mth_eq'] } },
      have [] [":", expr ∀ {{b}}, «expr = »(g.partial_denominators.nth n, some b) → «expr ≠ »(b, 0)] [],
      by { assume [binders (b nth_part_denom_eq)],
        obtain ["⟨", ident gp, ",", ident s_nth_eq, ",", "⟨", ident refl, "⟩", "⟩", ":", expr «expr∃ , »((gp), «expr ∧ »(«expr = »(g.s.nth n, some gp), «expr = »(gp.b, b)))],
        from [expr exists_s_b_of_part_denom nth_part_denom_eq],
        exact [expr (ne_of_lt (s_pos (lt_add_one n) s_nth_eq).right).symm] },
      exact [expr succ_nth_convergent_eq_squash_gcf_nth_convergent this] } }
end

end GeneralizedContinuedFraction

open GeneralizedContinuedFraction

namespace ContinuedFraction

/-- Shows that the recurrence relation (`convergents`) and direct evaluation (`convergents'`) of a
(regular) continued fraction coincide. -/
theorem convergents_eq_convergents' [LinearOrderedField K] {c : ContinuedFraction K} :
  («expr↑ » c : GeneralizedContinuedFraction K).convergents =
    («expr↑ » c : GeneralizedContinuedFraction K).convergents' :=
  by 
    ext n 
    apply convergents_eq_convergents' 
    intro gp m m_lt_n s_nth_eq 
    exact
      ⟨zero_lt_one.trans_le ((c : SimpleContinuedFraction K).property m gp.a (part_num_eq_s_a s_nth_eq)).symm.le,
        c.property m gp.b$ part_denom_eq_s_b s_nth_eq⟩

end ContinuedFraction

