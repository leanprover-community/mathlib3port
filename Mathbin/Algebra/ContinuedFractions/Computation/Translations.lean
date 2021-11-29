import Mathbin.Algebra.ContinuedFractions.Computation.Basic 
import Mathbin.Algebra.ContinuedFractions.Translations

/-!
# Basic Translation Lemmas Between Structures Defined for Computing Continued Fractions

## Summary

This is a collection of simple lemmas between the different structures used for the computation
of continued fractions defined in `algebra.continued_fractions.computation.basic`. The file consists
of three sections:
1. Recurrences and inversion lemmas for `int_fract_pair.stream`: these lemmas give us inversion
   rules and recurrences for the computation of the stream of integer and fractional parts of
   a value.
2. Translation lemmas for the head term: these lemmas show us that the head term of the computed
   continued fraction of a value `v` is `⌊v⌋` and how this head term is moved along the structures
   used in the computation process.
3. Translation lemmas for the sequence: these lemmas show how the sequences of the involved
   structures (`int_fract_pair.stream`, `int_fract_pair.seq1`, and
   `generalized_continued_fraction.of`) are connected, i.e. how the values are moved along the
   structures and the termination of one sequence implies the termination of another sequence.

## Main Theorems

- `succ_nth_stream_eq_some_iff` gives as a recurrence to compute the `n + 1`th value of the sequence
  of integer and fractional parts of a value in case of non-termination.
- `succ_nth_stream_eq_none_iff` gives as a recurrence to compute the `n + 1`th value of the sequence
  of integer and fractional parts of a value in case of termination.
- `nth_of_eq_some_of_succ_nth_int_fract_pair_stream` and
  `nth_of_eq_some_of_nth_int_fract_pair_stream_fr_ne_zero` show how the entries of the sequence
  of the computed continued fraction can be obtained from the stream of integer and fractional
  parts.
-/


namespace GeneralizedContinuedFraction

open generalized_continued_fraction(of)

variable {K : Type _} [LinearOrderedField K] [FloorRing K] {v : K}

namespace IntFractPair

/-!
### Recurrences and Inversion Lemmas for `int_fract_pair.stream`

Here we state some lemmas that give us inversion rules and recurrences for the computation of the
stream of integer and fractional parts of a value.
-/


variable {n : ℕ}

theorem stream_eq_none_of_fr_eq_zero {ifp_n : int_fract_pair K} (stream_nth_eq : int_fract_pair.stream v n = some ifp_n)
  (nth_fr_eq_zero : ifp_n.fr = 0) : int_fract_pair.stream v (n+1) = none :=
  by 
    cases' ifp_n with _ fr 
    change fr = 0 at nth_fr_eq_zero 
    simp [int_fract_pair.stream, stream_nth_eq, nth_fr_eq_zero]

/--
Gives a recurrence to compute the `n + 1`th value of the sequence of integer and fractional
parts of a value in case of termination.
-/
theorem succ_nth_stream_eq_none_iff :
  int_fract_pair.stream v (n+1) = none ↔
    int_fract_pair.stream v n = none ∨ ∃ ifp, int_fract_pair.stream v n = some ifp ∧ ifp.fr = 0 :=
  by 
    cases' stream_nth_eq : int_fract_pair.stream v n with ifp 
    case option.none => 
      simp [stream_nth_eq, int_fract_pair.stream]
    case option.some => 
      cases' ifp with _ fr 
      cases Decidable.em (fr = 0) <;> finish [int_fract_pair.stream]

-- error in Algebra.ContinuedFractions.Computation.Translations: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Gives a recurrence to compute the `n + 1`th value of the sequence of integer and fractional
parts of a value in case of non-termination.
-/
theorem succ_nth_stream_eq_some_iff
{ifp_succ_n : int_fract_pair K} : «expr ↔ »(«expr = »(int_fract_pair.stream v «expr + »(n, 1), some ifp_succ_n), «expr∃ , »((ifp_n : int_fract_pair K), «expr ∧ »(«expr = »(int_fract_pair.stream v n, some ifp_n), «expr ∧ »(«expr ≠ »(ifp_n.fr, 0), «expr = »(int_fract_pair.of «expr ⁻¹»(ifp_n.fr), ifp_succ_n))))) :=
begin
  split,
  { assume [binders (stream_succ_nth_eq)],
    have [] [":", expr «expr ≠ »(int_fract_pair.stream v «expr + »(n, 1), none)] [],
    by simp [] [] [] ["[", expr stream_succ_nth_eq, "]"] [] [],
    have [] [":", expr «expr ∧ »(«expr¬ »(«expr = »(int_fract_pair.stream v n, none)), «expr¬ »(«expr∃ , »((ifp), «expr ∧ »(«expr = »(int_fract_pair.stream v n, some ifp), «expr = »(ifp.fr, 0)))))] [],
    by { have [ident not_none_not_fract_zero] [] [],
      from [expr (not_iff_not_of_iff succ_nth_stream_eq_none_iff).elim_left this],
      exact [expr not_or_distrib.elim_left not_none_not_fract_zero] },
    cases [expr this] ["with", ident stream_nth_ne_none, ident nth_fr_ne_zero],
    replace [ident nth_fr_ne_zero] [":", expr ∀
     ifp, «expr = »(int_fract_pair.stream v n, some ifp) → «expr ≠ »(ifp.fr, 0)] [],
    by simpa [] [] [] [] [] ["using", expr nth_fr_ne_zero],
    obtain ["⟨", ident ifp_n, ",", ident stream_nth_eq, "⟩", ":", expr «expr∃ , »((ifp_n), «expr = »(int_fract_pair.stream v n, some ifp_n))],
    from [expr option.ne_none_iff_exists'.mp stream_nth_ne_none],
    existsi [expr ifp_n],
    have [ident ifp_n_fr_ne_zero] [":", expr «expr ≠ »(ifp_n.fr, 0)] [],
    from [expr nth_fr_ne_zero ifp_n stream_nth_eq],
    cases [expr ifp_n] ["with", "_", ident ifp_n_fr],
    suffices [] [":", expr «expr = »(int_fract_pair.of «expr ⁻¹»(ifp_n_fr), ifp_succ_n)],
    by simpa [] [] [] ["[", expr stream_nth_eq, ",", expr ifp_n_fr_ne_zero, "]"] [] [],
    simp [] [] ["only"] ["[", expr int_fract_pair.stream, ",", expr stream_nth_eq, ",", expr ifp_n_fr_ne_zero, ",", expr option.some_bind, ",", expr if_false, "]"] [] ["at", ident stream_succ_nth_eq],
    injection [expr stream_succ_nth_eq] [] },
  { rintro ["⟨", "⟨", "_", "⟩", ",", ident ifp_n_props, "⟩"],
    finish ["[", expr int_fract_pair.stream, ",", expr ifp_n_props, "]"] [] }
end

-- error in Algebra.ContinuedFractions.Computation.Translations: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_succ_nth_stream_of_fr_zero
{ifp_succ_n : int_fract_pair K}
(stream_succ_nth_eq : «expr = »(int_fract_pair.stream v «expr + »(n, 1), some ifp_succ_n))
(succ_nth_fr_eq_zero : «expr = »(ifp_succ_n.fr, 0)) : «expr∃ , »((ifp_n : int_fract_pair K), «expr ∧ »(«expr = »(int_fract_pair.stream v n, some ifp_n), «expr = »(«expr ⁻¹»(ifp_n.fr), «expr⌊ ⌋»(«expr ⁻¹»(ifp_n.fr))))) :=
begin
  rcases [expr succ_nth_stream_eq_some_iff.elim_left stream_succ_nth_eq, "with", "⟨", ident ifp_n, ",", ident stream_nth_eq, ",", ident nth_fr_ne_zero, ",", "_", "⟩"],
  existsi [expr ifp_n],
  cases [expr ifp_n] ["with", "_", ident ifp_n_fr],
  suffices [] [":", expr «expr = »(«expr ⁻¹»(ifp_n_fr), «expr⌊ ⌋»(«expr ⁻¹»(ifp_n_fr)))],
  by simpa [] [] [] ["[", expr stream_nth_eq, "]"] [] [],
  have [] [":", expr «expr = »(int_fract_pair.of «expr ⁻¹»(ifp_n_fr), ifp_succ_n)] [],
  by finish [] [],
  cases [expr ifp_succ_n] ["with", "_", ident ifp_succ_n_fr],
  change [expr «expr = »(ifp_succ_n_fr, 0)] [] ["at", ident succ_nth_fr_eq_zero],
  have [] [":", expr «expr = »(int.fract «expr ⁻¹»(ifp_n_fr), ifp_succ_n_fr)] [],
  by injection [expr this] [],
  have [] [":", expr «expr = »(int.fract «expr ⁻¹»(ifp_n_fr), 0)] [],
  by rwa ["[", expr succ_nth_fr_eq_zero, "]"] ["at", ident this],
  calc
    «expr = »(«expr ⁻¹»(ifp_n_fr), «expr + »(int.fract «expr ⁻¹»(ifp_n_fr), «expr⌊ ⌋»(«expr ⁻¹»(ifp_n_fr)))) : by rw [expr int.fract_add_floor «expr ⁻¹»(ifp_n_fr)] []
    «expr = »(..., «expr⌊ ⌋»(«expr ⁻¹»(ifp_n_fr))) : by simp [] [] [] ["[", expr «expr‹ ›»(«expr = »(int.fract «expr ⁻¹»(ifp_n_fr), 0)), "]"] [] []
end

end IntFractPair

section Head

/-!
### Translation of the Head Term

Here we state some lemmas that show us that the head term of the computed continued fraction of a
value `v` is `⌊v⌋` and how this head term is moved along the structures used in the computation
process.
-/


/-- The head term of the sequence with head of `v` is just the integer part of `v`. -/
@[simp]
theorem int_fract_pair.seq1_fst_eq_of : (int_fract_pair.seq1 v).fst = int_fract_pair.of v :=
  rfl

theorem of_h_eq_int_fract_pair_seq1_fst_b : (of v).h = (int_fract_pair.seq1 v).fst.b :=
  by 
    cases aux_seq_eq : int_fract_pair.seq1 v 
    simp [of, aux_seq_eq]

/-- The head term of the gcf of `v` is `⌊v⌋`. -/
@[simp]
theorem of_h_eq_floor : (of v).h = ⌊v⌋ :=
  by 
    simp [of_h_eq_int_fract_pair_seq1_fst_b, int_fract_pair.of]

end Head

section sequence

/-!
### Translation of the Sequences

Here we state some lemmas that show how the sequences of the involved structures
(`int_fract_pair.stream`, `int_fract_pair.seq1`, and `generalized_continued_fraction.of`) are
connected, i.e. how the values are moved along the structures and how the termination of one
sequence implies the termination of another sequence.
-/


variable {n : ℕ}

theorem int_fract_pair.nth_seq1_eq_succ_nth_stream :
  (int_fract_pair.seq1 v).snd.nth n = (int_fract_pair.stream v) (n+1) :=
  rfl

section Termination

/-!
#### Translation of the Termination of the Sequences

Let's first show how the termination of one sequence implies the termination of another sequence.
-/


theorem of_terminated_at_iff_int_fract_pair_seq1_terminated_at :
  (of v).TerminatedAt n ↔ (int_fract_pair.seq1 v).snd.TerminatedAt n :=
  by 
    rw [terminated_at_iff_s_none, of]
    rcases int_fract_pair.seq1 v with ⟨head, ⟨st⟩⟩
    cases st_n_eq : st n <;> simp [of, st_n_eq, Seqₓₓ.map, Seqₓₓ.nth, Streamₓ.map, Seqₓₓ.TerminatedAt, Streamₓ.nth]

theorem of_terminated_at_n_iff_succ_nth_int_fract_pair_stream_eq_none :
  (of v).TerminatedAt n ↔ int_fract_pair.stream v (n+1) = none :=
  by 
    rw [of_terminated_at_iff_int_fract_pair_seq1_terminated_at, Seqₓₓ.TerminatedAt,
      int_fract_pair.nth_seq1_eq_succ_nth_stream]

end Termination

section Values

/-!
#### Translation of the Values of the Sequence

Now let's show how the values of the sequences correspond to one another.
-/


theorem int_fract_pair.exists_succ_nth_stream_of_gcf_of_nth_eq_some {gp_n : pair K}
  (s_nth_eq : (of v).s.nth n = some gp_n) :
  ∃ ifp : int_fract_pair K, int_fract_pair.stream v (n+1) = some ifp ∧ (ifp.b : K) = gp_n.b :=
  by 
    obtain ⟨ifp, stream_succ_nth_eq, gp_n_eq⟩ :
      ∃ ifp, int_fract_pair.stream v (n+1) = some ifp ∧ pair.mk 1 (ifp.b : K) = gp_n
    ·
      ·
        unfold of int_fract_pair.seq1  at s_nth_eq 
        rwa [Seqₓₓ.map_tail, Seqₓₓ.nth_tail, Seqₓₓ.map_nth, Option.map_eq_some'] at s_nth_eq 
    cases gp_n_eq 
    injection gp_n_eq with _ ifp_b_eq_gp_n_b 
    exists ifp 
    exact ⟨stream_succ_nth_eq, ifp_b_eq_gp_n_b⟩

/--
Shows how the entries of the sequence of the computed continued fraction can be obtained by the
integer parts of the stream of integer and fractional parts.
-/
theorem nth_of_eq_some_of_succ_nth_int_fract_pair_stream {ifp_succ_n : int_fract_pair K}
  (stream_succ_nth_eq : int_fract_pair.stream v (n+1) = some ifp_succ_n) : (of v).s.nth n = some ⟨1, ifp_succ_n.b⟩ :=
  by 
    unfold of int_fract_pair.seq1 
    rw [Seqₓₓ.map_tail, Seqₓₓ.nth_tail, Seqₓₓ.map_nth]
    simp [Seqₓₓ.nth, stream_succ_nth_eq]

/--
Shows how the entries of the sequence of the computed continued fraction can be obtained by the
fractional parts of the stream of integer and fractional parts.
-/
theorem nth_of_eq_some_of_nth_int_fract_pair_stream_fr_ne_zero {ifp_n : int_fract_pair K}
  (stream_nth_eq : int_fract_pair.stream v n = some ifp_n) (nth_fr_ne_zero : ifp_n.fr ≠ 0) :
  (of v).s.nth n = some ⟨1, (int_fract_pair.of (ifp_n.fr⁻¹)).b⟩ :=
  have  : int_fract_pair.stream v (n+1) = some (int_fract_pair.of (ifp_n.fr⁻¹)) :=
    by 
      cases ifp_n 
      simp [int_fract_pair.stream, stream_nth_eq, nth_fr_ne_zero]
      rfl 
  nth_of_eq_some_of_succ_nth_int_fract_pair_stream this

end Values

end sequence

end GeneralizedContinuedFraction

