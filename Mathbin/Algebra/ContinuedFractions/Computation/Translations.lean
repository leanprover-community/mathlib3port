/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann

! This file was ported from Lean 3 source module algebra.continued_fractions.computation.translations
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
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

open GeneralizedContinuedFraction (of)

-- Fix a discrete linear ordered floor field and a value `v`.
variable {K : Type _} [LinearOrderedField K] [FloorRing K] {v : K}

namespace IntFractPair

/-!
### Recurrences and Inversion Lemmas for `int_fract_pair.stream`

Here we state some lemmas that give us inversion rules and recurrences for the computation of the
stream of integer and fractional parts of a value.
-/


variable {n : ℕ}

theorem stream_eq_none_of_fr_eq_zero {ifp_n : IntFractPair K}
    (stream_nth_eq : IntFractPair.stream v n = some ifp_n) (nth_fr_eq_zero : ifp_n.fr = 0) :
    IntFractPair.stream v (n + 1) = none :=
  by
  cases' ifp_n with _ fr
  change fr = 0 at nth_fr_eq_zero
  simp [int_fract_pair.stream, stream_nth_eq, nth_fr_eq_zero]
#align generalized_continued_fraction.int_fract_pair.stream_eq_none_of_fr_eq_zero GeneralizedContinuedFraction.IntFractPair.stream_eq_none_of_fr_eq_zero

/-- Gives a recurrence to compute the `n + 1`th value of the sequence of integer and fractional
parts of a value in case of termination.
-/
theorem succ_nth_stream_eq_none_iff :
    IntFractPair.stream v (n + 1) = none ↔
      IntFractPair.stream v n = none ∨ ∃ ifp, IntFractPair.stream v n = some ifp ∧ ifp.fr = 0 :=
  by
  rw [int_fract_pair.stream]
  cases int_fract_pair.stream v n <;> simp [imp_false]
#align generalized_continued_fraction.int_fract_pair.succ_nth_stream_eq_none_iff GeneralizedContinuedFraction.IntFractPair.succ_nth_stream_eq_none_iff

/-- Gives a recurrence to compute the `n + 1`th value of the sequence of integer and fractional
parts of a value in case of non-termination.
-/
theorem succ_nth_stream_eq_some_iff {ifp_succ_n : IntFractPair K} :
    IntFractPair.stream v (n + 1) = some ifp_succ_n ↔
      ∃ ifp_n : IntFractPair K,
        IntFractPair.stream v n = some ifp_n ∧
          ifp_n.fr ≠ 0 ∧ IntFractPair.of ifp_n.fr⁻¹ = ifp_succ_n :=
  by simp [int_fract_pair.stream, ite_eq_iff]
#align generalized_continued_fraction.int_fract_pair.succ_nth_stream_eq_some_iff GeneralizedContinuedFraction.IntFractPair.succ_nth_stream_eq_some_iff

theorem exists_succ_nth_stream_of_fr_zero {ifp_succ_n : IntFractPair K}
    (stream_succ_nth_eq : IntFractPair.stream v (n + 1) = some ifp_succ_n)
    (succ_nth_fr_eq_zero : ifp_succ_n.fr = 0) :
    ∃ ifp_n : IntFractPair K, IntFractPair.stream v n = some ifp_n ∧ ifp_n.fr⁻¹ = ⌊ifp_n.fr⁻¹⌋ :=
  by
  -- get the witness from `succ_nth_stream_eq_some_iff` and prove that it has the additional
  -- properties
  rcases succ_nth_stream_eq_some_iff.mp stream_succ_nth_eq with
    ⟨ifp_n, seq_nth_eq, nth_fr_ne_zero, rfl⟩
  refine' ⟨ifp_n, seq_nth_eq, _⟩
  simpa only [int_fract_pair.of, Int.fract, sub_eq_zero] using succ_nth_fr_eq_zero
#align generalized_continued_fraction.int_fract_pair.exists_succ_nth_stream_of_fr_zero GeneralizedContinuedFraction.IntFractPair.exists_succ_nth_stream_of_fr_zero

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
theorem IntFractPair.seq1_fst_eq_of : (IntFractPair.seq1 v).fst = IntFractPair.of v :=
  rfl
#align generalized_continued_fraction.int_fract_pair.seq1_fst_eq_of GeneralizedContinuedFraction.IntFractPair.seq1_fst_eq_of

theorem of_h_eq_intFractPair_seq1_fst_b : (of v).h = (IntFractPair.seq1 v).fst.b :=
  by
  cases aux_seq_eq : int_fract_pair.seq1 v
  simp [of, aux_seq_eq]
#align generalized_continued_fraction.of_h_eq_int_fract_pair_seq1_fst_b GeneralizedContinuedFraction.of_h_eq_intFractPair_seq1_fst_b

/-- The head term of the gcf of `v` is `⌊v⌋`. -/
@[simp]
theorem of_h_eq_floor : (of v).h = ⌊v⌋ := by
  simp [of_h_eq_int_fract_pair_seq1_fst_b, int_fract_pair.of]
#align generalized_continued_fraction.of_h_eq_floor GeneralizedContinuedFraction.of_h_eq_floor

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

theorem IntFractPair.nth_seq1_eq_succ_nth_stream :
    (IntFractPair.seq1 v).snd.nth n = (IntFractPair.stream v) (n + 1) :=
  rfl
#align generalized_continued_fraction.int_fract_pair.nth_seq1_eq_succ_nth_stream GeneralizedContinuedFraction.IntFractPair.nth_seq1_eq_succ_nth_stream

section Termination

/-!
#### Translation of the Termination of the Sequences

Let's first show how the termination of one sequence implies the termination of another sequence.
-/


theorem of_terminatedAt_iff_intFractPair_seq1_terminatedAt :
    (of v).TerminatedAt n ↔ (IntFractPair.seq1 v).snd.TerminatedAt n :=
  Option.map_eq_none
#align generalized_continued_fraction.of_terminated_at_iff_int_fract_pair_seq1_terminated_at GeneralizedContinuedFraction.of_terminatedAt_iff_intFractPair_seq1_terminatedAt

theorem of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none :
    (of v).TerminatedAt n ↔ IntFractPair.stream v (n + 1) = none := by
  rw [of_terminated_at_iff_int_fract_pair_seq1_terminated_at, Seq.TerminatedAt,
    int_fract_pair.nth_seq1_eq_succ_nth_stream]
#align generalized_continued_fraction.of_terminated_at_n_iff_succ_nth_int_fract_pair_stream_eq_none GeneralizedContinuedFraction.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none

end Termination

section Values

/-!
#### Translation of the Values of the Sequence

Now let's show how the values of the sequences correspond to one another.
-/


theorem IntFractPair.exists_succ_nth_stream_of_gcf_of_nth_eq_some {gp_n : Pair K}
    (s_nth_eq : (of v).s.nth n = some gp_n) :
    ∃ ifp : IntFractPair K, IntFractPair.stream v (n + 1) = some ifp ∧ (ifp.b : K) = gp_n.b :=
  by
  obtain ⟨ifp, stream_succ_nth_eq, gp_n_eq⟩ :
    ∃ ifp, int_fract_pair.stream v (n + 1) = some ifp ∧ pair.mk 1 (ifp.b : K) = gp_n :=
    by
    unfold of int_fract_pair.seq1 at s_nth_eq
    rwa [Seq.map_tail, Seq.nth_tail, Seq.map_nth, Option.map_eq_some'] at s_nth_eq
  cases gp_n_eq
  injection gp_n_eq with _ ifp_b_eq_gp_n_b
  exists ifp
  exact ⟨stream_succ_nth_eq, ifp_b_eq_gp_n_b⟩
#align generalized_continued_fraction.int_fract_pair.exists_succ_nth_stream_of_gcf_of_nth_eq_some GeneralizedContinuedFraction.IntFractPair.exists_succ_nth_stream_of_gcf_of_nth_eq_some

/-- Shows how the entries of the sequence of the computed continued fraction can be obtained by the
integer parts of the stream of integer and fractional parts.
-/
theorem nth_of_eq_some_of_succ_nth_intFractPair_stream {ifp_succ_n : IntFractPair K}
    (stream_succ_nth_eq : IntFractPair.stream v (n + 1) = some ifp_succ_n) :
    (of v).s.nth n = some ⟨1, ifp_succ_n.b⟩ :=
  by
  unfold of int_fract_pair.seq1
  rw [Seq.map_tail, Seq.nth_tail, Seq.map_nth]
  simp [Seq.nth, stream_succ_nth_eq]
#align generalized_continued_fraction.nth_of_eq_some_of_succ_nth_int_fract_pair_stream GeneralizedContinuedFraction.nth_of_eq_some_of_succ_nth_intFractPair_stream

/-- Shows how the entries of the sequence of the computed continued fraction can be obtained by the
fractional parts of the stream of integer and fractional parts.
-/
theorem nth_of_eq_some_of_nth_intFractPair_stream_fr_ne_zero {ifp_n : IntFractPair K}
    (stream_nth_eq : IntFractPair.stream v n = some ifp_n) (nth_fr_ne_zero : ifp_n.fr ≠ 0) :
    (of v).s.nth n = some ⟨1, (IntFractPair.of ifp_n.fr⁻¹).b⟩ :=
  have : IntFractPair.stream v (n + 1) = some (IntFractPair.of ifp_n.fr⁻¹) :=
    by
    cases ifp_n
    simp [int_fract_pair.stream, stream_nth_eq, nth_fr_ne_zero]
  nth_of_eq_some_of_succ_nth_intFractPair_stream this
#align generalized_continued_fraction.nth_of_eq_some_of_nth_int_fract_pair_stream_fr_ne_zero GeneralizedContinuedFraction.nth_of_eq_some_of_nth_intFractPair_stream_fr_ne_zero

end Values

end sequence

end GeneralizedContinuedFraction

