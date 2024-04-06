/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Algebra.Order.Chebyshev
import Analysis.SpecialFunctions.Pow.Real
import Order.Partition.Equipartition

#align_import combinatorics.simple_graph.regularity.bound from "leanprover-community/mathlib"@"08b63ab58a6ec1157ebeafcbbe6c7a3fb3c9f6d5"

/-!
# Numerical bounds for Szemerédi Regularity Lemma

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file gathers the numerical facts required by the proof of Szemerédi's regularity lemma.

This entire file is internal to the proof of Szemerédi Regularity Lemma.

## Main declarations

* `szemeredi_regularity.step_bound`: During the inductive step, a partition of size `n` is blown to
  size at most `step_bound n`.
* `szemeredi_regularity.initial_bound`: The size of the partition we start the induction with.
* `szemeredi_regularity.bound`: The upper bound on the size of the partition produced by our version
  of Szemerédi's regularity lemma.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/


open Finset Fintype Function Real

open scoped BigOperators

namespace szemeredi_regularity

#print SzemerediRegularity.stepBound /-
/-- Auxiliary function for Szemerédi's regularity lemma. Blowing up a partition of size `n` during
the induction results in a partition of size at most `step_bound n`. -/
def stepBound (n : ℕ) : ℕ :=
  n * 4 ^ n
#align szemeredi_regularity.step_bound SzemerediRegularity.stepBound
-/

#print SzemerediRegularity.le_stepBound /-
theorem le_stepBound : id ≤ stepBound := fun n => Nat.le_mul_of_pos_right <| pow_pos (by norm_num) n
#align szemeredi_regularity.le_step_bound SzemerediRegularity.le_stepBound
-/

#print SzemerediRegularity.stepBound_mono /-
theorem stepBound_mono : Monotone stepBound := fun a b h =>
  Nat.mul_le_mul h <| Nat.pow_le_pow_right (by norm_num) h
#align szemeredi_regularity.step_bound_mono SzemerediRegularity.stepBound_mono
-/

#print SzemerediRegularity.stepBound_pos_iff /-
theorem stepBound_pos_iff {n : ℕ} : 0 < stepBound n ↔ 0 < n :=
  mul_pos_iff_of_pos_right <| by positivity
#align szemeredi_regularity.step_bound_pos_iff SzemerediRegularity.stepBound_pos_iff
-/

alias ⟨_, step_bound_pos⟩ := step_bound_pos_iff
#align szemeredi_regularity.step_bound_pos SzemerediRegularity.stepBound_pos

end szemeredi_regularity

open szemeredi_regularity

variable {α : Type _} [DecidableEq α] [Fintype α] {P : Finpartition (univ : Finset α)}
  {u : Finset α} {ε : ℝ}

local notation "m" => (card α / stepBound P.parts.card : ℕ)

local notation "a" => (card α / P.parts.card - m * 4 ^ P.parts.card : ℕ)

namespace Tactic

open Positivity

private theorem eps_pos {ε : ℝ} {n : ℕ} (h : 100 ≤ 4 ^ n * ε ^ 5) : 0 < ε :=
  pow_bit1_pos_iff.1 <| pos_of_mul_pos_right (h.trans_lt' <| by norm_num) <| by positivity

private theorem m_pos [Nonempty α] (hPα : P.parts.card * 16 ^ P.parts.card ≤ card α) : 0 < m :=
  Nat.div_pos ((Nat.mul_le_mul_left _ <| Nat.pow_le_pow_left (by norm_num) _).trans hPα) <|
    stepBound_pos (P.parts_nonempty <| univ_nonempty.ne_empty).card_pos

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      Local extension for the `positivity` tactic: A few facts that are needed many times for the
      proof of Szemerédi's regularity lemma. -/
    unsafe
  def
    positivity_szemeredi_regularity
    : expr → tactic strictness
    |
        q( $ ( n ) / stepBound ( Finpartition.parts $ ( P ) ) . card )
        =>
        do
          let
              p
                ←
                to_expr
                    `
                      `(
                        ( Finpartition.parts $ ( P ) ) . card
                            *
                            16 ^ ( Finpartition.parts $ ( P ) ) . card
                          ≤
                          $ ( n )
                        )
                  >>=
                  find_assumption
            positive <$> mk_app ` ` m_pos [ p ]
      |
        ε
        =>
        do
          let typ ← infer_type ε
            unify typ q( ℝ )
            let p ← to_expr ` `( 100 ≤ 4 ^ _ * $ ( ε ) ^ 5 ) >>= find_assumption
            positive <$> mk_app ` ` eps_pos [ p ]
#align tactic.positivity_szemeredi_regularity tactic.positivity_szemeredi_regularity

end Tactic

attribute [local positivity] tactic.positivity_szemeredi_regularity

namespace szemeredi_regularity

#print SzemerediRegularity.m_pos /-
theorem m_pos [Nonempty α] (hPα : P.parts.card * 16 ^ P.parts.card ≤ card α) : 0 < m := by
  positivity
#align szemeredi_regularity.m_pos SzemerediRegularity.m_pos
-/

#print SzemerediRegularity.coe_m_add_one_pos /-
theorem coe_m_add_one_pos : 0 < (m : ℝ) + 1 := by positivity
#align szemeredi_regularity.coe_m_add_one_pos SzemerediRegularity.coe_m_add_one_pos
-/

#print SzemerediRegularity.one_le_m_coe /-
theorem one_le_m_coe [Nonempty α] (hPα : P.parts.card * 16 ^ P.parts.card ≤ card α) : (1 : ℝ) ≤ m :=
  Nat.one_le_cast.2 <| m_pos hPα
#align szemeredi_regularity.one_le_m_coe SzemerediRegularity.one_le_m_coe
-/

#print SzemerediRegularity.eps_pow_five_pos /-
theorem eps_pow_five_pos (hPε : 100 ≤ 4 ^ P.parts.card * ε ^ 5) : 0 < ε ^ 5 :=
  pos_of_mul_pos_right ((by norm_num : (0 : ℝ) < 100).trans_le hPε) <| pow_nonneg (by norm_num) _
#align szemeredi_regularity.eps_pow_five_pos SzemerediRegularity.eps_pow_five_pos
-/

#print SzemerediRegularity.eps_pos /-
theorem eps_pos (hPε : 100 ≤ 4 ^ P.parts.card * ε ^ 5) : 0 < ε :=
  pow_bit1_pos_iff.1 <| eps_pow_five_pos hPε
#align szemeredi_regularity.eps_pos SzemerediRegularity.eps_pos
-/

#print SzemerediRegularity.hundred_div_ε_pow_five_le_m /-
theorem hundred_div_ε_pow_five_le_m [Nonempty α] (hPα : P.parts.card * 16 ^ P.parts.card ≤ card α)
    (hPε : 100 ≤ 4 ^ P.parts.card * ε ^ 5) : 100 / ε ^ 5 ≤ m :=
  (div_le_of_nonneg_of_le_mul (eps_pow_five_pos hPε).le (by positivity) hPε).trans
    (by
      norm_cast
      rwa [Nat.le_div_iff_mul_le'
          (step_bound_pos (P.parts_nonempty <| univ_nonempty.ne_empty).card_pos),
        step_bound, mul_left_comm, ← mul_pow])
#align szemeredi_regularity.hundred_div_ε_pow_five_le_m SzemerediRegularity.hundred_div_ε_pow_five_le_m
-/

#print SzemerediRegularity.hundred_le_m /-
theorem hundred_le_m [Nonempty α] (hPα : P.parts.card * 16 ^ P.parts.card ≤ card α)
    (hPε : 100 ≤ 4 ^ P.parts.card * ε ^ 5) (hε : ε ≤ 1) : 100 ≤ m := by
  exact_mod_cast
    (hundred_div_ε_pow_five_le_m hPα hPε).trans'
      (le_div_self (by norm_num) (by positivity) <| pow_le_one _ (by positivity) hε)
#align szemeredi_regularity.hundred_le_m SzemerediRegularity.hundred_le_m
-/

#print SzemerediRegularity.a_add_one_le_four_pow_parts_card /-
theorem a_add_one_le_four_pow_parts_card : a + 1 ≤ 4 ^ P.parts.card :=
  by
  have h : 1 ≤ 4 ^ P.parts.card := one_le_pow_of_one_le (by norm_num) _
  rw [step_bound, ← Nat.div_div_eq_div_mul, ← Nat.le_sub_iff_add_le h, tsub_le_iff_left, ←
    Nat.add_sub_assoc h]
  exact Nat.le_pred_of_lt (Nat.lt_div_mul_add h)
#align szemeredi_regularity.a_add_one_le_four_pow_parts_card SzemerediRegularity.a_add_one_le_four_pow_parts_card
-/

#print SzemerediRegularity.card_aux₁ /-
theorem card_aux₁ (hucard : u.card = m * 4 ^ P.parts.card + a) :
    (4 ^ P.parts.card - a) * m + a * (m + 1) = u.card := by
  rw [hucard, mul_add, mul_one, ← add_assoc, ← add_mul,
    Nat.sub_add_cancel ((Nat.le_succ _).trans a_add_one_le_four_pow_parts_card), mul_comm]
#align szemeredi_regularity.card_aux₁ SzemerediRegularity.card_aux₁
-/

#print SzemerediRegularity.card_aux₂ /-
theorem card_aux₂ (hP : P.IsEquipartition) (hu : u ∈ P.parts)
    (hucard : ¬u.card = m * 4 ^ P.parts.card + a) :
    (4 ^ P.parts.card - (a + 1)) * m + (a + 1) * (m + 1) = u.card :=
  by
  have : m * 4 ^ P.parts.card ≤ card α / P.parts.card :=
    by
    rw [step_bound, ← Nat.div_div_eq_div_mul]
    exact Nat.div_mul_le_self _ _
  rw [Nat.add_sub_of_le this] at hucard
  rw [(hP.card_parts_eq_average hu).resolve_left hucard, mul_add, mul_one, ← add_assoc, ← add_mul,
    Nat.sub_add_cancel a_add_one_le_four_pow_parts_card, ← add_assoc, mul_comm,
    Nat.add_sub_of_le this, card_univ]
#align szemeredi_regularity.card_aux₂ SzemerediRegularity.card_aux₂
-/

#print SzemerediRegularity.pow_mul_m_le_card_part /-
theorem pow_mul_m_le_card_part (hP : P.IsEquipartition) (hu : u ∈ P.parts) :
    (4 : ℝ) ^ P.parts.card * m ≤ u.card := by
  norm_cast
  rw [step_bound, ← Nat.div_div_eq_div_mul]
  exact (Nat.mul_div_le _ _).trans (hP.average_le_card_part hu)
#align szemeredi_regularity.pow_mul_m_le_card_part SzemerediRegularity.pow_mul_m_le_card_part
-/

variable (P ε) (l : ℕ)

#print SzemerediRegularity.initialBound /-
/-- Auxiliary function for Szemerédi's regularity lemma. The size of the partition by which we start
blowing. -/
noncomputable def initialBound : ℕ :=
  max 7 <| max l <| ⌊log (100 / ε ^ 5) / log 4⌋₊ + 1
#align szemeredi_regularity.initial_bound SzemerediRegularity.initialBound
-/

#print SzemerediRegularity.le_initialBound /-
theorem le_initialBound : l ≤ initialBound ε l :=
  (le_max_left _ _).trans <| le_max_right _ _
#align szemeredi_regularity.le_initial_bound SzemerediRegularity.le_initialBound
-/

#print SzemerediRegularity.seven_le_initialBound /-
theorem seven_le_initialBound : 7 ≤ initialBound ε l :=
  le_max_left _ _
#align szemeredi_regularity.seven_le_initial_bound SzemerediRegularity.seven_le_initialBound
-/

#print SzemerediRegularity.initialBound_pos /-
theorem initialBound_pos : 0 < initialBound ε l :=
  Nat.succ_pos'.trans_le <| seven_le_initialBound _ _
#align szemeredi_regularity.initial_bound_pos SzemerediRegularity.initialBound_pos
-/

#print SzemerediRegularity.hundred_lt_pow_initialBound_mul /-
theorem hundred_lt_pow_initialBound_mul {ε : ℝ} (hε : 0 < ε) (l : ℕ) :
    100 < 4 ^ initialBound ε l * ε ^ 5 :=
  by
  rw [← rpow_nat_cast 4, ← div_lt_iff (pow_pos hε 5), lt_rpow_iff_log_lt _ zero_lt_four, ←
    div_lt_iff, initial_bound, Nat.cast_max, Nat.cast_max]
  · push_cast; exact lt_max_of_lt_right (lt_max_of_lt_right <| Nat.lt_floor_add_one _)
  · exact log_pos (by norm_num)
  · exact div_pos (by norm_num) (pow_pos hε 5)
#align szemeredi_regularity.hundred_lt_pow_initial_bound_mul SzemerediRegularity.hundred_lt_pow_initialBound_mul
-/

#print SzemerediRegularity.bound /-
/-- An explicit bound on the size of the equipartition whose existence is given by Szemerédi's
regularity lemma. -/
noncomputable def bound : ℕ :=
  (stepBound^[⌊4 / ε ^ 5⌋₊] <| initialBound ε l) *
    16 ^ (stepBound^[⌊4 / ε ^ 5⌋₊] <| initialBound ε l)
#align szemeredi_regularity.bound SzemerediRegularity.bound
-/

#print SzemerediRegularity.initialBound_le_bound /-
theorem initialBound_le_bound : initialBound ε l ≤ bound ε l :=
  (id_le_iterate_of_id_le le_stepBound _ _).trans <| Nat.le_mul_of_pos_right <| by positivity
#align szemeredi_regularity.initial_bound_le_bound SzemerediRegularity.initialBound_le_bound
-/

#print SzemerediRegularity.le_bound /-
theorem le_bound : l ≤ bound ε l :=
  (le_initialBound ε l).trans <| initialBound_le_bound ε l
#align szemeredi_regularity.le_bound SzemerediRegularity.le_bound
-/

#print SzemerediRegularity.bound_pos /-
theorem bound_pos : 0 < bound ε l :=
  (initialBound_pos ε l).trans_le <| initialBound_le_bound ε l
#align szemeredi_regularity.bound_pos SzemerediRegularity.bound_pos
-/

variable {ι 𝕜 : Type _} [LinearOrderedField 𝕜] (r : ι → ι → Prop) [DecidableRel r] {s t : Finset ι}
  {x : 𝕜}

#print SzemerediRegularity.mul_sq_le_sum_sq /-
theorem mul_sq_le_sum_sq (hst : s ⊆ t) (f : ι → 𝕜) (hs : x ^ 2 ≤ ((∑ i in s, f i) / s.card) ^ 2)
    (hs' : (s.card : 𝕜) ≠ 0) : (s.card : 𝕜) * x ^ 2 ≤ ∑ i in t, f i ^ 2 :=
  (mul_le_mul_of_nonneg_left (hs.trans sum_div_card_sq_le_sum_sq_div_card) <|
        Nat.cast_nonneg _).trans <|
    (mul_div_cancel₀ _ hs').le.trans <| sum_le_sum_of_subset_of_nonneg hst fun i _ _ => sq_nonneg _
#align szemeredi_regularity.mul_sq_le_sum_sq SzemerediRegularity.mul_sq_le_sum_sq
-/

#print SzemerediRegularity.add_div_le_sum_sq_div_card /-
theorem add_div_le_sum_sq_div_card (hst : s ⊆ t) (f : ι → 𝕜) (d : 𝕜) (hx : 0 ≤ x)
    (hs : x ≤ |(∑ i in s, f i) / s.card - (∑ i in t, f i) / t.card|)
    (ht : d ≤ ((∑ i in t, f i) / t.card) ^ 2) :
    d + s.card / t.card * x ^ 2 ≤ (∑ i in t, f i ^ 2) / t.card :=
  by
  obtain hscard | hscard := (s.card.cast_nonneg : (0 : 𝕜) ≤ s.card).eq_or_lt
  · simpa [← hscard] using ht.trans sum_div_card_sq_le_sum_sq_div_card
  have htcard : (0 : 𝕜) < t.card := hscard.trans_le (Nat.cast_le.2 (card_le_of_subset hst))
  have h₁ : x ^ 2 ≤ ((∑ i in s, f i) / s.card - (∑ i in t, f i) / t.card) ^ 2 :=
    sq_le_sq.2 (by rwa [abs_of_nonneg hx])
  have h₂ : x ^ 2 ≤ ((∑ i in s, (f i - (∑ j in t, f j) / t.card)) / s.card) ^ 2 :=
    by
    apply h₁.trans
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, sub_div, mul_div_cancel_left₀ _ hscard.ne']
  apply (add_le_add_right ht _).trans
  rw [← mul_div_right_comm, le_div_iff htcard, add_mul, div_mul_cancel₀ _ htcard.ne']
  have h₃ := mul_sq_le_sum_sq hst (fun i => f i - (∑ j in t, f j) / t.card) h₂ hscard.ne'
  apply (add_le_add_left h₃ _).trans
  simp [← mul_div_right_comm _ (t.card : 𝕜), sub_div' _ _ _ htcard.ne', ← sum_div, ← add_div,
    mul_pow, div_le_iff (sq_pos_of_ne_zero _ htcard.ne'), sub_sq, sum_add_distrib, ← sum_mul, ←
    mul_sum]
  ring_nf
#align szemeredi_regularity.add_div_le_sum_sq_div_card SzemerediRegularity.add_div_le_sum_sq_div_card
-/

end szemeredi_regularity

namespace Tactic

open Positivity szemeredi_regularity

/-- Extension for the `positivity` tactic: `szemeredi_regularity.initial_bound` and
`szemeredi_regularity.bound` are always positive. -/
@[positivity]
unsafe def positivity_szemeredi_regularity_bound : expr → tactic strictness
  | q(SzemerediRegularity.initialBound $(ε) $(l)) => positive <$> mk_app `` initial_bound_pos [ε, l]
  | q(SzemerediRegularity.bound $(ε) $(l)) => positive <$> mk_app `` bound_pos [ε, l]
  | e =>
    pp e >>=
      fail ∘
        format.bracket "The expression `"
          "` isn't of the form `szemeredi_regularity.initial_bound ε l` nor `szemeredi_regularity.bound ε l`"
#align tactic.positivity_szemeredi_regularity_bound tactic.positivity_szemeredi_regularity_bound

example (ε : ℝ) (l : ℕ) : 0 < SzemerediRegularity.initialBound ε l := by positivity

example (ε : ℝ) (l : ℕ) : 0 < SzemerediRegularity.bound ε l := by positivity

end Tactic

