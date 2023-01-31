/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta

! This file was ported from Lean 3 source module combinatorics.simple_graph.regularity.bound
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Pow
import Mathbin.Order.Partition.Equipartition

/-!
# Numerical bounds for Szemerédi Regularity Lemma

This file gathers the numerical facts required by the proof of Szemerédi's regularity lemma.

## Main declarations

* `szemeredi_regularity.step_bound`: During the inductive step, a partition of size `n` is blown to
  size at most `step_bound n`.
* `szemeredi_regularity.initial_bound`: The size of the partition we start the induction with.
* `szemeredi_regularity.bound`: The upper bound on the size of the partition produced by our version
  of Szemerédi's regularity lemma.
-/


open Finset Fintype Function Real

namespace SzemerediRegularity

/-- Auxiliary function for Szemerédi's regularity lemma. Blowing up a partition of size `n` during
the induction results in a partition of size at most `step_bound n`. -/
def stepBound (n : ℕ) : ℕ :=
  n * 4 ^ n
#align szemeredi_regularity.step_bound SzemerediRegularity.stepBound

theorem le_stepBound : id ≤ stepBound := fun n => Nat.le_mul_of_pos_right <| pow_pos (by norm_num) n
#align szemeredi_regularity.le_step_bound SzemerediRegularity.le_stepBound

theorem stepBound_mono : Monotone stepBound := fun a b h =>
  Nat.mul_le_mul h <| Nat.pow_le_pow_of_le_right (by norm_num) h
#align szemeredi_regularity.step_bound_mono SzemerediRegularity.stepBound_mono

theorem stepBound_pos_iff {n : ℕ} : 0 < stepBound n ↔ 0 < n :=
  zero_lt_mul_right <| by positivity
#align szemeredi_regularity.step_bound_pos_iff SzemerediRegularity.stepBound_pos_iff

alias step_bound_pos_iff ↔ _ step_bound_pos
#align szemeredi_regularity.step_bound_pos SzemerediRegularity.stepBound_pos

variable {α : Type _} [DecidableEq α] [Fintype α] {P : Finpartition (univ : Finset α)}
  {u : Finset α} {ε : ℝ}

-- mathport name: exprm
local notation "m" => (card α / stepBound P.parts.card : ℕ)

-- mathport name: expra
local notation "a" => (card α / P.parts.card - m * 4 ^ P.parts.card : ℕ)

theorem m_pos [Nonempty α] (hPα : P.parts.card * 16 ^ P.parts.card ≤ card α) : 0 < m :=
  Nat.div_pos ((Nat.mul_le_mul_left _ <| Nat.pow_le_pow_of_le_left (by norm_num) _).trans hPα) <|
    stepBound_pos (P.parts_nonempty <| univ_nonempty.ne_empty).card_pos
#align szemeredi_regularity.m_pos SzemerediRegularity.m_pos

theorem m_coe_pos [Nonempty α] (hPα : P.parts.card * 16 ^ P.parts.card ≤ card α) : (0 : ℝ) < m :=
  Nat.cast_pos.2 <| m_pos hPα
#align szemeredi_regularity.m_coe_pos SzemerediRegularity.m_coe_pos

theorem coe_m_add_one_pos : 0 < (m : ℝ) + 1 :=
  Nat.cast_add_one_pos _
#align szemeredi_regularity.coe_m_add_one_pos SzemerediRegularity.coe_m_add_one_pos

theorem one_le_m_coe [Nonempty α] (hPα : P.parts.card * 16 ^ P.parts.card ≤ card α) : (1 : ℝ) ≤ m :=
  Nat.one_le_cast.2 <| m_pos hPα
#align szemeredi_regularity.one_le_m_coe SzemerediRegularity.one_le_m_coe

theorem eps_pow_five_pos (hPε : 100 ≤ 4 ^ P.parts.card * ε ^ 5) : 0 < ε ^ 5 :=
  pos_of_mul_pos_right ((by norm_num : (0 : ℝ) < 100).trans_le hPε) <| pow_nonneg (by norm_num) _
#align szemeredi_regularity.eps_pow_five_pos SzemerediRegularity.eps_pow_five_pos

theorem eps_pos (hPε : 100 ≤ 4 ^ P.parts.card * ε ^ 5) : 0 < ε :=
  pow_bit1_pos_iff.1 <| eps_pow_five_pos hPε
#align szemeredi_regularity.eps_pos SzemerediRegularity.eps_pos

theorem hundred_div_ε_pow_five_le_m [Nonempty α] (hPα : P.parts.card * 16 ^ P.parts.card ≤ card α)
    (hPε : 100 ≤ 4 ^ P.parts.card * ε ^ 5) : 100 / ε ^ 5 ≤ m :=
  (div_le_of_nonneg_of_le_mul (eps_pow_five_pos hPε).le (by positivity) hPε).trans
    (by
      norm_cast
      rwa [Nat.le_div_iff_mul_le'
          (step_bound_pos (P.parts_nonempty <| univ_nonempty.ne_empty).card_pos),
        step_bound, mul_left_comm, ← mul_pow])
#align szemeredi_regularity.hundred_div_ε_pow_five_le_m SzemerediRegularity.hundred_div_ε_pow_five_le_m

theorem hundred_le_m [Nonempty α] (hPα : P.parts.card * 16 ^ P.parts.card ≤ card α)
    (hPε : 100 ≤ 4 ^ P.parts.card * ε ^ 5) (hε : ε ≤ 1) : 100 ≤ m := by
  exact_mod_cast
    (le_div_self (by norm_num) (eps_pow_five_pos hPε) <| pow_le_one _ (eps_pos hPε).le hε).trans
      (hundred_div_ε_pow_five_le_m hPα hPε)
#align szemeredi_regularity.hundred_le_m SzemerediRegularity.hundred_le_m

theorem a_add_one_le_four_pow_parts_card : a + 1 ≤ 4 ^ P.parts.card :=
  by
  have h : 1 ≤ 4 ^ P.parts.card := one_le_pow_of_one_le (by norm_num) _
  rw [step_bound, ← Nat.div_div_eq_div_mul, ← Nat.le_sub_iff_right h, tsub_le_iff_left, ←
    Nat.add_sub_assoc h]
  exact Nat.le_pred_of_lt (Nat.lt_div_mul_add h)
#align szemeredi_regularity.a_add_one_le_four_pow_parts_card SzemerediRegularity.a_add_one_le_four_pow_parts_card

theorem card_aux₁ (hucard : u.card = m * 4 ^ P.parts.card + a) :
    (4 ^ P.parts.card - a) * m + a * (m + 1) = u.card := by
  rw [hucard, mul_add, mul_one, ← add_assoc, ← add_mul,
    Nat.sub_add_cancel ((Nat.le_succ _).trans a_add_one_le_four_pow_parts_card), mul_comm]
#align szemeredi_regularity.card_aux₁ SzemerediRegularity.card_aux₁

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

theorem pow_mul_m_le_card_part (hP : P.IsEquipartition) (hu : u ∈ P.parts) :
    (4 : ℝ) ^ P.parts.card * m ≤ u.card := by
  norm_cast
  rw [step_bound, ← Nat.div_div_eq_div_mul]
  exact (Nat.mul_div_le _ _).trans (hP.average_le_card_part hu)
#align szemeredi_regularity.pow_mul_m_le_card_part SzemerediRegularity.pow_mul_m_le_card_part

variable (P ε) (l : ℕ)

/-- Auxiliary function for Szemerédi's regularity lemma. The size of the partition by which we start
blowing. -/
noncomputable def initialBound : ℕ :=
  max 7 <| max l <| ⌊log (100 / ε ^ 5) / log 4⌋₊ + 1
#align szemeredi_regularity.initial_bound SzemerediRegularity.initialBound

theorem le_initialBound : l ≤ initialBound ε l :=
  (le_max_left _ _).trans <| le_max_right _ _
#align szemeredi_regularity.le_initial_bound SzemerediRegularity.le_initialBound

theorem seven_le_initialBound : 7 ≤ initialBound ε l :=
  le_max_left _ _
#align szemeredi_regularity.seven_le_initial_bound SzemerediRegularity.seven_le_initialBound

theorem initialBound_pos : 0 < initialBound ε l :=
  Nat.succ_pos'.trans_le <| seven_le_initialBound _ _
#align szemeredi_regularity.initial_bound_pos SzemerediRegularity.initialBound_pos

theorem hundred_lt_pow_initialBound_mul {ε : ℝ} (hε : 0 < ε) (l : ℕ) :
    100 < 4 ^ initialBound ε l * ε ^ 5 :=
  by
  rw [← rpow_nat_cast 4, ← div_lt_iff (pow_pos hε 5), lt_rpow_iff_log_lt _ zero_lt_four, ←
    div_lt_iff, initial_bound, Nat.cast_max, Nat.cast_max]
  · push_cast
    exact lt_max_of_lt_right (lt_max_of_lt_right <| Nat.lt_floor_add_one _)
  · exact log_pos (by norm_num)
  · exact div_pos (by norm_num) (pow_pos hε 5)
#align szemeredi_regularity.hundred_lt_pow_initial_bound_mul SzemerediRegularity.hundred_lt_pow_initialBound_mul

/-- An explicit bound on the size of the equipartition whose existence is given by Szemerédi's
regularity lemma. -/
noncomputable def bound : ℕ :=
  (stepBound^[⌊4 / ε ^ 5⌋₊] <| initialBound ε l) *
    16 ^ (stepBound^[⌊4 / ε ^ 5⌋₊] <| initialBound ε l)
#align szemeredi_regularity.bound SzemerediRegularity.bound

theorem initialBound_le_bound : initialBound ε l ≤ bound ε l :=
  (id_le_iterate_of_id_le le_stepBound _ _).trans <| Nat.le_mul_of_pos_right <| by positivity
#align szemeredi_regularity.initial_bound_le_bound SzemerediRegularity.initialBound_le_bound

theorem le_bound : l ≤ bound ε l :=
  (le_initialBound ε l).trans <| initialBound_le_bound ε l
#align szemeredi_regularity.le_bound SzemerediRegularity.le_bound

theorem bound_pos : 0 < bound ε l :=
  (initialBound_pos ε l).trans_le <| initialBound_le_bound ε l
#align szemeredi_regularity.bound_pos SzemerediRegularity.bound_pos

end SzemerediRegularity

namespace Tactic

open Positivity SzemerediRegularity

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

