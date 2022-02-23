/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import Mathbin.SetTheory.Pgame

/-!
# Basic definitions about who has a winning stratergy

We define `G.first_loses`, `G.first_wins`, `G.left_wins` and `G.right_wins` for a pgame `G`, which
means the second, first, left and right players have a winning strategy respectively.
These are defined by inequalities which can be unfolded with `pgame.lt_def` and `pgame.le_def`.
-/


namespace Pgame

-- mathport name: «expr ≈ »
local infixl:0 " ≈ " => Equiv

/-- The player who goes first loses -/
def FirstLoses (G : Pgame) : Prop :=
  G ≤ 0 ∧ 0 ≤ G

/-- The player who goes first wins -/
def FirstWins (G : Pgame) : Prop :=
  0 < G ∧ G < 0

/-- The left player can always win -/
def LeftWins (G : Pgame) : Prop :=
  0 < G ∧ 0 ≤ G

/-- The right player can always win -/
def RightWins (G : Pgame) : Prop :=
  G ≤ 0 ∧ G < 0

theorem zero_first_loses : FirstLoses 0 := by
  tidy

theorem one_left_wins : LeftWins 1 :=
  ⟨by
    rw [lt_def_le]
    tidy, by
    rw [le_def] <;> tidy⟩

theorem star_first_wins : FirstWins star :=
  ⟨zero_lt_star, star_lt_zero⟩

theorem omega_left_wins : LeftWins omega :=
  ⟨by
    rw [lt_def_le]
    exact
      Or.inl
        ⟨ULift.up 0, by
          tidy⟩,
    by
    rw [le_def] <;> tidy⟩

theorem winner_cases (G : Pgame) : G.LeftWins ∨ G.RightWins ∨ G.FirstLoses ∨ G.FirstWins := by
  classical
  by_cases' hpos : 0 < G <;>
    by_cases' hneg : G < 0 <;>
      · try
          rw [not_ltₓ] at hpos
        try
          rw [not_ltₓ] at hneg
        try
          left
          exact ⟨hpos, hneg⟩
        try
          right
          left
          exact ⟨hpos, hneg⟩
        try
          right
          right
          left
          exact ⟨hpos, hneg⟩
        try
          right
          right
          right
          exact ⟨hpos, hneg⟩
        

theorem first_loses_is_zero {G : Pgame} : G.FirstLoses ↔ (G ≈ 0) := by
  rfl

theorem first_loses_of_equiv {G H : Pgame} (h : G ≈ H) : G.FirstLoses → H.FirstLoses := fun hGp =>
  ⟨le_of_equiv_of_le h.symm hGp.1, le_of_le_of_equiv hGp.2 h⟩

theorem first_wins_of_equiv {G H : Pgame} (h : G ≈ H) : G.FirstWins → H.FirstWins := fun hGn =>
  ⟨lt_of_lt_of_equiv hGn.1 h, lt_of_equiv_of_lt h.symm hGn.2⟩

theorem left_wins_of_equiv {G H : Pgame} (h : G ≈ H) : G.LeftWins → H.LeftWins := fun hGl =>
  ⟨lt_of_lt_of_equiv hGl.1 h, le_of_le_of_equiv hGl.2 h⟩

theorem right_wins_of_equiv {G H : Pgame} (h : G ≈ H) : G.RightWins → H.RightWins := fun hGr =>
  ⟨le_of_equiv_of_le h.symm hGr.1, lt_of_equiv_of_lt h.symm hGr.2⟩

theorem first_loses_of_equiv_iff {G H : Pgame} (h : G ≈ H) : G.FirstLoses ↔ H.FirstLoses :=
  ⟨first_loses_of_equiv h, first_loses_of_equiv h.symm⟩

theorem first_wins_of_equiv_iff {G H : Pgame} (h : G ≈ H) : G.FirstWins ↔ H.FirstWins :=
  ⟨first_wins_of_equiv h, first_wins_of_equiv h.symm⟩

theorem left_wins_of_equiv_iff {G H : Pgame} (h : G ≈ H) : G.LeftWins ↔ H.LeftWins :=
  ⟨left_wins_of_equiv h, left_wins_of_equiv h.symm⟩

theorem right_wins_of_equiv_iff {G H : Pgame} (h : G ≈ H) : G.RightWins ↔ H.RightWins :=
  ⟨right_wins_of_equiv h, right_wins_of_equiv h.symm⟩

theorem not_first_wins_of_first_loses {G : Pgame} : G.FirstLoses → ¬G.FirstWins := by
  rw [first_loses_is_zero]
  rintro h ⟨h₀, -⟩
  exact Pgame.lt_irrefl 0 (lt_of_lt_of_equiv h₀ h)

theorem not_first_loses_of_first_wins {G : Pgame} : G.FirstWins → ¬G.FirstLoses :=
  imp_not_comm.1 <| not_first_wins_of_first_loses

end Pgame

