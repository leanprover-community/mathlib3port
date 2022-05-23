/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import Mathbin.SetTheory.Game.Pgame

/-!
# Basic definitions about who has a winning stratergy

We define `G.first_loses`, `G.first_wins`, `G.left_wins` and `G.right_wins` for a pgame `G`, which
means the second, first, left and right players have a winning strategy respectively.
These are defined by inequalities which can be unfolded with `pgame.lt_def` and `pgame.le_def`.
-/


namespace Pgame

-- mathport name: «expr ≈ »
local infixl:0 " ≈ " => Equiv

-- mathport name: «expr ⧏ »
local infixl:50 " ⧏ " => Lf

-- mathport name: «expr ∥ »
local infixl:50 " ∥ " => Fuzzy

/-- The player who goes first loses -/
def FirstLoses (G : Pgame) : Prop :=
  G ≈ 0

/-- The player who goes first wins -/
def FirstWins (G : Pgame) : Prop :=
  G ∥ 0

/-- The left player can always win -/
def LeftWins (G : Pgame) : Prop :=
  0 < G

/-- The right player can always win -/
def RightWins (G : Pgame) : Prop :=
  G < 0

theorem zero_first_loses : FirstLoses 0 :=
  equiv_rfl

theorem one_left_wins : LeftWins 1 :=
  zero_lt_one

theorem star_first_wins : FirstWins star :=
  star_fuzzy_zero

theorem winner_cases (G : Pgame) : G.RightWins ∨ G.FirstLoses ∨ G.LeftWins ∨ G.FirstWins :=
  lt_or_equiv_or_gt_or_fuzzy G 0

theorem first_loses_is_zero {G : Pgame} : G.FirstLoses ↔ (G ≈ 0) := by
  rfl

theorem first_loses_of_equiv {G H : Pgame} (h : G ≈ H) : G.FirstLoses → H.FirstLoses :=
  equiv_trans <| equiv_symm h

theorem first_wins_of_equiv {G H : Pgame} (h : G ≈ H) : G.FirstWins → H.FirstWins :=
  (fuzzy_congr_left h).1

theorem left_wins_of_equiv {G H : Pgame} (h : G ≈ H) : G.LeftWins → H.LeftWins :=
  (lt_congr_right h).1

theorem right_wins_of_equiv {G H : Pgame} (h : G ≈ H) : G.RightWins → H.RightWins :=
  (lt_congr_left h).1

theorem first_loses_of_equiv_iff {G H : Pgame} (h : G ≈ H) : G.FirstLoses ↔ H.FirstLoses :=
  ⟨first_loses_of_equiv h, equiv_trans h⟩

theorem first_wins_of_equiv_iff {G H : Pgame} : (G ≈ H) → (G.FirstWins ↔ H.FirstWins) :=
  fuzzy_congr_left

theorem left_wins_of_equiv_iff {G H : Pgame} : (G ≈ H) → (G.LeftWins ↔ H.LeftWins) :=
  lt_congr_right

theorem right_wins_of_equiv_iff {G H : Pgame} : (G ≈ H) → (G.RightWins ↔ H.RightWins) :=
  lt_congr_left

theorem not_first_wins_of_first_loses {G : Pgame} : G.FirstLoses → ¬G.FirstWins :=
  equiv.not_fuzzy

theorem not_first_loses_of_first_wins {G : Pgame} : G.FirstWins → ¬G.FirstLoses :=
  fuzzy.not_equiv

end Pgame

