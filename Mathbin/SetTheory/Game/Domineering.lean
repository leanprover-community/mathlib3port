import Mathbin.SetTheory.Game.State

/-!
# Domineering as a combinatorial game.

We define the game of Domineering, played on a chessboard of arbitrary shape
(possibly even disconnected).
Left moves by placing a domino vertically, while Right moves by placing a domino horizontally.

This is only a fragment of a full development;
in order to successfully analyse positions we would need some more theorems.
Most importantly, we need a general statement that allows us to discard irrelevant moves.
Specifically to domineering, we need the fact that
disjoint parts of the chessboard give sums of games.
-/


namespace Pgame

namespace Domineering

open Function

/-- The embedding `(x, y) ↦ (x, y+1)`. -/
def shift_up : ℤ × ℤ ↪ ℤ × ℤ :=
  (embedding.refl ℤ).prod_map ⟨fun n => n+1, add_left_injective 1⟩

/-- The embedding `(x, y) ↦ (x+1, y)`. -/
def shift_right : ℤ × ℤ ↪ ℤ × ℤ :=
  embedding.prod_map ⟨fun n => n+1, add_left_injective 1⟩ (embedding.refl ℤ)

-- error in SetTheory.Game.Domineering: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler inhabited
/-- A Domineering board is an arbitrary finite subset of `ℤ × ℤ`. -/ @[derive #[expr inhabited]] def board :=
finset «expr × »(exprℤ(), exprℤ())

attribute [local reducible] board

/-- Left can play anywhere that a square and the square below it are open. -/
def left (b : board) : Finset (ℤ × ℤ) :=
  b ∩ b.map shift_up

/-- Right can play anywhere that a square and the square to the left are open. -/
def right (b : board) : Finset (ℤ × ℤ) :=
  b ∩ b.map shift_right

/-- After Left moves, two vertically adjacent squares are removed from the board. -/
def move_left (b : board) (m : ℤ × ℤ) : board :=
  (b.erase m).erase (m.1, m.2 - 1)

/-- After Left moves, two horizontally adjacent squares are removed from the board. -/
def move_right (b : board) (m : ℤ × ℤ) : board :=
  (b.erase m).erase (m.1 - 1, m.2)

-- error in SetTheory.Game.Domineering: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem card_of_mem_left
{b : board}
{m : «expr × »(exprℤ(), exprℤ())}
(h : «expr ∈ »(m, left b)) : «expr ≤ »(2, finset.card b) :=
begin
  dsimp [] ["[", expr left, "]"] [] ["at", ident h],
  have [ident w₁] [":", expr «expr ∈ »(m, b)] [],
  { rw [expr finset.mem_inter] ["at", ident h],
    exact [expr h.1] },
  have [ident w₂] [":", expr «expr ∈ »((m.1, «expr - »(m.2, 1)), b.erase m)] [],
  { simp [] [] ["only"] ["[", expr finset.mem_erase, "]"] [] [],
    fsplit,
    { exact [expr λ w, pred_ne_self m.2 (congr_arg prod.snd w)] },
    { rw [expr finset.mem_inter] ["at", ident h],
      have [ident h₂] [] [":=", expr h.2],
      clear [ident h],
      rw [expr finset.mem_map] ["at", ident h₂],
      rcases [expr h₂, "with", "⟨", ident m', ",", "⟨", ident h₂, ",", ident rfl, "⟩", "⟩"],
      dsimp [] ["[", expr shift_up, "]"] [] [],
      simpa [] [] [] [] [] [] } },
  have [ident i₁] [] [":=", expr finset.card_erase_lt_of_mem w₁],
  have [ident i₂] [] [":=", expr nat.lt_of_le_of_lt (nat.zero_le _) (finset.card_erase_lt_of_mem w₂)],
  exact [expr nat.lt_of_le_of_lt i₂ i₁]
end

-- error in SetTheory.Game.Domineering: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem card_of_mem_right
{b : board}
{m : «expr × »(exprℤ(), exprℤ())}
(h : «expr ∈ »(m, right b)) : «expr ≤ »(2, finset.card b) :=
begin
  dsimp [] ["[", expr right, "]"] [] ["at", ident h],
  have [ident w₁] [":", expr «expr ∈ »(m, b)] [],
  { rw [expr finset.mem_inter] ["at", ident h],
    exact [expr h.1] },
  have [ident w₂] [":", expr «expr ∈ »((«expr - »(m.1, 1), m.2), b.erase m)] [],
  { simp [] [] ["only"] ["[", expr finset.mem_erase, "]"] [] [],
    fsplit,
    { exact [expr λ w, pred_ne_self m.1 (congr_arg prod.fst w)] },
    { rw [expr finset.mem_inter] ["at", ident h],
      have [ident h₂] [] [":=", expr h.2],
      clear [ident h],
      rw [expr finset.mem_map] ["at", ident h₂],
      rcases [expr h₂, "with", "⟨", ident m', ",", "⟨", ident h₂, ",", ident rfl, "⟩", "⟩"],
      dsimp [] ["[", expr shift_right, "]"] [] [],
      simpa [] [] [] [] [] [] } },
  have [ident i₁] [] [":=", expr finset.card_erase_lt_of_mem w₁],
  have [ident i₂] [] [":=", expr nat.lt_of_le_of_lt (nat.zero_le _) (finset.card_erase_lt_of_mem w₂)],
  exact [expr nat.lt_of_le_of_lt i₂ i₁]
end

-- error in SetTheory.Game.Domineering: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem move_left_card
{b : board}
{m : «expr × »(exprℤ(), exprℤ())}
(h : «expr ∈ »(m, left b)) : «expr = »(«expr + »(finset.card (move_left b m), 2), finset.card b) :=
begin
  dsimp [] ["[", expr move_left, "]"] [] [],
  rw [expr finset.card_erase_of_mem] [],
  { rw [expr finset.card_erase_of_mem] [],
    { exact [expr tsub_add_cancel_of_le (card_of_mem_left h)] },
    { exact [expr finset.mem_of_mem_inter_left h] } },
  { apply [expr finset.mem_erase_of_ne_of_mem],
    { exact [expr λ w, pred_ne_self m.2 (congr_arg prod.snd w)] },
    { have [ident t] [] [":=", expr finset.mem_of_mem_inter_right h],
      dsimp [] ["[", expr shift_up, "]"] [] ["at", ident t],
      simp [] [] ["only"] ["[", expr finset.mem_map, ",", expr prod.exists, "]"] [] ["at", ident t],
      rcases [expr t, "with", "⟨", ident x, ",", ident y, ",", ident w, ",", ident h, "⟩"],
      rw ["<-", expr h] [],
      convert [] [expr w] [],
      simp [] [] [] [] [] [] } }
end

-- error in SetTheory.Game.Domineering: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem move_right_card
{b : board}
{m : «expr × »(exprℤ(), exprℤ())}
(h : «expr ∈ »(m, right b)) : «expr = »(«expr + »(finset.card (move_right b m), 2), finset.card b) :=
begin
  dsimp [] ["[", expr move_right, "]"] [] [],
  rw [expr finset.card_erase_of_mem] [],
  { rw [expr finset.card_erase_of_mem] [],
    { exact [expr tsub_add_cancel_of_le (card_of_mem_right h)] },
    { exact [expr finset.mem_of_mem_inter_left h] } },
  { apply [expr finset.mem_erase_of_ne_of_mem],
    { exact [expr λ w, pred_ne_self m.1 (congr_arg prod.fst w)] },
    { have [ident t] [] [":=", expr finset.mem_of_mem_inter_right h],
      dsimp [] ["[", expr shift_right, "]"] [] ["at", ident t],
      simp [] [] ["only"] ["[", expr finset.mem_map, ",", expr prod.exists, "]"] [] ["at", ident t],
      rcases [expr t, "with", "⟨", ident x, ",", ident y, ",", ident w, ",", ident h, "⟩"],
      rw ["<-", expr h] [],
      convert [] [expr w] [],
      simp [] [] [] [] [] [] } }
end

theorem move_left_smaller {b : board} {m : ℤ × ℤ} (h : m ∈ left b) :
  Finset.card (move_left b m) / 2 < Finset.card b / 2 :=
  by 
    simp [←move_left_card h, lt_add_one]

theorem move_right_smaller {b : board} {m : ℤ × ℤ} (h : m ∈ right b) :
  Finset.card (move_right b m) / 2 < Finset.card b / 2 :=
  by 
    simp [←move_right_card h, lt_add_one]

/-- The instance describing allowed moves on a Domineering board. -/
instance State : State board :=
  { turnBound := fun s => s.card / 2, l := fun s => (left s).Image (move_left s),
    r := fun s => (right s).Image (move_right s),
    left_bound :=
      fun s t m =>
        by 
          simp only [Finset.mem_image, Prod.exists] at m 
          rcases m with ⟨_, _, ⟨h, rfl⟩⟩
          exact move_left_smaller h,
    right_bound :=
      fun s t m =>
        by 
          simp only [Finset.mem_image, Prod.exists] at m 
          rcases m with ⟨_, _, ⟨h, rfl⟩⟩
          exact move_right_smaller h }

end Domineering

/-- Construct a pre-game from a Domineering board. -/
def domineering (b : domineering.board) : Pgame :=
  Pgame.of b

/-- All games of Domineering are short, because each move removes two squares. -/
instance short_domineering (b : domineering.board) : short (domineering b) :=
  by 
    dsimp [domineering]
    infer_instance

/-- The Domineering board with two squares arranged vertically, in which Left has the only move. -/
def domineering.one :=
  domineering [(0, 0), (0, 1)].toFinset

/-- The `L` shaped Domineering board, in which Left is exactly half a move ahead. -/
def domineering.L :=
  domineering [(0, 2), (0, 1), (0, 0), (1, 0)].toFinset

instance short_one : short domineering.one :=
  by 
    dsimp [domineering.one]
    infer_instance

instance short_L : short domineering.L :=
  by 
    dsimp [domineering.L]
    infer_instance

end Pgame

