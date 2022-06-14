/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import Mathbin.SetTheory.Game.Winner
import Mathbin.Tactic.NthRewrite.Default

/-!
# Basic definitions about impartial (pre-)games

We will define an impartial game, one in which left and right can make exactly the same moves.
Our definition differs slightly by saying that the game is always equivalent to its negative,
no matter what moves are played. This allows for games such as poker-nim to be classifed as
impartial.
-/


universe u

namespace Pgame

-- mathport name: «expr ≈ »
local infixl:0 " ≈ " => Equiv

-- mathport name: «expr ⧏ »
local infixl:50 " ⧏ " => Lf

/-- The definition for a impartial game, defined using Conway induction -/
def ImpartialAux : Pgame → Prop
  | G => (G ≈ -G) ∧ (∀ i, impartial_aux (G.moveLeft i)) ∧ ∀ j, impartial_aux (G.moveRight j)

theorem impartial_aux_def {G : Pgame} :
    G.ImpartialAux ↔ (G ≈ -G) ∧ (∀ i, ImpartialAux (G.moveLeft i)) ∧ ∀ j, ImpartialAux (G.moveRight j) := by
  rw [impartial_aux]

/-- A typeclass on impartial games. -/
class Impartial (G : Pgame) : Prop where
  out : ImpartialAux G

theorem impartial_iff_aux {G : Pgame} : G.Impartial ↔ G.ImpartialAux :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

theorem impartial_def {G : Pgame} :
    G.Impartial ↔ (G ≈ -G) ∧ (∀ i, Impartial (G.moveLeft i)) ∧ ∀ j, Impartial (G.moveRight j) := by
  simpa only [impartial_iff_aux] using impartial_aux_def

namespace Impartial

instance impartial_zero : Impartial 0 := by
  rw [impartial_def]
  dsimp'
  simp

instance impartial_star : Impartial star := by
  rw [impartial_def]
  simpa using impartial.impartial_zero

theorem neg_equiv_self (G : Pgame) [h : G.Impartial] : G ≈ -G :=
  (impartial_def.1 h).1

instance move_left_impartial {G : Pgame} [h : G.Impartial] (i : G.LeftMoves) : (G.moveLeft i).Impartial :=
  (impartial_def.1 h).2.1 i

instance move_right_impartial {G : Pgame} [h : G.Impartial] (j : G.RightMoves) : (G.moveRight j).Impartial :=
  (impartial_def.1 h).2.2 j

theorem impartial_congr : ∀ {G H : Pgame} e : Relabelling G H [G.Impartial], H.Impartial
  | G, H, e => by
    intro h
    rw [impartial_def]
    refine' ⟨e.symm.equiv.trans ((neg_equiv_self G).trans (neg_equiv_neg_iff.2 e.equiv)), fun i => _, fun j => _⟩ <;>
      cases' e with _ _ L R hL hR
    · convert impartial_congr (hL (L.symm i))
      rw [Equivₓ.apply_symm_apply]
      
    · exact impartial_congr (hR j)
      

instance impartial_add : ∀ G H : Pgame [G.Impartial] [H.Impartial], (G + H).Impartial
  | G, H => by
    intro hG hH
    rw [impartial_def]
    refine'
      ⟨(add_congr (neg_equiv_self _) (neg_equiv_self _)).trans (neg_add_relabelling _ _).Equiv.symm, fun k => _,
        fun k => _⟩
    · apply left_moves_add_cases k
      all_goals
        intro i
        simp only [add_move_left_inl, add_move_left_inr]
        apply impartial_add
      
    · apply right_moves_add_cases k
      all_goals
        intro i
        simp only [add_move_right_inl, add_move_right_inr]
        apply impartial_add
      

instance impartial_neg : ∀ G : Pgame [G.Impartial], (-G).Impartial
  | G => by
    intro hG
    rw [impartial_def]
    refine' ⟨_, fun i => _, fun i => _⟩
    · rw [neg_negₓ]
      exact (neg_equiv_self G).symm
      
    · rw [move_left_neg']
      apply impartial_neg
      
    · rw [move_right_neg']
      apply impartial_neg
      

theorem nonpos (G : Pgame) [G.Impartial] : ¬0 < G := fun h => by
  have h' := neg_lt_neg_iff.2 h
  rw [Pgame.neg_zero, lt_congr_left (neg_equiv_self G).symm] at h'
  exact (h.trans h').False

theorem nonneg (G : Pgame) [G.Impartial] : ¬G < 0 := fun h => by
  have h' := neg_lt_neg_iff.2 h
  rw [Pgame.neg_zero, lt_congr_right (neg_equiv_self G).symm] at h'
  exact (h.trans h').False

theorem winner_cases (G : Pgame) [G.Impartial] : G.FirstLoses ∨ G.FirstWins := by
  rcases G.winner_cases with (h | h | h | h)
  · exact ((nonneg G) h).elim
    
  · exact Or.inl h
    
  · exact ((nonpos G) h).elim
    
  · exact Or.inr h
    

theorem not_first_wins (G : Pgame) [G.Impartial] : ¬G.FirstWins ↔ G.FirstLoses := by
  cases winner_cases G <;>-- `finish using [not_first_loses_of_first_wins]` can close these goals
    simp [not_first_loses_of_first_wins, not_first_wins_of_first_loses, h]

theorem not_first_loses (G : Pgame) [G.Impartial] : ¬G.FirstLoses ↔ G.FirstWins :=
  Iff.symm <| iff_not_comm.1 <| Iff.symm <| not_first_wins G

theorem add_self (G : Pgame) [G.Impartial] : (G + G).FirstLoses :=
  first_loses_is_zero.2 <| (add_congr_left (neg_equiv_self G)).trans (add_left_neg_equiv G)

theorem equiv_iff_sum_first_loses (G H : Pgame) [G.Impartial] [H.Impartial] : (G ≈ H) ↔ (G + H).FirstLoses := by
  constructor
  · intro heq
    exact first_loses_of_equiv (add_congr_right HEq) (add_self G)
    
  · intro hGHp
    constructor
    · rw [le_iff_sub_nonneg]
      exact hGHp.2.trans (add_comm_le.trans <| le_of_le_of_equiv le_rfl <| add_congr_right (neg_equiv_self G))
      
    · rw [le_iff_sub_nonneg]
      exact hGHp.2.trans (le_of_le_of_equiv le_rfl <| add_congr_right (neg_equiv_self H))
      
    

theorem le_zero_iff {G : Pgame} [G.Impartial] : G ≤ 0 ↔ 0 ≤ G := by
  rw [← zero_le_neg_iff, le_congr_right (neg_equiv_self G)]

theorem lf_zero_iff {G : Pgame} [G.Impartial] : G ⧏ 0 ↔ 0 ⧏ G := by
  rw [← zero_lf_neg_iff, lf_congr_right (neg_equiv_self G)]

theorem first_loses_symm (G : Pgame) [G.Impartial] : G.FirstLoses ↔ G ≤ 0 :=
  ⟨And.left, fun h => ⟨h, le_zero_iff.1 h⟩⟩

theorem first_wins_symm (G : Pgame) [G.Impartial] : G.FirstWins ↔ G ⧏ 0 :=
  ⟨And.left, fun h => ⟨h, lf_zero_iff.1 h⟩⟩

theorem first_loses_symm' (G : Pgame) [G.Impartial] : G.FirstLoses ↔ 0 ≤ G :=
  ⟨And.right, fun h => ⟨le_zero_iff.2 h, h⟩⟩

theorem first_wins_symm' (G : Pgame) [G.Impartial] : G.FirstWins ↔ 0 ⧏ G :=
  ⟨And.right, fun h => ⟨lf_zero_iff.2 h, h⟩⟩

theorem no_good_left_moves_iff_first_loses (G : Pgame) [G.Impartial] :
    (∀ i : G.LeftMoves, (G.moveLeft i).FirstWins) ↔ G.FirstLoses := by
  refine' ⟨fun hb => _, fun hp i => _⟩
  · rw [first_loses_symm G, le_iff_forall_lf]
    exact ⟨fun i => (hb i).1, isEmptyElim⟩
    
  · rw [first_wins_symm]
    exact (le_iff_forall_lf.1 <| (first_loses_symm G).1 hp).1 i
    

theorem no_good_right_moves_iff_first_loses (G : Pgame) [G.Impartial] :
    (∀ j : G.RightMoves, (G.moveRight j).FirstWins) ↔ G.FirstLoses := by
  rw [first_loses_of_equiv_iff (neg_equiv_self G), ← no_good_left_moves_iff_first_loses]
  refine' ⟨fun h i => _, fun h i => _⟩
  · rw [move_left_neg', ← first_wins_of_equiv_iff (neg_equiv_self (G.move_right (to_left_moves_neg.symm i)))]
    apply h
    
  · rw [move_right_neg_symm', ← first_wins_of_equiv_iff (neg_equiv_self ((-G).moveLeft (to_left_moves_neg i)))]
    apply h
    

theorem good_left_move_iff_first_wins (G : Pgame) [G.Impartial] :
    (∃ i : G.LeftMoves, (G.moveLeft i).FirstLoses) ↔ G.FirstWins := by
  refine' ⟨fun ⟨i, hi⟩ => (first_wins_symm' G).2 (lf_of_forall_le <| Or.inl ⟨i, hi.2⟩), fun hn => _⟩
  rw [first_wins_symm' G, lf_iff_forall_le] at hn
  rcases hn with (⟨i, hi⟩ | ⟨j, _⟩)
  · exact ⟨i, (first_loses_symm' _).2 hi⟩
    
  · exact Pempty.elimₓ j
    

theorem good_right_move_iff_first_wins (G : Pgame) [G.Impartial] :
    (∃ j : G.RightMoves, (G.moveRight j).FirstLoses) ↔ G.FirstWins := by
  refine' ⟨fun ⟨j, hj⟩ => (first_wins_symm G).2 (lf_of_forall_le <| Or.inr ⟨j, hj.1⟩), fun hn => _⟩
  rw [first_wins_symm G, lf_iff_forall_le] at hn
  rcases hn with (⟨i, _⟩ | ⟨j, hj⟩)
  · exact Pempty.elimₓ i
    
  · exact ⟨j, (first_loses_symm _).2 hj⟩
    

end Impartial

end Pgame

