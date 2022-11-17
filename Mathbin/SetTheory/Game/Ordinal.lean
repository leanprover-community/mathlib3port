/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathbin.SetTheory.Game.Basic
import Mathbin.SetTheory.Ordinal.NaturalOps

/-!
# Ordinals as games

We define the canonical map `ordinal → pgame`, where every ordinal is mapped to the game whose left
set consists of all previous ordinals.

The map to surreals is defined in `ordinal.to_surreal`.

# Main declarations

- `ordinal.to_pgame`: The canonical map between ordinals and pre-games.
- `ordinal.to_pgame_embedding`: The order embedding version of the previous map.
-/


universe u

open Pgame

open NaturalOps Pgame

namespace Ordinal

/-- Converts an ordinal into the corresponding pre-game. -/
noncomputable def toPgame : Ordinal.{u} → Pgame.{u}
  | o =>
    ⟨o.out.α, PEmpty, fun x =>
      let hwf := Ordinal.typein_lt_self x
      (typein (· < ·) x).toPgame,
      PEmpty.elim⟩
#align ordinal.to_pgame Ordinal.toPgame

theorem to_pgame_def (o : Ordinal) : o.toPgame = ⟨o.out.α, PEmpty, fun x => (typein (· < ·) x).toPgame, PEmpty.elim⟩ :=
  by rw [to_pgame]
#align ordinal.to_pgame_def Ordinal.to_pgame_def

@[simp]
theorem to_pgame_left_moves (o : Ordinal) : o.toPgame.LeftMoves = o.out.α := by rw [to_pgame, left_moves]
#align ordinal.to_pgame_left_moves Ordinal.to_pgame_left_moves

@[simp]
theorem to_pgame_right_moves (o : Ordinal) : o.toPgame.RightMoves = PEmpty := by rw [to_pgame, right_moves]
#align ordinal.to_pgame_right_moves Ordinal.to_pgame_right_moves

instance is_empty_zero_to_pgame_left_moves : IsEmpty (toPgame 0).LeftMoves := by
  rw [to_pgame_left_moves]
  infer_instance
#align ordinal.is_empty_zero_to_pgame_left_moves Ordinal.is_empty_zero_to_pgame_left_moves

instance is_empty_to_pgame_right_moves (o : Ordinal) : IsEmpty o.toPgame.RightMoves := by
  rw [to_pgame_right_moves]
  infer_instance
#align ordinal.is_empty_to_pgame_right_moves Ordinal.is_empty_to_pgame_right_moves

/-- Converts an ordinal less than `o` into a move for the `pgame` corresponding to `o`, and vice
versa. -/
noncomputable def toLeftMovesToPgame {o : Ordinal} : Set.iio o ≃ o.toPgame.LeftMoves :=
  (enumIsoOut o).toEquiv.trans (Equiv.cast (to_pgame_left_moves o).symm)
#align ordinal.to_left_moves_to_pgame Ordinal.toLeftMovesToPgame

@[simp]
theorem to_left_moves_to_pgame_symm_lt {o : Ordinal} (i : o.toPgame.LeftMoves) : ↑(toLeftMovesToPgame.symm i) < o :=
  (toLeftMovesToPgame.symm i).Prop
#align ordinal.to_left_moves_to_pgame_symm_lt Ordinal.to_left_moves_to_pgame_symm_lt

theorem to_pgame_move_left_heq {o : Ordinal} : o.toPgame.moveLeft == fun x : o.out.α => (typein (· < ·) x).toPgame := by
  rw [to_pgame]
  rfl
#align ordinal.to_pgame_move_left_heq Ordinal.to_pgame_move_left_heq

@[simp]
theorem to_pgame_move_left' {o : Ordinal} (i) : o.toPgame.moveLeft i = (toLeftMovesToPgame.symm i).val.toPgame :=
  (congr_heq to_pgame_move_left_heq.symm (cast_heq _ i)).symm
#align ordinal.to_pgame_move_left' Ordinal.to_pgame_move_left'

theorem to_pgame_move_left {o : Ordinal} (i) : o.toPgame.moveLeft (toLeftMovesToPgame i) = i.val.toPgame := by simp
#align ordinal.to_pgame_move_left Ordinal.to_pgame_move_left

/-- `0.to_pgame` has the same moves as `0`. -/
noncomputable def zeroToPgameRelabelling : toPgame 0 ≡r 0 :=
  Relabelling.isEmpty _
#align ordinal.zero_to_pgame_relabelling Ordinal.zeroToPgameRelabelling

noncomputable instance uniqueOneToPgameLeftMoves : Unique (toPgame 1).LeftMoves :=
  (Equiv.cast $ to_pgame_left_moves 1).unique
#align ordinal.unique_one_to_pgame_left_moves Ordinal.uniqueOneToPgameLeftMoves

@[simp]
theorem one_to_pgame_left_moves_default_eq :
    (default : (toPgame 1).LeftMoves) = @toLeftMovesToPgame 1 ⟨0, zero_lt_one⟩ :=
  rfl
#align ordinal.one_to_pgame_left_moves_default_eq Ordinal.one_to_pgame_left_moves_default_eq

@[simp]
theorem to_left_moves_one_to_pgame_symm (i) : (@toLeftMovesToPgame 1).symm i = ⟨0, zero_lt_one⟩ := by simp
#align ordinal.to_left_moves_one_to_pgame_symm Ordinal.to_left_moves_one_to_pgame_symm

theorem one_to_pgame_move_left (x) : (toPgame 1).moveLeft x = toPgame 0 := by simp
#align ordinal.one_to_pgame_move_left Ordinal.one_to_pgame_move_left

/-- `1.to_pgame` has the same moves as `1`. -/
noncomputable def oneToPgameRelabelling : toPgame 1 ≡r 1 :=
  ⟨Equiv.equivOfUnique _ _, Equiv.equivOfIsEmpty _ _, fun i => by simpa using zero_to_pgame_relabelling, isEmptyElim⟩
#align ordinal.one_to_pgame_relabelling Ordinal.oneToPgameRelabelling

theorem to_pgame_lf {a b : Ordinal} (h : a < b) : a.toPgame ⧏ b.toPgame := by
  convert move_left_lf (to_left_moves_to_pgame ⟨a, h⟩)
  rw [to_pgame_move_left]
#align ordinal.to_pgame_lf Ordinal.to_pgame_lf

theorem to_pgame_le {a b : Ordinal} (h : a ≤ b) : a.toPgame ≤ b.toPgame := by
  refine' le_iff_forall_lf.2 ⟨fun i => _, isEmptyElim⟩
  rw [to_pgame_move_left']
  exact to_pgame_lf ((to_left_moves_to_pgame_symm_lt i).trans_le h)
#align ordinal.to_pgame_le Ordinal.to_pgame_le

theorem to_pgame_lt {a b : Ordinal} (h : a < b) : a.toPgame < b.toPgame :=
  ⟨to_pgame_le h.le, to_pgame_lf h⟩
#align ordinal.to_pgame_lt Ordinal.to_pgame_lt

theorem to_pgame_nonneg (a : Ordinal) : 0 ≤ a.toPgame :=
  zeroToPgameRelabelling.ge.trans $ to_pgame_le $ Ordinal.zero_le a
#align ordinal.to_pgame_nonneg Ordinal.to_pgame_nonneg

@[simp]
theorem to_pgame_lf_iff {a b : Ordinal} : a.toPgame ⧏ b.toPgame ↔ a < b :=
  ⟨by
    contrapose
    rw [not_lt, not_lf]
    exact to_pgame_le, to_pgame_lf⟩
#align ordinal.to_pgame_lf_iff Ordinal.to_pgame_lf_iff

@[simp]
theorem to_pgame_le_iff {a b : Ordinal} : a.toPgame ≤ b.toPgame ↔ a ≤ b :=
  ⟨by
    contrapose
    rw [not_le, Pgame.not_le]
    exact to_pgame_lf, to_pgame_le⟩
#align ordinal.to_pgame_le_iff Ordinal.to_pgame_le_iff

@[simp]
theorem to_pgame_lt_iff {a b : Ordinal} : a.toPgame < b.toPgame ↔ a < b :=
  ⟨by
    contrapose
    rw [not_lt]
    exact fun h => not_lt_of_le (to_pgame_le h), to_pgame_lt⟩
#align ordinal.to_pgame_lt_iff Ordinal.to_pgame_lt_iff

@[simp]
theorem to_pgame_equiv_iff {a b : Ordinal} : (a.toPgame ≈ b.toPgame) ↔ a = b := by
  rw [Pgame.Equiv, le_antisymm_iff, to_pgame_le_iff, to_pgame_le_iff]
#align ordinal.to_pgame_equiv_iff Ordinal.to_pgame_equiv_iff

theorem to_pgame_injective : Function.Injective Ordinal.toPgame := fun a b h => to_pgame_equiv_iff.1 $ equiv_of_eq h
#align ordinal.to_pgame_injective Ordinal.to_pgame_injective

@[simp]
theorem to_pgame_eq_iff {a b : Ordinal} : a.toPgame = b.toPgame ↔ a = b :=
  to_pgame_injective.eq_iff
#align ordinal.to_pgame_eq_iff Ordinal.to_pgame_eq_iff

/-- The order embedding version of `to_pgame`. -/
@[simps]
noncomputable def toPgameEmbedding : Ordinal.{u} ↪o Pgame.{u} where
  toFun := Ordinal.toPgame
  inj' := to_pgame_injective
  map_rel_iff' := @to_pgame_le_iff
#align ordinal.to_pgame_embedding Ordinal.toPgameEmbedding

/-- The sum of ordinals as games corresponds to natural addition of ordinals. -/
theorem to_pgame_add : ∀ a b : Ordinal.{u}, a.toPgame + b.toPgame ≈ (a ♯ b).toPgame
  | a, b => by
    refine' ⟨le_of_forall_lf (fun i => _) isEmptyElim, le_of_forall_lf (fun i => _) isEmptyElim⟩
    · apply left_moves_add_cases i <;>
        intro i <;>
          let wf := to_left_moves_to_pgame_symm_lt i <;>
            try rw [add_move_left_inl] <;>
              try rw [add_move_left_inr] <;> rw [to_pgame_move_left', lf_congr_left (to_pgame_add _ _), to_pgame_lf_iff]
      · exact nadd_lt_nadd_right wf _
        
      · exact nadd_lt_nadd_left wf _
        
      
    · rw [to_pgame_move_left']
      rcases lt_nadd_iff.1 (to_left_moves_to_pgame_symm_lt i) with (⟨c, hc, hc'⟩ | ⟨c, hc, hc'⟩) <;>
        rw [← to_pgame_le_iff, ← le_congr_right (to_pgame_add _ _)] at hc' <;> apply lf_of_le_of_lf hc'
      · apply add_lf_add_right
        rwa [to_pgame_lf_iff]
        
      · apply add_lf_add_left
        rwa [to_pgame_lf_iff]
        
      
#align ordinal.to_pgame_add Ordinal.to_pgame_add

@[simp]
theorem to_pgame_add_mk (a b : Ordinal) : ⟦a.toPgame⟧ + ⟦b.toPgame⟧ = ⟦(a ♯ b).toPgame⟧ :=
  Quot.sound (to_pgame_add a b)
#align ordinal.to_pgame_add_mk Ordinal.to_pgame_add_mk

end Ordinal

