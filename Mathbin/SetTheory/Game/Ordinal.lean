/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathbin.SetTheory.Game.Basic
import Mathbin.SetTheory.Ordinal.NaturalOps

#align_import set_theory.game.ordinal from "leanprover-community/mathlib"@"08b63ab58a6ec1157ebeafcbbe6c7a3fb3c9f6d5"

/-!
# Ordinals as games

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define the canonical map `ordinal → pgame`, where every ordinal is mapped to the game whose left
set consists of all previous ordinals.

The map to surreals is defined in `ordinal.to_surreal`.

# Main declarations

- `ordinal.to_pgame`: The canonical map between ordinals and pre-games.
- `ordinal.to_pgame_embedding`: The order embedding version of the previous map.
-/


universe u

open SetTheory.PGame

open scoped NaturalOps SetTheory.PGame

namespace Ordinal

#print Ordinal.toPGame /-
/-- Converts an ordinal into the corresponding pre-game. -/
noncomputable def toPGame : Ordinal.{u} → SetTheory.PGame.{u}
  | o =>
    ⟨o.out.α, PEmpty, fun x =>
      let hwf := Ordinal.typein_lt_self x
      (typein (· < ·) x).toPGame,
      PEmpty.elim⟩
#align ordinal.to_pgame Ordinal.toPGame
-/

#print Ordinal.toPGame_def /-
theorem toPGame_def (o : Ordinal) :
    o.toPGame = ⟨o.out.α, PEmpty, fun x => (typein (· < ·) x).toPGame, PEmpty.elim⟩ := by
  rw [to_pgame]
#align ordinal.to_pgame_def Ordinal.toPGame_def
-/

#print Ordinal.toPGame_leftMoves /-
@[simp]
theorem toPGame_leftMoves (o : Ordinal) : o.toPGame.LeftMoves = o.out.α := by
  rw [to_pgame, left_moves]
#align ordinal.to_pgame_left_moves Ordinal.toPGame_leftMoves
-/

#print Ordinal.toPGame_rightMoves /-
@[simp]
theorem toPGame_rightMoves (o : Ordinal) : o.toPGame.RightMoves = PEmpty := by
  rw [to_pgame, right_moves]
#align ordinal.to_pgame_right_moves Ordinal.toPGame_rightMoves
-/

#print Ordinal.isEmpty_zero_toPGame_leftMoves /-
instance isEmpty_zero_toPGame_leftMoves : IsEmpty (toPGame 0).LeftMoves := by
  rw [to_pgame_left_moves]; infer_instance
#align ordinal.is_empty_zero_to_pgame_left_moves Ordinal.isEmpty_zero_toPGame_leftMoves
-/

#print Ordinal.isEmpty_toPGame_rightMoves /-
instance isEmpty_toPGame_rightMoves (o : Ordinal) : IsEmpty o.toPGame.RightMoves := by
  rw [to_pgame_right_moves]; infer_instance
#align ordinal.is_empty_to_pgame_right_moves Ordinal.isEmpty_toPGame_rightMoves
-/

#print Ordinal.toLeftMovesToPGame /-
/-- Converts an ordinal less than `o` into a move for the `pgame` corresponding to `o`, and vice
versa. -/
noncomputable def toLeftMovesToPGame {o : Ordinal} : Set.Iio o ≃ o.toPGame.LeftMoves :=
  (enumIsoOut o).toEquiv.trans (Equiv.cast (toPGame_leftMoves o).symm)
#align ordinal.to_left_moves_to_pgame Ordinal.toLeftMovesToPGame
-/

#print Ordinal.toLeftMovesToPGame_symm_lt /-
@[simp]
theorem toLeftMovesToPGame_symm_lt {o : Ordinal} (i : o.toPGame.LeftMoves) :
    ↑(toLeftMovesToPGame.symm i) < o :=
  (toLeftMovesToPGame.symm i).Prop
#align ordinal.to_left_moves_to_pgame_symm_lt Ordinal.toLeftMovesToPGame_symm_lt
-/

#print Ordinal.toPGame_moveLeft_hEq /-
theorem toPGame_moveLeft_hEq {o : Ordinal} :
    HEq o.toPGame.moveLeft fun x : o.out.α => (typein (· < ·) x).toPGame := by rw [to_pgame]; rfl
#align ordinal.to_pgame_move_left_heq Ordinal.toPGame_moveLeft_hEq
-/

#print Ordinal.toPGame_moveLeft' /-
@[simp]
theorem toPGame_moveLeft' {o : Ordinal} (i) :
    o.toPGame.moveLeft i = (toLeftMovesToPGame.symm i).val.toPGame :=
  (congr_heq toPGame_moveLeft_hEq.symm (cast_hEq _ i)).symm
#align ordinal.to_pgame_move_left' Ordinal.toPGame_moveLeft'
-/

#print Ordinal.toPGame_moveLeft /-
theorem toPGame_moveLeft {o : Ordinal} (i) :
    o.toPGame.moveLeft (toLeftMovesToPGame i) = i.val.toPGame := by simp
#align ordinal.to_pgame_move_left Ordinal.toPGame_moveLeft
-/

#print Ordinal.zeroToPgameRelabelling /-
/-- `0.to_pgame` has the same moves as `0`. -/
noncomputable def zeroToPgameRelabelling : toPGame 0 ≡r 0 :=
  SetTheory.PGame.Relabelling.isEmpty _
#align ordinal.zero_to_pgame_relabelling Ordinal.zeroToPgameRelabelling
-/

#print Ordinal.uniqueOneToPgameLeftMoves /-
noncomputable instance uniqueOneToPgameLeftMoves : Unique (toPGame 1).LeftMoves :=
  (Equiv.cast <| toPGame_leftMoves 1).unique
#align ordinal.unique_one_to_pgame_left_moves Ordinal.uniqueOneToPgameLeftMoves
-/

#print Ordinal.one_toPGame_leftMoves_default_eq /-
@[simp]
theorem one_toPGame_leftMoves_default_eq :
    (default : (toPGame 1).LeftMoves) = @toLeftMovesToPGame 1 ⟨0, zero_lt_one⟩ :=
  rfl
#align ordinal.one_to_pgame_left_moves_default_eq Ordinal.one_toPGame_leftMoves_default_eq
-/

#print Ordinal.to_leftMoves_one_toPGame_symm /-
@[simp]
theorem to_leftMoves_one_toPGame_symm (i) : (@toLeftMovesToPGame 1).symm i = ⟨0, zero_lt_one⟩ := by
  simp
#align ordinal.to_left_moves_one_to_pgame_symm Ordinal.to_leftMoves_one_toPGame_symm
-/

#print Ordinal.one_toPGame_moveLeft /-
theorem one_toPGame_moveLeft (x) : (toPGame 1).moveLeft x = toPGame 0 := by simp
#align ordinal.one_to_pgame_move_left Ordinal.one_toPGame_moveLeft
-/

#print Ordinal.oneToPGameRelabelling /-
/-- `1.to_pgame` has the same moves as `1`. -/
noncomputable def oneToPGameRelabelling : toPGame 1 ≡r 1 :=
  ⟨Equiv.equivOfUnique _ _, Equiv.equivOfIsEmpty _ _, fun i => by
    simpa using zero_to_pgame_relabelling, isEmptyElim⟩
#align ordinal.one_to_pgame_relabelling Ordinal.oneToPGameRelabelling
-/

#print Ordinal.toPGame_lf /-
theorem toPGame_lf {a b : Ordinal} (h : a < b) : a.toPGame ⧏ b.toPGame := by
  convert move_left_lf (to_left_moves_to_pgame ⟨a, h⟩); rw [to_pgame_move_left]
#align ordinal.to_pgame_lf Ordinal.toPGame_lf
-/

#print Ordinal.toPGame_le /-
theorem toPGame_le {a b : Ordinal} (h : a ≤ b) : a.toPGame ≤ b.toPGame :=
  by
  refine' le_iff_forall_lf.2 ⟨fun i => _, isEmptyElim⟩
  rw [to_pgame_move_left']
  exact to_pgame_lf ((to_left_moves_to_pgame_symm_lt i).trans_le h)
#align ordinal.to_pgame_le Ordinal.toPGame_le
-/

#print Ordinal.toPGame_lt /-
theorem toPGame_lt {a b : Ordinal} (h : a < b) : a.toPGame < b.toPGame :=
  ⟨toPGame_le h.le, toPGame_lf h⟩
#align ordinal.to_pgame_lt Ordinal.toPGame_lt
-/

#print Ordinal.toPGame_nonneg /-
theorem toPGame_nonneg (a : Ordinal) : 0 ≤ a.toPGame :=
  zeroToPgameRelabelling.ge.trans <| toPGame_le <| Ordinal.zero_le a
#align ordinal.to_pgame_nonneg Ordinal.toPGame_nonneg
-/

#print Ordinal.toPGame_lf_iff /-
@[simp]
theorem toPGame_lf_iff {a b : Ordinal} : a.toPGame ⧏ b.toPGame ↔ a < b :=
  ⟨by contrapose; rw [not_lt, not_lf]; exact to_pgame_le, toPGame_lf⟩
#align ordinal.to_pgame_lf_iff Ordinal.toPGame_lf_iff
-/

#print Ordinal.toPGame_le_iff /-
@[simp]
theorem toPGame_le_iff {a b : Ordinal} : a.toPGame ≤ b.toPGame ↔ a ≤ b :=
  ⟨by contrapose; rw [not_le, SetTheory.PGame.not_le]; exact to_pgame_lf, toPGame_le⟩
#align ordinal.to_pgame_le_iff Ordinal.toPGame_le_iff
-/

#print Ordinal.toPGame_lt_iff /-
@[simp]
theorem toPGame_lt_iff {a b : Ordinal} : a.toPGame < b.toPGame ↔ a < b :=
  ⟨by contrapose; rw [not_lt]; exact fun h => not_lt_of_le (to_pgame_le h), toPGame_lt⟩
#align ordinal.to_pgame_lt_iff Ordinal.toPGame_lt_iff
-/

#print Ordinal.toPGame_equiv_iff /-
@[simp]
theorem toPGame_equiv_iff {a b : Ordinal} : (a.toPGame ≈ b.toPGame) ↔ a = b := by
  rw [SetTheory.PGame.Equiv, le_antisymm_iff, to_pgame_le_iff, to_pgame_le_iff]
#align ordinal.to_pgame_equiv_iff Ordinal.toPGame_equiv_iff
-/

#print Ordinal.toPGame_injective /-
theorem toPGame_injective : Function.Injective Ordinal.toPGame := fun a b h =>
  toPGame_equiv_iff.1 <| SetTheory.PGame.equiv_of_eq h
#align ordinal.to_pgame_injective Ordinal.toPGame_injective
-/

#print Ordinal.toPGame_eq_iff /-
@[simp]
theorem toPGame_eq_iff {a b : Ordinal} : a.toPGame = b.toPGame ↔ a = b :=
  toPGame_injective.eq_iff
#align ordinal.to_pgame_eq_iff Ordinal.toPGame_eq_iff
-/

#print Ordinal.toPGameEmbedding /-
/-- The order embedding version of `to_pgame`. -/
@[simps]
noncomputable def toPGameEmbedding : Ordinal.{u} ↪o SetTheory.PGame.{u}
    where
  toFun := Ordinal.toPGame
  inj' := toPGame_injective
  map_rel_iff' := @toPGame_le_iff
#align ordinal.to_pgame_embedding Ordinal.toPGameEmbedding
-/

#print Ordinal.toPGame_add /-
/-- The sum of ordinals as games corresponds to natural addition of ordinals. -/
theorem toPGame_add : ∀ a b : Ordinal.{u}, a.toPGame + b.toPGame ≈ (a ♯ b).toPGame
  | a, b =>
    by
    refine' ⟨le_of_forall_lf (fun i => _) isEmptyElim, le_of_forall_lf (fun i => _) isEmptyElim⟩
    · apply left_moves_add_cases i <;> intro i <;> let wf := to_left_moves_to_pgame_symm_lt i <;>
            try rw [add_move_left_inl] <;> try rw [add_move_left_inr] <;>
        rw [to_pgame_move_left', lf_congr_left (to_pgame_add _ _), to_pgame_lf_iff]
      · exact nadd_lt_nadd_right wf _
      · exact nadd_lt_nadd_left wf _
    · rw [to_pgame_move_left']
      rcases lt_nadd_iff.1 (to_left_moves_to_pgame_symm_lt i) with (⟨c, hc, hc'⟩ | ⟨c, hc, hc'⟩) <;>
          rw [← to_pgame_le_iff, ← le_congr_right (to_pgame_add _ _)] at hc'  <;>
        apply lf_of_le_of_lf hc'
      · apply add_lf_add_right
        rwa [to_pgame_lf_iff]
      · apply add_lf_add_left
        rwa [to_pgame_lf_iff]
decreasing_by solve_by_elim [PSigma.Lex.left, PSigma.Lex.right]
#align ordinal.to_pgame_add Ordinal.toPGame_add
-/

#print Ordinal.toPGame_add_mk' /-
@[simp]
theorem toPGame_add_mk' (a b : Ordinal) : ⟦a.toPGame⟧ + ⟦b.toPGame⟧ = ⟦(a ♯ b).toPGame⟧ :=
  Quot.sound (toPGame_add a b)
#align ordinal.to_pgame_add_mk Ordinal.toPGame_add_mk'
-/

end Ordinal

