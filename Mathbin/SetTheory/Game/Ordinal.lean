/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathbin.SetTheory.Game.Pgame
import Mathbin.SetTheory.Ordinal.Basic

/-!
# Ordinals as games

We define the canonical map `ordinal → pgame`, where every ordinal is mapped to the game whose left
set consists of all previous ordinals.

# Main declarations

- `ordinal.to_pgame`: The canonical map between ordinals and pre-games.
- `ordinal.to_pgame_embedding`: The order embedding version of the previous map.

# Todo

- Extend this map to `game` and `surreal`.
-/


-- mathport name: «expr ≈ »
local infixl:0 " ≈ " => Pgame.Equiv

universe u

namespace Ordinal

/-- Converts an ordinal into the corresponding pre-game. -/
noncomputable def toPgame : ∀ o : Ordinal.{u}, Pgame.{u}
  | o =>
    ⟨o.out.α, Pempty, fun x =>
      let hwf := Ordinal.typein_lt_self x
      (typein (· < ·) x).toPgame,
      Pempty.elimₓ⟩

theorem to_pgame_def (o : Ordinal) : o.toPgame = ⟨o.out.α, Pempty, fun x => (typein (· < ·) x).toPgame, Pempty.elimₓ⟩ :=
  by
  rw [to_pgame]

@[simp]
theorem to_pgame_left_moves (o : Ordinal) : o.toPgame.LeftMoves = o.out.α := by
  rw [to_pgame, Pgame.LeftMoves]

@[simp]
theorem to_pgame_right_moves (o : Ordinal) : o.toPgame.RightMoves = Pempty := by
  rw [to_pgame, Pgame.RightMoves]

instance : IsEmpty (toPgame 0).LeftMoves := by
  rw [to_pgame_left_moves]
  infer_instance

instance (o : Ordinal) : IsEmpty o.toPgame.RightMoves := by
  rw [to_pgame_right_moves]
  infer_instance

/-- Converts an ordinal less than `o` into a move for the `pgame` corresponding to `o`, and vice
versa. -/
noncomputable def toLeftMovesToPgame {o : Ordinal} : Set.Iio o ≃ o.toPgame.LeftMoves :=
  (enumIsoOut o).toEquiv.trans (Equivₓ.cast (to_pgame_left_moves o).symm)

@[simp]
theorem to_left_moves_to_pgame_symm_lt {o : Ordinal} (i : o.toPgame.LeftMoves) : ↑(toLeftMovesToPgame.symm i) < o :=
  (toLeftMovesToPgame.symm i).Prop

theorem to_pgame_move_left_heq {o : Ordinal} : HEq o.toPgame.moveLeft fun x : o.out.α => (typein (· < ·) x).toPgame :=
  by
  rw [to_pgame]
  rfl

@[simp]
theorem to_pgame_move_left' {o : Ordinal} i : o.toPgame.moveLeft i = (toLeftMovesToPgame.symm i).val.toPgame :=
  (congr_heq to_pgame_move_left_heq.symm (cast_heq _ i)).symm

theorem to_pgame_move_left {o : Ordinal} i : o.toPgame.moveLeft (toLeftMovesToPgame i) = i.val.toPgame := by
  simp

theorem to_pgame_lt {a b : Ordinal} (h : a < b) : a.toPgame < b.toPgame := by
  convert Pgame.move_left_lt (to_left_moves_to_pgame ⟨a, h⟩)
  rw [to_pgame_move_left]

theorem to_pgame_le {a b : Ordinal} (h : a ≤ b) : a.toPgame ≤ b.toPgame :=
  Pgame.le_def.2
    ⟨fun i =>
      Or.inl
        ⟨toLeftMovesToPgame ⟨(toLeftMovesToPgame.symm i).val, (to_left_moves_to_pgame_symm_lt i).trans_le h⟩, by
          simp ⟩,
      isEmptyElim⟩

@[simp]
theorem to_pgame_lt_iff {a b : Ordinal} : a.toPgame < b.toPgame ↔ a < b :=
  ⟨by
    contrapose
    rw [not_ltₓ, Pgame.not_lt]
    exact to_pgame_le, to_pgame_lt⟩

@[simp]
theorem to_pgame_le_iff {a b : Ordinal} : a.toPgame ≤ b.toPgame ↔ a ≤ b :=
  ⟨by
    contrapose
    rw [not_leₓ, Pgame.not_le]
    exact to_pgame_lt, to_pgame_le⟩

@[simp]
theorem to_pgame_equiv_iff {a b : Ordinal} : (a.toPgame ≈ b.toPgame) ↔ a = b := by
  rw [Pgame.Equiv, le_antisymm_iffₓ, to_pgame_le_iff, to_pgame_le_iff]

theorem to_pgame_injective : Function.Injective Ordinal.toPgame := fun a b h => by
  by_contra hne
  cases' lt_or_gt_of_neₓ hne with hlt hlt <;>
    · have := to_pgame_lt hlt
      rw [h] at this
      exact Pgame.lt_irrefl _ this
      

/-- The order embedding version of `to_pgame`. -/
@[simps]
noncomputable def toPgameEmbedding : Ordinal.{u} ↪o Pgame.{u} where
  toFun := Ordinal.toPgame
  inj' := to_pgame_injective
  map_rel_iff' := @to_pgame_le_iff

end Ordinal

