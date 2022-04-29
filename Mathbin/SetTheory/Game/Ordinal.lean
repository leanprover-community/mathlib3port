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
- Prove that `birthday o.to_pgame = o`.
-/


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

instance : IsEmpty (0 : Ordinal).toPgame.LeftMoves := by
  rw [to_pgame_left_moves]
  infer_instance

instance (o : Ordinal) : IsEmpty o.toPgame.RightMoves := by
  rw [to_pgame_right_moves]
  infer_instance

/-- Converts a member of `o.out.α` into a move for the `pgame` corresponding to `o`, and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toLeftMovesToPgame {o : Ordinal} : o.out.α ≃ o.toPgame.LeftMoves :=
  Equivₓ.cast (to_pgame_left_moves o).symm

theorem to_pgame_move_left_heq {o : Ordinal} : HEq o.toPgame.moveLeft fun x : o.out.α => (typein (· < ·) x).toPgame :=
  by
  rw [to_pgame]
  rfl

@[simp]
theorem to_pgame_move_left {o : Ordinal} (i : o.out.α) :
    o.toPgame.moveLeft (toLeftMovesToPgame i) = (typein (· < ·) i).toPgame := by
  rw [to_left_moves_to_pgame]
  exact congr_fun_heq _ to_pgame_move_left_heq i

theorem to_pgame_lt {a b : Ordinal} (h : a < b) : a.toPgame < b.toPgame := by
  convert Pgame.move_left_lt (to_left_moves_to_pgame (enum (· < ·) a _))
  · rw [to_pgame_move_left, typein_enum]
    
  · rwa [type_lt]
    

theorem to_pgame_le {a b : Ordinal} (h : a ≤ b) : a.toPgame ≤ b.toPgame := by
  rw [Pgame.le_def]
  refine'
    ⟨fun i => Or.inl ⟨to_left_moves_to_pgame (enum (· < ·) (typein (· < ·) (to_left_moves_to_pgame.symm i)) _), _⟩,
      isEmptyElim⟩
  · rw [type_lt]
    apply lt_of_lt_of_leₓ _ h
    simp_rw [← type_lt a]
    apply typein_lt_type
    
  · rw [← to_left_moves_to_pgame.apply_symm_apply i, to_pgame_move_left]
    simp
    

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

