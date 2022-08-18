/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathbin.Logic.Relation
import Mathbin.Order.Basic

/-!
# Game addition relation

This file defines, given relations `rα : α → α → Prop` and `rβ : β → β → Prop`, a relation
`prod.game_add` on pairs, such that `game_add rα rβ x y` iff `x` can be reached from `y` by
decreasing either entry (with respect to `rα` and `rβ`). It is so called since it models the
subsequency relation on the addition of combinatorial games.

## Main definitions and results

- `prod.game_add`: the game addition relation on ordered pairs.
- `well_founded.game_add`: formalizes induction on ordered pairs, where exactly one entry decreases
  at a time.

## Todo

- Add custom `induction` and `fix` lemmas.
- Define `sym2.game_add`.
-/


variable {α β : Type _} (rα : α → α → Prop) (rβ : β → β → Prop)

namespace Prod

/-- The "addition of games" relation in combinatorial game theory, on the product type: if
  `rα a' a` means that `a ⟶ a'` is a valid move in game `α`, and `rβ b' b` means that `b ⟶ b'`
  is a valid move in game `β`, then `game_add rα rβ` specifies the valid moves in the juxtaposition
  of `α` and `β`: the player is free to choose one of the games and make a move in it,
  while leaving the other game unchanged. -/
inductive GameAdd : α × β → α × β → Prop
  | fst {a' a b} : rα a' a → game_add (a', b) (a, b)
  | snd {a b' b} : rβ b' b → game_add (a, b') (a, b)

/-- `game_add` is a `subrelation` of `prod.lex`. -/
theorem game_add_le_lex : GameAdd rα rβ ≤ Prod.Lex rα rβ := fun _ _ h =>
  h.rec (fun _ _ b => Prod.Lex.left b b) fun a _ _ => Prod.Lex.right a

/-- `prod.rprod` is a subrelation of the transitive closure of `game_add`. -/
theorem rprod_le_trans_gen_game_add : Prod.Rprod rα rβ ≤ Relation.TransGen (GameAdd rα rβ) := fun _ _ h =>
  h.rec
    (by
      intro _ _ _ _ hα hβ
      exact Relation.TransGen.tail (Relation.TransGen.single <| game_add.fst hα) (game_add.snd hβ))

end Prod

variable {rα rβ}

/-- If `a` is accessible under `rα` and `b` is accessible under `rβ`, then `(a, b)` is
  accessible under `prod.game_add rα rβ`. Notice that `prod.lex_accessible` requires the
  stronger condition `∀ b, acc rβ b`. -/
theorem Acc.prod_game_add {a b} (ha : Acc rα a) (hb : Acc rβ b) : Acc (Prod.GameAdd rα rβ) (a, b) := by
  induction' ha with a ha iha generalizing b
  induction' hb with b hb ihb
  refine' Acc.intro _ fun h => _
  rintro (⟨_, _, _, ra⟩ | ⟨_, _, _, rb⟩)
  exacts[iha _ ra (Acc.intro b hb), ihb _ rb]

/-- The sum of two well-founded games is well-founded. -/
theorem WellFounded.prod_game_add (hα : WellFounded rα) (hβ : WellFounded rβ) : WellFounded (Prod.GameAdd rα rβ) :=
  ⟨fun ⟨a, b⟩ => (hα.apply a).prod_game_add (hβ.apply b)⟩

