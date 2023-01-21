/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu

! This file was ported from Lean 3 source module order.game_add
! leanprover-community/mathlib commit 2445c98ae4b87eabebdde552593519b9b6dc350c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Basic
import Mathbin.Logic.Relation

/-!
# Game addition relation

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines, given relations `rα : α → α → Prop` and `rβ : β → β → Prop`, a relation
`prod.game_add` on pairs, such that `game_add rα rβ x y` iff `x` can be reached from `y` by
decreasing either entry (with respect to `rα` and `rβ`). It is so called since it models the
subsequency relation on the addition of combinatorial games.

## Main definitions and results

- `prod.game_add`: the game addition relation on ordered pairs.
- `well_founded.prod_game_add`: formalizes induction on ordered pairs, where exactly one entry
  decreases at a time.

## Todo

- Add custom `induction` and `fix` lemmas.
- Define `sym2.game_add`.
-/


variable {α β : Type _} (rα : α → α → Prop) (rβ : β → β → Prop)

namespace Prod

#print Prod.GameAdd /-
/-- The "addition of games" relation in combinatorial game theory, on the product type: if
  `rα a' a` means that `a ⟶ a'` is a valid move in game `α`, and `rβ b' b` means that `b ⟶ b'`
  is a valid move in game `β`, then `game_add rα rβ` specifies the valid moves in the juxtaposition
  of `α` and `β`: the player is free to choose one of the games and make a move in it,
  while leaving the other game unchanged. -/
inductive GameAdd : α × β → α × β → Prop
  | fst {a' a b} : rα a' a → game_add (a', b) (a, b)
  | snd {a b' b} : rβ b' b → game_add (a, b') (a, b)
#align prod.game_add Prod.GameAdd
-/

#print Prod.gameAdd_le_lex /-
/-- `game_add` is a `subrelation` of `prod.lex`. -/
theorem gameAdd_le_lex : GameAdd rα rβ ≤ Prod.Lex rα rβ := fun _ _ h =>
  h.rec (fun _ _ b => Prod.Lex.left b b) fun a _ _ => Prod.Lex.right a
#align prod.game_add_le_lex Prod.gameAdd_le_lex
-/

#print Prod.rprod_le_transGen_gameAdd /-
/-- `prod.rprod` is a subrelation of the transitive closure of `game_add`. -/
theorem rprod_le_transGen_gameAdd : Prod.RProd rα rβ ≤ Relation.TransGen (GameAdd rα rβ) :=
  fun _ _ h =>
  h.rec
    (by
      intro _ _ _ _ hα hβ
      exact Relation.TransGen.tail (Relation.TransGen.single <| game_add.fst hα) (game_add.snd hβ))
#align prod.rprod_le_trans_gen_game_add Prod.rprod_le_transGen_gameAdd
-/

end Prod

variable {rα rβ}

/- warning: acc.prod_game_add -> Acc.prod_gameAdd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {rα : α -> α -> Prop} {rβ : β -> β -> Prop} {a : α} {b : β}, (Acc.{succ u1} α rα a) -> (Acc.{succ u2} β rβ b) -> (Acc.{max (succ u1) (succ u2)} (Prod.{u1, u2} α β) (Prod.GameAdd.{u1, u2} α β rα rβ) (Prod.mk.{u1, u2} α β a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {rα : α -> α -> Prop} {rβ : β -> β -> Prop} {a : α} {b : β}, (Acc.{succ u2} α rα a) -> (Acc.{succ u1} β rβ b) -> (Acc.{max (succ u1) (succ u2)} (Prod.{u2, u1} α β) (Prod.GameAdd.{u2, u1} α β rα rβ) (Prod.mk.{u2, u1} α β a b))
Case conversion may be inaccurate. Consider using '#align acc.prod_game_add Acc.prod_gameAddₓ'. -/
/-- If `a` is accessible under `rα` and `b` is accessible under `rβ`, then `(a, b)` is
  accessible under `prod.game_add rα rβ`. Notice that `prod.lex_accessible` requires the
  stronger condition `∀ b, acc rβ b`. -/
theorem Acc.prod_gameAdd {a b} (ha : Acc rα a) (hb : Acc rβ b) : Acc (Prod.GameAdd rα rβ) (a, b) :=
  by
  induction' ha with a ha iha generalizing b
  induction' hb with b hb ihb
  refine' Acc.intro _ fun h => _
  rintro (⟨ra⟩ | ⟨rb⟩)
  exacts[iha _ ra (Acc.intro b hb), ihb _ rb]
#align acc.prod_game_add Acc.prod_gameAdd

/- warning: well_founded.prod_game_add -> WellFounded.prod_gameAdd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {rα : α -> α -> Prop} {rβ : β -> β -> Prop}, (WellFounded.{succ u1} α rα) -> (WellFounded.{succ u2} β rβ) -> (WellFounded.{max (succ u1) (succ u2)} (Prod.{u1, u2} α β) (Prod.GameAdd.{u1, u2} α β rα rβ))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {rα : α -> α -> Prop} {rβ : β -> β -> Prop}, (WellFounded.{succ u2} α rα) -> (WellFounded.{succ u1} β rβ) -> (WellFounded.{max (succ u1) (succ u2)} (Prod.{u2, u1} α β) (Prod.GameAdd.{u2, u1} α β rα rβ))
Case conversion may be inaccurate. Consider using '#align well_founded.prod_game_add WellFounded.prod_gameAddₓ'. -/
/-- The sum of two well-founded games is well-founded. -/
theorem WellFounded.prod_gameAdd (hα : WellFounded rα) (hβ : WellFounded rβ) :
    WellFounded (Prod.GameAdd rα rβ) :=
  ⟨fun ⟨a, b⟩ => (hα.apply a).prod_game_add (hβ.apply b)⟩
#align well_founded.prod_game_add WellFounded.prod_gameAdd

