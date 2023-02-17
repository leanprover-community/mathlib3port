/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu

! This file was ported from Lean 3 source module order.game_add
! leanprover-community/mathlib commit 740acc0e6f9adf4423f92a485d0456fc271482da
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

- Define `sym2.game_add`.
-/


variable {α β : Type _} (rα : α → α → Prop) (rβ : β → β → Prop)

namespace Prod

#print Prod.GameAdd /-
/-- `prod.game_add rα rβ x y` means that `x` can be reached from `y` by decreasing either entry with
  respect to the relations `rα` and `rβ`.

  It is so called, as it models game addition within combinatorial game theory. If `rα a₁ a₂` means
  that `a₂ ⟶ a₁` is a valid move in game `α`, and `rβ b₁ b₂` means that `b₂ ⟶ b₁` is a valid move
  in game `β`, then `game_add rα rβ` specifies the valid moves in the juxtaposition of `α` and `β`:
  the player is free to choose one of the games and make a move in it, while leaving the other game
  unchanged. -/
inductive GameAdd : α × β → α × β → Prop
  | fst {a₁ a₂ b} : rα a₁ a₂ → game_add (a₁, b) (a₂, b)
  | snd {a b₁ b₂} : rβ b₁ b₂ → game_add (a, b₁) (a, b₂)
#align prod.game_add Prod.GameAdd
-/

theorem gameAdd_iff {rα rβ} {x y : α × β} :
    GameAdd rα rβ x y ↔ rα x.1 y.1 ∧ x.2 = y.2 ∨ rβ x.2 y.2 ∧ x.1 = y.1 :=
  by
  constructor
  · rintro (@⟨a₁, a₂, b, h⟩ | @⟨a, b₁, b₂, h⟩)
    exacts[Or.inl ⟨h, rfl⟩, Or.inr ⟨h, rfl⟩]
  · revert x y
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ (⟨h, rfl : b₁ = b₂⟩ | ⟨h, rfl : a₁ = a₂⟩)
    exacts[game_add.fst h, game_add.snd h]
#align prod.game_add_iff Prod.gameAdd_iff

theorem gameAdd_mk_iff {rα rβ} {a₁ a₂ : α} {b₁ b₂ : β} :
    GameAdd rα rβ (a₁, b₁) (a₂, b₂) ↔ rα a₁ a₂ ∧ b₁ = b₂ ∨ rβ b₁ b₂ ∧ a₁ = a₂ :=
  gameAdd_iff
#align prod.game_add_mk_iff Prod.gameAdd_mk_iff

@[simp]
theorem gameAdd_swap_swap : ∀ a b : α × β, GameAdd rβ rα a.symm b.symm ↔ GameAdd rα rβ a b :=
  fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ => by rw [Prod.swap, game_add_mk_iff, game_add_mk_iff, or_comm']
#align prod.game_add_swap_swap Prod.gameAdd_swap_swap

#print Prod.gameAdd_le_lex /-
/-- `prod.game_add` is a `subrelation` of `prod.lex`. -/
theorem gameAdd_le_lex : GameAdd rα rβ ≤ Prod.Lex rα rβ := fun _ _ h =>
  h.rec (fun _ _ b => Prod.Lex.left b b) fun a _ _ => Prod.Lex.right a
#align prod.game_add_le_lex Prod.gameAdd_le_lex
-/

#print Prod.rprod_le_transGen_gameAdd /-
/-- `prod.rprod` is a subrelation of the transitive closure of `prod.game_add`. -/
theorem rprod_le_transGen_gameAdd : RProd rα rβ ≤ Relation.TransGen (GameAdd rα rβ) := fun _ _ h =>
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
/-- The `prod.game_add` relation on well-founded inputs is well-founded.

  In particular, the sum of two well-founded games is well-founded. -/
theorem WellFounded.prod_gameAdd (hα : WellFounded rα) (hβ : WellFounded rβ) :
    WellFounded (Prod.GameAdd rα rβ) :=
  ⟨fun ⟨a, b⟩ => (hα.apply a).prod_gameAdd (hβ.apply b)⟩
#align well_founded.prod_game_add WellFounded.prod_gameAdd

namespace Prod

/-- Recursion on the well-founded `prod.game_add` relation.

  Note that it's strictly more general to recurse on the lexicographic order instead. -/
def GameAdd.fix {C : α → β → Sort _} (hα : WellFounded rα) (hβ : WellFounded rβ)
    (IH : ∀ a₁ b₁, (∀ a₂ b₂, GameAdd rα rβ (a₂, b₂) (a₁, b₁) → C a₂ b₂) → C a₁ b₁) (a : α) (b : β) :
    C a b :=
  @WellFounded.fix (α × β) (fun x => C x.1 x.2) _ (hα.prod_gameAdd hβ)
    (fun ⟨x₁, x₂⟩ IH' => IH x₁ x₂ fun a' b' => IH' ⟨a', b'⟩) ⟨a, b⟩
#align prod.game_add.fix Prod.GameAdd.fix

theorem GameAdd.fix_eq {C : α → β → Sort _} (hα : WellFounded rα) (hβ : WellFounded rβ)
    (IH : ∀ a₁ b₁, (∀ a₂ b₂, GameAdd rα rβ (a₂, b₂) (a₁, b₁) → C a₂ b₂) → C a₁ b₁) (a : α) (b : β) :
    GameAdd.fix hα hβ IH a b = IH a b fun a' b' h => GameAdd.fix hα hβ IH a' b' :=
  by
  rw [game_add.fix, WellFounded.fix_eq]
  rfl
#align prod.game_add.fix_eq Prod.GameAdd.fix_eq

/-- Induction on the well-founded `prod.game_add` relation.

  Note that it's strictly more general to induct on the lexicographic order instead. -/
theorem GameAdd.induction {C : α → β → Prop} :
    WellFounded rα →
      WellFounded rβ →
        (∀ a₁ b₁, (∀ a₂ b₂, GameAdd rα rβ (a₂, b₂) (a₁, b₁) → C a₂ b₂) → C a₁ b₁) → ∀ a b, C a b :=
  GameAdd.fix
#align prod.game_add.induction Prod.GameAdd.induction

end Prod

