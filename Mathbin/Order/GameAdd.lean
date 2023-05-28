/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu

! This file was ported from Lean 3 source module order.game_add
! leanprover-community/mathlib commit fee218fb033b2fd390c447f8be27754bc9093be9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Sym.Sym2
import Mathbin.Logic.Relation

/-!
# Game addition relation

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines, given relations `rα : α → α → Prop` and `rβ : β → β → Prop`, a relation
`prod.game_add` on pairs, such that `game_add rα rβ x y` iff `x` can be reached from `y` by
decreasing either entry (with respect to `rα` and `rβ`). It is so called since it models the
subsequency relation on the addition of combinatorial games.

We also define `sym2.game_add`, which is the unordered pair analog of `prod.game_add`.

## Main definitions and results

- `prod.game_add`: the game addition relation on ordered pairs.
- `well_founded.prod_game_add`: formalizes induction on ordered pairs, where exactly one entry
  decreases at a time.

- `sym2.game_add`: the game addition relation on unordered pairs.
- `well_founded.sym2_game_add`: formalizes induction on unordered pairs, where exactly one entry
  decreases at a time.
-/


variable {α β : Type _} {rα : α → α → Prop} {rβ : β → β → Prop}

/-! ### `prod.game_add` -/


namespace Prod

variable (rα rβ)

#print Prod.GameAdd /-
/-- `prod.game_add rα rβ x y` means that `x` can be reached from `y` by decreasing either entry with
  respect to the relations `rα` and `rβ`.

  It is so called, as it models game addition within combinatorial game theory. If `rα a₁ a₂` means
  that `a₂ ⟶ a₁` is a valid move in game `α`, and `rβ b₁ b₂` means that `b₂ ⟶ b₁` is a valid move
  in game `β`, then `game_add rα rβ` specifies the valid moves in the juxtaposition of `α` and `β`:
  the player is free to choose one of the games and make a move in it, while leaving the other game
  unchanged.

  See `sym2.game_add` for the unordered pair analog. -/
inductive GameAdd : α × β → α × β → Prop
  | fst {a₁ a₂ b} : rα a₁ a₂ → game_add (a₁, b) (a₂, b)
  | snd {a b₁ b₂} : rβ b₁ b₂ → game_add (a, b₁) (a, b₂)
#align prod.game_add Prod.GameAdd
-/

/- warning: prod.game_add_iff -> Prod.gameAdd_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {rα : α -> α -> Prop} {rβ : β -> β -> Prop} {x : Prod.{u1, u2} α β} {y : Prod.{u1, u2} α β}, Iff (Prod.GameAdd.{u1, u2} α β rα rβ x y) (Or (And (rα (Prod.fst.{u1, u2} α β x) (Prod.fst.{u1, u2} α β y)) (Eq.{succ u2} β (Prod.snd.{u1, u2} α β x) (Prod.snd.{u1, u2} α β y))) (And (rβ (Prod.snd.{u1, u2} α β x) (Prod.snd.{u1, u2} α β y)) (Eq.{succ u1} α (Prod.fst.{u1, u2} α β x) (Prod.fst.{u1, u2} α β y))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {rα : α -> α -> Prop} {rβ : β -> β -> Prop} {x : Prod.{u2, u1} α β} {y : Prod.{u2, u1} α β}, Iff (Prod.GameAdd.{u2, u1} α β rα rβ x y) (Or (And (rα (Prod.fst.{u2, u1} α β x) (Prod.fst.{u2, u1} α β y)) (Eq.{succ u1} β (Prod.snd.{u2, u1} α β x) (Prod.snd.{u2, u1} α β y))) (And (rβ (Prod.snd.{u2, u1} α β x) (Prod.snd.{u2, u1} α β y)) (Eq.{succ u2} α (Prod.fst.{u2, u1} α β x) (Prod.fst.{u2, u1} α β y))))
Case conversion may be inaccurate. Consider using '#align prod.game_add_iff Prod.gameAdd_iffₓ'. -/
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

/- warning: prod.game_add_mk_iff -> Prod.gameAdd_mk_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {rα : α -> α -> Prop} {rβ : β -> β -> Prop} {a₁ : α} {a₂ : α} {b₁ : β} {b₂ : β}, Iff (Prod.GameAdd.{u1, u2} α β rα rβ (Prod.mk.{u1, u2} α β a₁ b₁) (Prod.mk.{u1, u2} α β a₂ b₂)) (Or (And (rα a₁ a₂) (Eq.{succ u2} β b₁ b₂)) (And (rβ b₁ b₂) (Eq.{succ u1} α a₁ a₂)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {rα : α -> α -> Prop} {rβ : β -> β -> Prop} {a₁ : α} {a₂ : α} {b₁ : β} {b₂ : β}, Iff (Prod.GameAdd.{u2, u1} α β rα rβ (Prod.mk.{u2, u1} α β a₁ b₁) (Prod.mk.{u2, u1} α β a₂ b₂)) (Or (And (rα a₁ a₂) (Eq.{succ u1} β b₁ b₂)) (And (rβ b₁ b₂) (Eq.{succ u2} α a₁ a₂)))
Case conversion may be inaccurate. Consider using '#align prod.game_add_mk_iff Prod.gameAdd_mk_iffₓ'. -/
theorem gameAdd_mk_iff {rα rβ} {a₁ a₂ : α} {b₁ b₂ : β} :
    GameAdd rα rβ (a₁, b₁) (a₂, b₂) ↔ rα a₁ a₂ ∧ b₁ = b₂ ∨ rβ b₁ b₂ ∧ a₁ = a₂ :=
  gameAdd_iff
#align prod.game_add_mk_iff Prod.gameAdd_mk_iff

/- warning: prod.game_add_swap_swap -> Prod.gameAdd_swap_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (rα : α -> α -> Prop) (rβ : β -> β -> Prop) (a : Prod.{u1, u2} α β) (b : Prod.{u1, u2} α β), Iff (Prod.GameAdd.{u2, u1} β α rβ rα (Prod.swap.{u1, u2} α β a) (Prod.swap.{u1, u2} α β b)) (Prod.GameAdd.{u1, u2} α β rα rβ a b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (rα : α -> α -> Prop) (rβ : β -> β -> Prop) (a : Prod.{u2, u1} α β) (b : Prod.{u2, u1} α β), Iff (Prod.GameAdd.{u1, u2} β α rβ rα (Prod.swap.{u2, u1} α β a) (Prod.swap.{u2, u1} α β b)) (Prod.GameAdd.{u2, u1} α β rα rβ a b)
Case conversion may be inaccurate. Consider using '#align prod.game_add_swap_swap Prod.gameAdd_swap_swapₓ'. -/
@[simp]
theorem gameAdd_swap_swap : ∀ a b : α × β, GameAdd rβ rα a.symm b.symm ↔ GameAdd rα rβ a b :=
  fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ => by rw [Prod.swap, game_add_mk_iff, game_add_mk_iff, or_comm']
#align prod.game_add_swap_swap Prod.gameAdd_swap_swap

/- warning: prod.game_add_swap_swap_mk -> Prod.gameAdd_swap_swap_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (rα : α -> α -> Prop) (rβ : β -> β -> Prop) (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), Iff (Prod.GameAdd.{u1, u2} α β rα rβ (Prod.mk.{u1, u2} α β a₁ b₁) (Prod.mk.{u1, u2} α β a₂ b₂)) (Prod.GameAdd.{u2, u1} β α rβ rα (Prod.mk.{u2, u1} β α b₁ a₁) (Prod.mk.{u2, u1} β α b₂ a₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (rα : α -> α -> Prop) (rβ : β -> β -> Prop) (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), Iff (Prod.GameAdd.{u2, u1} α β rα rβ (Prod.mk.{u2, u1} α β a₁ b₁) (Prod.mk.{u2, u1} α β a₂ b₂)) (Prod.GameAdd.{u1, u2} β α rβ rα (Prod.mk.{u1, u2} β α b₁ a₁) (Prod.mk.{u1, u2} β α b₂ a₂))
Case conversion may be inaccurate. Consider using '#align prod.game_add_swap_swap_mk Prod.gameAdd_swap_swap_mkₓ'. -/
theorem gameAdd_swap_swap_mk (a₁ a₂ : α) (b₁ b₂ : β) :
    GameAdd rα rβ (a₁, b₁) (a₂, b₂) ↔ GameAdd rβ rα (b₁, a₁) (b₂, a₂) :=
  gameAdd_swap_swap rβ rα (b₁, a₁) (b₂, a₂)
#align prod.game_add_swap_swap_mk Prod.gameAdd_swap_swap_mk

/- warning: prod.game_add_le_lex -> Prod.gameAdd_le_lex is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (rα : α -> α -> Prop) (rβ : β -> β -> Prop), LE.le.{max u1 u2} ((Prod.{u1, u2} α β) -> (Prod.{u1, u2} α β) -> Prop) (Pi.hasLe.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (fun (ᾰ : Prod.{u1, u2} α β) => (Prod.{u1, u2} α β) -> Prop) (fun (i : Prod.{u1, u2} α β) => Pi.hasLe.{max u1 u2, 0} (Prod.{u1, u2} α β) (fun (ᾰ : Prod.{u1, u2} α β) => Prop) (fun (i : Prod.{u1, u2} α β) => Prop.le))) (Prod.GameAdd.{u1, u2} α β rα rβ) (Prod.Lex.{u1, u2} α β rα rβ)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (rα : α -> α -> Prop) (rβ : β -> β -> Prop), LE.le.{max u2 u1} ((Prod.{u2, u1} α β) -> (Prod.{u2, u1} α β) -> Prop) (Pi.hasLe.{max u2 u1, max u2 u1} (Prod.{u2, u1} α β) (fun (ᾰ : Prod.{u2, u1} α β) => (Prod.{u2, u1} α β) -> Prop) (fun (i : Prod.{u2, u1} α β) => Pi.hasLe.{max u2 u1, 0} (Prod.{u2, u1} α β) (fun (ᾰ : Prod.{u2, u1} α β) => Prop) (fun (i : Prod.{u2, u1} α β) => Prop.le))) (Prod.GameAdd.{u2, u1} α β rα rβ) (Prod.Lex.{u2, u1} α β rα rβ)
Case conversion may be inaccurate. Consider using '#align prod.game_add_le_lex Prod.gameAdd_le_lexₓ'. -/
/-- `prod.game_add` is a `subrelation` of `prod.lex`. -/
theorem gameAdd_le_lex : GameAdd rα rβ ≤ Prod.Lex rα rβ := fun _ _ h =>
  h.rec (fun _ _ b => Prod.Lex.left b b) fun a _ _ => Prod.Lex.right a
#align prod.game_add_le_lex Prod.gameAdd_le_lex

/- warning: prod.rprod_le_trans_gen_game_add -> Prod.rprod_le_transGen_gameAdd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (rα : α -> α -> Prop) (rβ : β -> β -> Prop), LE.le.{max u1 u2} ((Prod.{u1, u2} α β) -> (Prod.{u1, u2} α β) -> Prop) (Pi.hasLe.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (fun (ᾰ : Prod.{u1, u2} α β) => (Prod.{u1, u2} α β) -> Prop) (fun (i : Prod.{u1, u2} α β) => Pi.hasLe.{max u1 u2, 0} (Prod.{u1, u2} α β) (fun (ᾰ : Prod.{u1, u2} α β) => Prop) (fun (i : Prod.{u1, u2} α β) => Prop.le))) (Prod.RProd.{u1, u2} α β rα rβ) (Relation.TransGen.{max u1 u2} (Prod.{u1, u2} α β) (Prod.GameAdd.{u1, u2} α β rα rβ))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (rα : α -> α -> Prop) (rβ : β -> β -> Prop), LE.le.{max u2 u1} ((Prod.{u2, u1} α β) -> (Prod.{u2, u1} α β) -> Prop) (Pi.hasLe.{max u2 u1, max u2 u1} (Prod.{u2, u1} α β) (fun (ᾰ : Prod.{u2, u1} α β) => (Prod.{u2, u1} α β) -> Prop) (fun (i : Prod.{u2, u1} α β) => Pi.hasLe.{max u2 u1, 0} (Prod.{u2, u1} α β) (fun (ᾰ : Prod.{u2, u1} α β) => Prop) (fun (i : Prod.{u2, u1} α β) => Prop.le))) (Prod.RProd.{u2, u1} α β rα rβ) (Relation.TransGen.{max u1 u2} (Prod.{u2, u1} α β) (Prod.GameAdd.{u2, u1} α β rα rβ))
Case conversion may be inaccurate. Consider using '#align prod.rprod_le_trans_gen_game_add Prod.rprod_le_transGen_gameAddₓ'. -/
/-- `prod.rprod` is a subrelation of the transitive closure of `prod.game_add`. -/
theorem rprod_le_transGen_gameAdd : RProd rα rβ ≤ Relation.TransGen (GameAdd rα rβ) := fun _ _ h =>
  h.rec
    (by
      intro _ _ _ _ hα hβ
      exact Relation.TransGen.tail (Relation.TransGen.single <| game_add.fst hα) (game_add.snd hβ))
#align prod.rprod_le_trans_gen_game_add Prod.rprod_le_transGen_gameAdd

end Prod

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

#print Prod.GameAdd.fix /-
/-- Recursion on the well-founded `prod.game_add` relation.

  Note that it's strictly more general to recurse on the lexicographic order instead. -/
def GameAdd.fix {C : α → β → Sort _} (hα : WellFounded rα) (hβ : WellFounded rβ)
    (IH : ∀ a₁ b₁, (∀ a₂ b₂, GameAdd rα rβ (a₂, b₂) (a₁, b₁) → C a₂ b₂) → C a₁ b₁) (a : α) (b : β) :
    C a b :=
  @WellFounded.fix (α × β) (fun x => C x.1 x.2) _ (hα.prod_gameAdd hβ)
    (fun ⟨x₁, x₂⟩ IH' => IH x₁ x₂ fun a' b' => IH' ⟨a', b'⟩) ⟨a, b⟩
#align prod.game_add.fix Prod.GameAdd.fix
-/

/- warning: prod.game_add.fix_eq -> Prod.GameAdd.fix_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {rα : α -> α -> Prop} {rβ : β -> β -> Prop} {C : α -> β -> Sort.{u3}} (hα : WellFounded.{succ u1} α rα) (hβ : WellFounded.{succ u2} β rβ) (IH : forall (a₁ : α) (b₁ : β), (forall (a₂ : α) (b₂ : β), (Prod.GameAdd.{u1, u2} α β rα rβ (Prod.mk.{u1, u2} α β a₂ b₂) (Prod.mk.{u1, u2} α β a₁ b₁)) -> (C a₂ b₂)) -> (C a₁ b₁)) (a : α) (b : β), Eq.{u3} (C a b) (Prod.GameAdd.fix.{u1, u2, u3} α β rα rβ (fun (a₂ : α) (b₂ : β) => C a₂ b₂) hα hβ IH a b) (IH a b (fun (a' : α) (b' : β) (h : Prod.GameAdd.{u1, u2} α β rα rβ (Prod.mk.{u1, u2} α β a' b') (Prod.mk.{u1, u2} α β a b)) => Prod.GameAdd.fix.{u1, u2, u3} α β rα rβ C hα hβ IH a' b'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {rα : α -> α -> Prop} {rβ : β -> β -> Prop} {C : α -> β -> Sort.{u3}} (hα : WellFounded.{succ u2} α rα) (hβ : WellFounded.{succ u1} β rβ) (IH : forall (a₁ : α) (b₁ : β), (forall (a₂ : α) (b₂ : β), (Prod.GameAdd.{u2, u1} α β rα rβ (Prod.mk.{u2, u1} α β a₂ b₂) (Prod.mk.{u2, u1} α β a₁ b₁)) -> (C a₂ b₂)) -> (C a₁ b₁)) (a : α) (b : β), Eq.{u3} (C a b) (Prod.GameAdd.fix.{u2, u1, u3} α β rα rβ (fun (a₂ : α) (b₂ : β) => C a₂ b₂) hα hβ IH a b) (IH a b (fun (a' : α) (b' : β) (h : Prod.GameAdd.{u2, u1} α β rα rβ (Prod.mk.{u2, u1} α β a' b') (Prod.mk.{u2, u1} α β a b)) => Prod.GameAdd.fix.{u2, u1, u3} α β rα rβ (fun (a₂ : α) (b₂ : β) => C a₂ b₂) hα hβ IH a' b'))
Case conversion may be inaccurate. Consider using '#align prod.game_add.fix_eq Prod.GameAdd.fix_eqₓ'. -/
theorem GameAdd.fix_eq {C : α → β → Sort _} (hα : WellFounded rα) (hβ : WellFounded rβ)
    (IH : ∀ a₁ b₁, (∀ a₂ b₂, GameAdd rα rβ (a₂, b₂) (a₁, b₁) → C a₂ b₂) → C a₁ b₁) (a : α) (b : β) :
    GameAdd.fix hα hβ IH a b = IH a b fun a' b' h => GameAdd.fix hα hβ IH a' b' :=
  WellFounded.fix_eq _ _ _
#align prod.game_add.fix_eq Prod.GameAdd.fix_eq

/- warning: prod.game_add.induction -> Prod.GameAdd.induction is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {rα : α -> α -> Prop} {rβ : β -> β -> Prop} {C : α -> β -> Prop}, (WellFounded.{succ u1} α rα) -> (WellFounded.{succ u2} β rβ) -> (forall (a₁ : α) (b₁ : β), (forall (a₂ : α) (b₂ : β), (Prod.GameAdd.{u1, u2} α β rα rβ (Prod.mk.{u1, u2} α β a₂ b₂) (Prod.mk.{u1, u2} α β a₁ b₁)) -> (C a₂ b₂)) -> (C a₁ b₁)) -> (forall (a : α) (b : β), C a b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {rα : α -> α -> Prop} {rβ : β -> β -> Prop} {C : α -> β -> Prop}, (WellFounded.{succ u2} α rα) -> (WellFounded.{succ u1} β rβ) -> (forall (a₁ : α) (b₁ : β), (forall (a₂ : α) (b₂ : β), (Prod.GameAdd.{u2, u1} α β rα rβ (Prod.mk.{u2, u1} α β a₂ b₂) (Prod.mk.{u2, u1} α β a₁ b₁)) -> (C a₂ b₂)) -> (C a₁ b₁)) -> (forall (a : α) (b : β), C a b)
Case conversion may be inaccurate. Consider using '#align prod.game_add.induction Prod.GameAdd.inductionₓ'. -/
/-- Induction on the well-founded `prod.game_add` relation.

  Note that it's strictly more general to induct on the lexicographic order instead. -/
theorem GameAdd.induction {C : α → β → Prop} :
    WellFounded rα →
      WellFounded rβ →
        (∀ a₁ b₁, (∀ a₂ b₂, GameAdd rα rβ (a₂, b₂) (a₁, b₁) → C a₂ b₂) → C a₁ b₁) → ∀ a b, C a b :=
  GameAdd.fix
#align prod.game_add.induction Prod.GameAdd.induction

end Prod

/-! ### `sym2.game_add` -/


namespace Sym2

#print Sym2.GameAdd /-
/-- `sym2.game_add rα x y` means that `x` can be reached from `y` by decreasing either entry with
  respect to the relation `rα`.

  See `prod.game_add` for the ordered pair analog. -/
def GameAdd (rα : α → α → Prop) : Sym2 α → Sym2 α → Prop :=
  Sym2.lift₂
    ⟨fun a₁ b₁ a₂ b₂ => Prod.GameAdd rα rα (a₁, b₁) (a₂, b₂) ∨ Prod.GameAdd rα rα (b₁, a₁) (a₂, b₂),
      fun a₁ b₁ a₂ b₂ =>
      by
      rw [Prod.gameAdd_swap_swap_mk _ _ b₁ b₂ a₁ a₂, Prod.gameAdd_swap_swap_mk _ _ a₁ b₂ b₁ a₂]
      simp [or_comm']⟩
#align sym2.game_add Sym2.GameAdd
-/

variable {rα}

#print Sym2.gameAdd_iff /-
theorem gameAdd_iff :
    ∀ {x y : α × α}, GameAdd rα ⟦x⟧ ⟦y⟧ ↔ Prod.GameAdd rα rα x y ∨ Prod.GameAdd rα rα x.symm y := by
  rintro ⟨_, _⟩ ⟨_, _⟩; rfl
#align sym2.game_add_iff Sym2.gameAdd_iff
-/

#print Sym2.gameAdd_mk'_iff /-
theorem gameAdd_mk'_iff {a₁ a₂ b₁ b₂ : α} :
    GameAdd rα ⟦(a₁, b₁)⟧ ⟦(a₂, b₂)⟧ ↔
      Prod.GameAdd rα rα (a₁, b₁) (a₂, b₂) ∨ Prod.GameAdd rα rα (b₁, a₁) (a₂, b₂) :=
  Iff.rfl
#align sym2.game_add_mk_iff Sym2.gameAdd_mk'_iff
-/

#print Prod.GameAdd.to_sym2 /-
theorem Prod.GameAdd.to_sym2 {a₁ a₂ b₁ b₂ : α} (h : Prod.GameAdd rα rα (a₁, b₁) (a₂, b₂)) :
    Sym2.GameAdd rα ⟦(a₁, b₁)⟧ ⟦(a₂, b₂)⟧ :=
  gameAdd_mk'_iff.2 <| Or.inl <| h
#align prod.game_add.to_sym2 Prod.GameAdd.to_sym2
-/

#print Sym2.GameAdd.fst /-
theorem GameAdd.fst {a₁ a₂ b : α} (h : rα a₁ a₂) : GameAdd rα ⟦(a₁, b)⟧ ⟦(a₂, b)⟧ :=
  (Prod.GameAdd.fst h).to_sym2
#align sym2.game_add.fst Sym2.GameAdd.fst
-/

#print Sym2.GameAdd.snd /-
theorem GameAdd.snd {a b₁ b₂ : α} (h : rα b₁ b₂) : GameAdd rα ⟦(a, b₁)⟧ ⟦(a, b₂)⟧ :=
  (Prod.GameAdd.snd h).to_sym2
#align sym2.game_add.snd Sym2.GameAdd.snd
-/

#print Sym2.GameAdd.fst_snd /-
theorem GameAdd.fst_snd {a₁ a₂ b : α} (h : rα a₁ a₂) : GameAdd rα ⟦(a₁, b)⟧ ⟦(b, a₂)⟧ := by
  rw [Sym2.eq_swap]; exact game_add.snd h
#align sym2.game_add.fst_snd Sym2.GameAdd.fst_snd
-/

#print Sym2.GameAdd.snd_fst /-
theorem GameAdd.snd_fst {a₁ a₂ b : α} (h : rα a₁ a₂) : GameAdd rα ⟦(b, a₁)⟧ ⟦(a₂, b)⟧ := by
  rw [Sym2.eq_swap]; exact game_add.fst h
#align sym2.game_add.snd_fst Sym2.GameAdd.snd_fst
-/

end Sym2

#print Acc.sym2_gameAdd /-
theorem Acc.sym2_gameAdd {a b} (ha : Acc rα a) (hb : Acc rα b) : Acc (Sym2.GameAdd rα) ⟦(a, b)⟧ :=
  by
  induction' ha with a ha iha generalizing b
  induction' hb with b hb ihb
  refine' Acc.intro _ fun s => _
  induction' s using Sym2.inductionOn with c d
  rintro ((rc | rd) | (rd | rc))
  · exact iha c rc ⟨b, hb⟩
  · exact ihb d rd
  · rw [Sym2.eq_swap]
    exact iha d rd ⟨b, hb⟩
  · rw [Sym2.eq_swap]
    exact ihb c rc
#align acc.sym2_game_add Acc.sym2_gameAdd
-/

#print WellFounded.sym2_gameAdd /-
/-- The `sym2.game_add` relation on well-founded inputs is well-founded. -/
theorem WellFounded.sym2_gameAdd (h : WellFounded rα) : WellFounded (Sym2.GameAdd rα) :=
  ⟨fun i => Sym2.inductionOn i fun x y => (h.apply x).sym2_gameAdd (h.apply y)⟩
#align well_founded.sym2_game_add WellFounded.sym2_gameAdd
-/

namespace Sym2

#print Sym2.GameAdd.fix /-
/-- Recursion on the well-founded `sym2.game_add` relation. -/
def GameAdd.fix {C : α → α → Sort _} (hr : WellFounded rα)
    (IH : ∀ a₁ b₁, (∀ a₂ b₂, Sym2.GameAdd rα ⟦(a₂, b₂)⟧ ⟦(a₁, b₁)⟧ → C a₂ b₂) → C a₁ b₁) (a b : α) :
    C a b :=
  @WellFounded.fix (α × α) (fun x => C x.1 x.2) _ hr.sym2_gameAdd.of_quotient_lift₂
    (fun ⟨x₁, x₂⟩ IH' => IH x₁ x₂ fun a' b' => IH' ⟨a', b'⟩) (a, b)
#align sym2.game_add.fix Sym2.GameAdd.fix
-/

#print Sym2.GameAdd.fix_eq /-
theorem GameAdd.fix_eq {C : α → α → Sort _} (hr : WellFounded rα)
    (IH : ∀ a₁ b₁, (∀ a₂ b₂, Sym2.GameAdd rα ⟦(a₂, b₂)⟧ ⟦(a₁, b₁)⟧ → C a₂ b₂) → C a₁ b₁) (a b : α) :
    GameAdd.fix hr IH a b = IH a b fun a' b' h => GameAdd.fix hr IH a' b' :=
  WellFounded.fix_eq _ _ _
#align sym2.game_add.fix_eq Sym2.GameAdd.fix_eq
-/

#print Sym2.GameAdd.induction /-
/-- Induction on the well-founded `sym2.game_add` relation. -/
theorem GameAdd.induction {C : α → α → Prop} :
    WellFounded rα →
      (∀ a₁ b₁, (∀ a₂ b₂, Sym2.GameAdd rα ⟦(a₂, b₂)⟧ ⟦(a₁, b₁)⟧ → C a₂ b₂) → C a₁ b₁) →
        ∀ a b, C a b :=
  GameAdd.fix
#align sym2.game_add.induction Sym2.GameAdd.induction
-/

end Sym2

