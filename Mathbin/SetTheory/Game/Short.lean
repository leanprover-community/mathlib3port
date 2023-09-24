/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Data.Fintype.Basic
import SetTheory.Cardinal.Cofinality
import SetTheory.Game.Birthday

#align_import set_theory.game.short from "leanprover-community/mathlib"@"728ef9dbb281241906f25cbeb30f90d83e0bb451"

/-!
# Short games

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A combinatorial game is `short` [Conway, ch.9][conway2001] if it has only finitely many positions.
In particular, this means there is a finite set of moves at every point.

We prove that the order relations `≤` and `<`, and the equivalence relation `≈`, are decidable on
short games, although unfortunately in practice `dec_trivial` doesn't seem to be able to
prove anything using these instances.
-/


universe u

open scoped SetTheory.PGame

namespace SetTheory.PGame

#print SetTheory.PGame.Short /-
/-- A short game is a game with a finite set of moves at every turn. -/
inductive SetTheory.PGame.Short : SetTheory.PGame.{u} → Type (u + 1)
  |
  mk :
    ∀ {α β : Type u} {L : α → SetTheory.PGame.{u}} {R : β → SetTheory.PGame.{u}}
      (sL : ∀ i : α, short (L i)) (sR : ∀ j : β, short (R j)) [Fintype α] [Fintype β],
      short ⟨α, β, L, R⟩
#align pgame.short SetTheory.PGame.Short
-/

#print SetTheory.PGame.subsingleton_short /-
instance SetTheory.PGame.subsingleton_short :
    ∀ x : SetTheory.PGame, Subsingleton (SetTheory.PGame.Short x)
  | mk xl xr xL xR =>
    ⟨fun a b => by
      cases a; cases b
      congr
      · funext
        apply @Subsingleton.elim _ (subsingleton_short (xL x))
      · funext
        apply @Subsingleton.elim _ (subsingleton_short (xR x))⟩
decreasing_by pgame_wf_tac
#align pgame.subsingleton_short SetTheory.PGame.subsingleton_short
-/

#print SetTheory.PGame.Short.mk' /-
/-- A synonym for `short.mk` that specifies the pgame in an implicit argument. -/
def SetTheory.PGame.Short.mk' {x : SetTheory.PGame} [Fintype x.LeftMoves] [Fintype x.RightMoves]
    (sL : ∀ i : x.LeftMoves, SetTheory.PGame.Short (x.moveLeft i))
    (sR : ∀ j : x.RightMoves, SetTheory.PGame.Short (x.moveRight j)) : SetTheory.PGame.Short x := by
  (cases x; dsimp at *) <;> exact short.mk sL sR
#align pgame.short.mk' SetTheory.PGame.Short.mk'
-/

attribute [class] short

#print SetTheory.PGame.fintypeLeft /-
/-- Extracting the `fintype` instance for the indexing type for Left's moves in a short game.
This is an unindexed typeclass, so it can't be made a global instance.
-/
def SetTheory.PGame.fintypeLeft {α β : Type u} {L : α → SetTheory.PGame.{u}}
    {R : β → SetTheory.PGame.{u}} [S : SetTheory.PGame.Short ⟨α, β, L, R⟩] : Fintype α := by
  cases' S with _ _ _ _ _ _ F _; exact F
#align pgame.fintype_left SetTheory.PGame.fintypeLeft
-/

attribute [local instance] fintype_left

#print SetTheory.PGame.fintypeLeftMoves /-
instance SetTheory.PGame.fintypeLeftMoves (x : SetTheory.PGame) [S : SetTheory.PGame.Short x] :
    Fintype x.LeftMoves := by cases x; dsimp; infer_instance
#align pgame.fintype_left_moves SetTheory.PGame.fintypeLeftMoves
-/

#print SetTheory.PGame.fintypeRight /-
/-- Extracting the `fintype` instance for the indexing type for Right's moves in a short game.
This is an unindexed typeclass, so it can't be made a global instance.
-/
def SetTheory.PGame.fintypeRight {α β : Type u} {L : α → SetTheory.PGame.{u}}
    {R : β → SetTheory.PGame.{u}} [S : SetTheory.PGame.Short ⟨α, β, L, R⟩] : Fintype β := by
  cases' S with _ _ _ _ _ _ _ F; exact F
#align pgame.fintype_right SetTheory.PGame.fintypeRight
-/

attribute [local instance] fintype_right

#print SetTheory.PGame.fintypeRightMoves /-
instance SetTheory.PGame.fintypeRightMoves (x : SetTheory.PGame) [S : SetTheory.PGame.Short x] :
    Fintype x.RightMoves := by cases x; dsimp; infer_instance
#align pgame.fintype_right_moves SetTheory.PGame.fintypeRightMoves
-/

#print SetTheory.PGame.moveLeftShort /-
instance SetTheory.PGame.moveLeftShort (x : SetTheory.PGame) [S : SetTheory.PGame.Short x]
    (i : x.LeftMoves) : SetTheory.PGame.Short (x.moveLeft i) := by cases' S with _ _ _ _ L _ _ _;
  apply L
#align pgame.move_left_short SetTheory.PGame.moveLeftShort
-/

#print SetTheory.PGame.moveLeftShort' /-
/-- Extracting the `short` instance for a move by Left.
This would be a dangerous instance potentially introducing new metavariables
in typeclass search, so we only make it an instance locally.
-/
def SetTheory.PGame.moveLeftShort' {xl xr} (xL xR)
    [S : SetTheory.PGame.Short (SetTheory.PGame.mk xl xr xL xR)] (i : xl) :
    SetTheory.PGame.Short (xL i) := by cases' S with _ _ _ _ L _ _ _; apply L
#align pgame.move_left_short' SetTheory.PGame.moveLeftShort'
-/

attribute [local instance] move_left_short'

#print SetTheory.PGame.moveRightShort /-
instance SetTheory.PGame.moveRightShort (x : SetTheory.PGame) [S : SetTheory.PGame.Short x]
    (j : x.RightMoves) : SetTheory.PGame.Short (x.moveRight j) := by cases' S with _ _ _ _ _ R _ _;
  apply R
#align pgame.move_right_short SetTheory.PGame.moveRightShort
-/

#print SetTheory.PGame.moveRightShort' /-
/-- Extracting the `short` instance for a move by Right.
This would be a dangerous instance potentially introducing new metavariables
in typeclass search, so we only make it an instance locally.
-/
def SetTheory.PGame.moveRightShort' {xl xr} (xL xR)
    [S : SetTheory.PGame.Short (SetTheory.PGame.mk xl xr xL xR)] (j : xr) :
    SetTheory.PGame.Short (xR j) := by cases' S with _ _ _ _ _ R _ _; apply R
#align pgame.move_right_short' SetTheory.PGame.moveRightShort'
-/

attribute [local instance] move_right_short'

#print SetTheory.PGame.short_birthday /-
theorem SetTheory.PGame.short_birthday :
    ∀ (x : SetTheory.PGame.{u}) [SetTheory.PGame.Short x], x.birthday < Ordinal.omega
  | ⟨xl, xr, xL, xR⟩, hs => by
    haveI := hs
    rcases hs with ⟨sL, sR⟩
    rw [birthday, max_lt_iff]
    constructor;
    all_goals
      rw [← Cardinal.ord_aleph0]
      refine'
        Cardinal.lsub_lt_ord_of_isRegular.{u, u} Cardinal.isRegular_aleph0
          (Cardinal.lt_aleph0_of_finite _) fun i => _
      rw [Cardinal.ord_aleph0]
      apply short_birthday _
    · exact move_left_short' xL xR i
    · exact move_right_short' xL xR i
#align pgame.short_birthday SetTheory.PGame.short_birthday
-/

#print SetTheory.PGame.Short.ofIsEmpty /-
/-- This leads to infinite loops if made into an instance. -/
def SetTheory.PGame.Short.ofIsEmpty {l r xL xR} [IsEmpty l] [IsEmpty r] :
    SetTheory.PGame.Short (SetTheory.PGame.mk l r xL xR) :=
  SetTheory.PGame.Short.mk isEmptyElim isEmptyElim
#align pgame.short.of_is_empty SetTheory.PGame.Short.ofIsEmpty
-/

#print SetTheory.PGame.short0 /-
instance SetTheory.PGame.short0 : SetTheory.PGame.Short 0 :=
  SetTheory.PGame.Short.ofIsEmpty
#align pgame.short_0 SetTheory.PGame.short0
-/

#print SetTheory.PGame.short1 /-
instance SetTheory.PGame.short1 : SetTheory.PGame.Short 1 :=
  SetTheory.PGame.Short.mk (fun i => by cases i; infer_instance) fun j => by cases j
#align pgame.short_1 SetTheory.PGame.short1
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print SetTheory.PGame.ListShort /-
/-- Evidence that every `pgame` in a list is `short`. -/
inductive SetTheory.PGame.ListShort : List SetTheory.PGame.{u} → Type (u + 1)
  | nil : list_short []
  |
  cons :
    ∀ (hd : SetTheory.PGame.{u}) [SetTheory.PGame.Short hd] (tl : List SetTheory.PGame.{u})
      [list_short tl], list_short (hd::tl)
#align pgame.list_short SetTheory.PGame.ListShort
-/

attribute [class] list_short

attribute [instance] list_short.nil list_short.cons

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print SetTheory.PGame.listShortNthLe /-
instance SetTheory.PGame.listShortNthLe :
    ∀ (L : List SetTheory.PGame.{u}) [SetTheory.PGame.ListShort L] (i : Fin (List.length L)),
      SetTheory.PGame.Short (List.nthLe L i i.is_lt)
  | [], _, n => by exfalso; rcases n with ⟨_, ⟨⟩⟩
  | hd::tl, @list_short.cons _ S _ _, ⟨0, _⟩ => S
  | hd::tl, @list_short.cons _ _ _ S, ⟨n + 1, h⟩ =>
    @list_short_nth_le tl S ⟨n, (add_lt_add_iff_right 1).mp h⟩
#align pgame.list_short_nth_le SetTheory.PGame.listShortNthLe
-/

#print SetTheory.PGame.shortOfLists /-
instance SetTheory.PGame.shortOfLists :
    ∀ (L R : List SetTheory.PGame) [SetTheory.PGame.ListShort L] [SetTheory.PGame.ListShort R],
      SetTheory.PGame.Short (SetTheory.PGame.ofLists L R)
  | L, R, _, _ => by
    skip; apply short.mk
    · intros; infer_instance
    · intros; apply SetTheory.PGame.listShortNthLe
#align pgame.short_of_lists SetTheory.PGame.shortOfLists
-/

#print SetTheory.PGame.shortOfRelabelling /-
-- where does the subtype.val come from?
/-- If `x` is a short game, and `y` is a relabelling of `x`, then `y` is also short. -/
def SetTheory.PGame.shortOfRelabelling :
    ∀ {x y : SetTheory.PGame.{u}} (R : SetTheory.PGame.Relabelling x y)
      (S : SetTheory.PGame.Short x), SetTheory.PGame.Short y
  | x, y, ⟨L, R, rL, rR⟩, S => by
    skip
    haveI := Fintype.ofEquiv _ L
    haveI := Fintype.ofEquiv _ R
    exact
      short.mk'
        (fun i => by rw [← L.right_inv i]; apply short_of_relabelling (rL (L.symm i)) inferInstance)
        fun j => by simpa using short_of_relabelling (rR (R.symm j)) inferInstance
#align pgame.short_of_relabelling SetTheory.PGame.shortOfRelabelling
-/

#print SetTheory.PGame.shortNeg /-
instance SetTheory.PGame.shortNeg :
    ∀ (x : SetTheory.PGame.{u}) [SetTheory.PGame.Short x], SetTheory.PGame.Short (-x)
  | mk xl xr xL xR, _ => by skip; exact short.mk (fun i => short_neg _) fun i => short_neg _
decreasing_by pgame_wf_tac
#align pgame.short_neg SetTheory.PGame.shortNeg
-/

#print SetTheory.PGame.shortAdd /-
instance SetTheory.PGame.shortAdd :
    ∀ (x y : SetTheory.PGame.{u}) [SetTheory.PGame.Short x] [SetTheory.PGame.Short y],
      SetTheory.PGame.Short (x + y)
  | mk xl xr xL xR, mk yl yr yL yR, _, _ => by
    skip
    apply short.mk;
    all_goals
      rintro ⟨i⟩
      · apply short_add
      · change short (mk xl xr xL xR + _); apply short_add
decreasing_by pgame_wf_tac
#align pgame.short_add SetTheory.PGame.shortAdd
-/

#print SetTheory.PGame.shortNat /-
instance SetTheory.PGame.shortNat : ∀ n : ℕ, SetTheory.PGame.Short n
  | 0 => SetTheory.PGame.short0
  | n + 1 => @SetTheory.PGame.shortAdd _ _ (short_nat n) SetTheory.PGame.short1
#align pgame.short_nat SetTheory.PGame.shortNat
-/

#print SetTheory.PGame.shortBit0 /-
instance SetTheory.PGame.shortBit0 (x : SetTheory.PGame.{u}) [SetTheory.PGame.Short x] :
    SetTheory.PGame.Short (bit0 x) := by dsimp [bit0]; infer_instance
#align pgame.short_bit0 SetTheory.PGame.shortBit0
-/

#print SetTheory.PGame.shortBit1 /-
instance SetTheory.PGame.shortBit1 (x : SetTheory.PGame.{u}) [SetTheory.PGame.Short x] :
    SetTheory.PGame.Short (bit1 x) := by dsimp [bit1]; infer_instance
#align pgame.short_bit1 SetTheory.PGame.shortBit1
-/

#print SetTheory.PGame.leLFDecidable /-
/-- Auxiliary construction of decidability instances.
We build `decidable (x ≤ y)` and `decidable (x ⧏ y)` in a simultaneous induction.
Instances for the two projections separately are provided below.
-/
def SetTheory.PGame.leLFDecidable :
    ∀ (x y : SetTheory.PGame.{u}) [SetTheory.PGame.Short x] [SetTheory.PGame.Short y],
      Decidable (x ≤ y) × Decidable (x ⧏ y)
  | mk xl xr xL xR, mk yl yr yL yR, shortx, shorty =>
    by
    skip
    constructor
    · refine' @decidable_of_iff' _ _ mk_le_mk (id _)
      apply @And.decidable _ _ _ _
      · apply @Fintype.decidableForallFintype xl _ _ (by infer_instance)
        intro i
        apply (@le_lf_decidable _ _ _ _).2 <;> infer_instance
      · apply @Fintype.decidableForallFintype yr _ _ (by infer_instance)
        intro i
        apply (@le_lf_decidable _ _ _ _).2 <;> infer_instance
    · refine' @decidable_of_iff' _ _ mk_lf_mk (id _)
      apply @Or.decidable _ _ _ _
      · apply @Fintype.decidableExistsFintype yl _ _ (by infer_instance)
        intro i
        apply (@le_lf_decidable _ _ _ _).1 <;> infer_instance
      · apply @Fintype.decidableExistsFintype xr _ _ (by infer_instance)
        intro i
        apply (@le_lf_decidable _ _ _ _).1 <;> infer_instance
decreasing_by pgame_wf_tac
#align pgame.le_lf_decidable SetTheory.PGame.leLFDecidable
-/

#print SetTheory.PGame.leDecidable /-
instance SetTheory.PGame.leDecidable (x y : SetTheory.PGame.{u}) [SetTheory.PGame.Short x]
    [SetTheory.PGame.Short y] : Decidable (x ≤ y) :=
  (SetTheory.PGame.leLFDecidable x y).1
#align pgame.le_decidable SetTheory.PGame.leDecidable
-/

#print SetTheory.PGame.lfDecidable /-
instance SetTheory.PGame.lfDecidable (x y : SetTheory.PGame.{u}) [SetTheory.PGame.Short x]
    [SetTheory.PGame.Short y] : Decidable (x ⧏ y) :=
  (SetTheory.PGame.leLFDecidable x y).2
#align pgame.lf_decidable SetTheory.PGame.lfDecidable
-/

#print SetTheory.PGame.ltDecidable /-
instance SetTheory.PGame.ltDecidable (x y : SetTheory.PGame.{u}) [SetTheory.PGame.Short x]
    [SetTheory.PGame.Short y] : Decidable (x < y) :=
  And.decidable
#align pgame.lt_decidable SetTheory.PGame.ltDecidable
-/

#print SetTheory.PGame.equivDecidable /-
instance SetTheory.PGame.equivDecidable (x y : SetTheory.PGame.{u}) [SetTheory.PGame.Short x]
    [SetTheory.PGame.Short y] : Decidable (x ≈ y) :=
  And.decidable
#align pgame.equiv_decidable SetTheory.PGame.equivDecidable
-/

example : SetTheory.PGame.Short 0 := by infer_instance

example : SetTheory.PGame.Short 1 := by infer_instance

example : SetTheory.PGame.Short 2 := by infer_instance

example : SetTheory.PGame.Short (-2) := by infer_instance

example : SetTheory.PGame.Short (SetTheory.PGame.ofLists [0] [1]) := by infer_instance

example : SetTheory.PGame.Short (SetTheory.PGame.ofLists [-2, -1] [1]) := by infer_instance

example : SetTheory.PGame.Short (0 + 0) := by infer_instance

example : Decidable ((1 : SetTheory.PGame) ≤ 1) := by infer_instance

-- No longer works since definitional reduction of well-founded definitions has been restricted.
-- example : (0 : pgame) ≤ 0 := dec_trivial
-- example : (1 : pgame) ≤ 1 := dec_trivial
end SetTheory.PGame

