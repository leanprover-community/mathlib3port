/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Isabel Longbottom, Scott Morrison
-/
import Data.Fin.Basic
import Data.List.Basic
import Logic.Relation
import Logic.Small.Defs
import Order.GameAdd

#align_import set_theory.game.pgame from "leanprover-community/mathlib"@"8900d545017cd21961daa2a1734bb658ef52c618"

/-!
# Combinatorial (pre-)games.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The basic theory of combinatorial games, following Conway's book `On Numbers and Games`. We
construct "pregames", define an ordering and arithmetic operations on them, then show that the
operations descend to "games", defined via the equivalence relation `p ≈ q ↔ p ≤ q ∧ q ≤ p`.

The surreal numbers will be built as a quotient of a subtype of pregames.

A pregame (`pgame` below) is axiomatised via an inductive type, whose sole constructor takes two
types (thought of as indexing the possible moves for the players Left and Right), and a pair of
functions out of these types to `pgame` (thought of as describing the resulting game after making a
move).

Combinatorial games themselves, as a quotient of pregames, are constructed in `game.lean`.

## Conway induction

By construction, the induction principle for pregames is exactly "Conway induction". That is, to
prove some predicate `pgame → Prop` holds for all pregames, it suffices to prove that for every
pregame `g`, if the predicate holds for every game resulting from making a move, then it also holds
for `g`.

While it is often convenient to work "by induction" on pregames, in some situations this becomes
awkward, so we also define accessor functions `pgame.left_moves`, `pgame.right_moves`,
`pgame.move_left` and `pgame.move_right`. There is a relation `pgame.subsequent p q`, saying that
`p` can be reached by playing some non-empty sequence of moves starting from `q`, an instance
`well_founded subsequent`, and a local tactic `pgame_wf_tac` which is helpful for discharging proof
obligations in inductive proofs relying on this relation.

## Order properties

Pregames have both a `≤` and a `<` relation, satisfying the usual properties of a `preorder`. The
relation `0 < x` means that `x` can always be won by Left, while `0 ≤ x` means that `x` can be won
by Left as the second player.

It turns out to be quite convenient to define various relations on top of these. We define the "less
or fuzzy" relation `x ⧏ y` as `¬ y ≤ x`, the equivalence relation `x ≈ y` as `x ≤ y ∧ y ≤ x`, and
the fuzzy relation `x ‖ y` as `x ⧏ y ∧ y ⧏ x`. If `0 ⧏ x`, then `x` can be won by Left as the
first player. If `x ≈ 0`, then `x` can be won by the second player. If `x ‖ 0`, then `x` can be won
by the first player.

Statements like `zero_le_lf`, `zero_lf_le`, etc. unfold these definitions. The theorems `le_def` and
`lf_def` give a recursive characterisation of each relation in terms of themselves two moves later.
The theorems `zero_le`, `zero_lf`, etc. also take into account that `0` has no moves.

Later, games will be defined as the quotient by the `≈` relation; that is to say, the
`antisymmetrization` of `pgame`.

## Algebraic structures

We next turn to defining the operations necessary to make games into a commutative additive group.
Addition is defined for $x = \{xL | xR\}$ and $y = \{yL | yR\}$ by $x + y = \{xL + y, x + yL | xR +
y, x + yR\}$. Negation is defined by $\{xL | xR\} = \{-xR | -xL\}$.

The order structures interact in the expected way with addition, so we have
```
theorem le_iff_sub_nonneg {x y : pgame} : x ≤ y ↔ 0 ≤ y - x := sorry
theorem lt_iff_sub_pos {x y : pgame} : x < y ↔ 0 < y - x := sorry
```

We show that these operations respect the equivalence relation, and hence descend to games. At the
level of games, these operations satisfy all the laws of a commutative group. To prove the necessary
equivalence relations at the level of pregames, we introduce the notion of a `relabelling` of a
game, and show, for example, that there is a relabelling between `x + (y + z)` and `(x + y) + z`.

## Future work

* The theory of dominated and reversible positions, and unique normal form for short games.
* Analysis of basic domineering positions.
* Hex.
* Temperature.
* The development of surreal numbers, based on this development of combinatorial games, is still
  quite incomplete.

## References

The material here is all drawn from
* [Conway, *On numbers and games*][conway2001]

An interested reader may like to formalise some of the material from
* [Andreas Blass, *A game semantics for linear logic*][MR1167694]
* [André Joyal, *Remarques sur la théorie des jeux à deux personnes*][joyal1997]
-/


open Function Relation

universe u

/-! ### Pre-game moves -/


#print SetTheory.PGame /-
/-- The type of pre-games, before we have quotiented
  by equivalence (`pgame.setoid`). In ZFC, a combinatorial game is constructed from
  two sets of combinatorial games that have been constructed at an earlier
  stage. To do this in type theory, we say that a pre-game is built
  inductively from two families of pre-games indexed over any type
  in Type u. The resulting type `pgame.{u}` lives in `Type (u+1)`,
  reflecting that it is a proper class in ZFC. -/
inductive SetTheory.PGame : Type (u + 1)
  | mk : ∀ α β : Type u, (α → SetTheory.PGame) → (β → SetTheory.PGame) → SetTheory.PGame
#align pgame SetTheory.PGame
-/

namespace SetTheory.PGame

#print SetTheory.PGame.LeftMoves /-
/-- The indexing type for allowable moves by Left. -/
def SetTheory.PGame.LeftMoves : SetTheory.PGame → Type u
  | mk l _ _ _ => l
#align pgame.left_moves SetTheory.PGame.LeftMoves
-/

#print SetTheory.PGame.RightMoves /-
/-- The indexing type for allowable moves by Right. -/
def SetTheory.PGame.RightMoves : SetTheory.PGame → Type u
  | mk _ r _ _ => r
#align pgame.right_moves SetTheory.PGame.RightMoves
-/

#print SetTheory.PGame.moveLeft /-
/-- The new game after Left makes an allowed move. -/
def SetTheory.PGame.moveLeft : ∀ g : SetTheory.PGame, SetTheory.PGame.LeftMoves g → SetTheory.PGame
  | mk l _ L _ => L
#align pgame.move_left SetTheory.PGame.moveLeft
-/

#print SetTheory.PGame.moveRight /-
/-- The new game after Right makes an allowed move. -/
def SetTheory.PGame.moveRight :
    ∀ g : SetTheory.PGame, SetTheory.PGame.RightMoves g → SetTheory.PGame
  | mk _ r _ R => R
#align pgame.move_right SetTheory.PGame.moveRight
-/

#print SetTheory.PGame.leftMoves_mk /-
@[simp]
theorem SetTheory.PGame.leftMoves_mk {xl xr xL xR} :
    (⟨xl, xr, xL, xR⟩ : SetTheory.PGame).LeftMoves = xl :=
  rfl
#align pgame.left_moves_mk SetTheory.PGame.leftMoves_mk
-/

#print SetTheory.PGame.moveLeft_mk /-
@[simp]
theorem SetTheory.PGame.moveLeft_mk {xl xr xL xR} :
    (⟨xl, xr, xL, xR⟩ : SetTheory.PGame).moveLeft = xL :=
  rfl
#align pgame.move_left_mk SetTheory.PGame.moveLeft_mk
-/

#print SetTheory.PGame.rightMoves_mk /-
@[simp]
theorem SetTheory.PGame.rightMoves_mk {xl xr xL xR} :
    (⟨xl, xr, xL, xR⟩ : SetTheory.PGame).RightMoves = xr :=
  rfl
#align pgame.right_moves_mk SetTheory.PGame.rightMoves_mk
-/

#print SetTheory.PGame.moveRight_mk /-
@[simp]
theorem SetTheory.PGame.moveRight_mk {xl xr xL xR} :
    (⟨xl, xr, xL, xR⟩ : SetTheory.PGame).moveRight = xR :=
  rfl
#align pgame.move_right_mk SetTheory.PGame.moveRight_mk
-/

#print SetTheory.PGame.ofLists /-
-- TODO define this at the level of games, as well, and perhaps also for finsets of games.
/-- Construct a pre-game from list of pre-games describing the available moves for Left and Right.
-/
def SetTheory.PGame.ofLists (L R : List SetTheory.PGame.{u}) : SetTheory.PGame.{u} :=
  SetTheory.PGame.mk (ULift (Fin L.length)) (ULift (Fin R.length))
    (fun i => L.nthLe i.down i.down.is_lt) fun j => R.nthLe j.down j.down.Prop
#align pgame.of_lists SetTheory.PGame.ofLists
-/

#print SetTheory.PGame.leftMoves_ofLists /-
theorem SetTheory.PGame.leftMoves_ofLists (L R : List SetTheory.PGame) :
    (SetTheory.PGame.ofLists L R).LeftMoves = ULift (Fin L.length) :=
  rfl
#align pgame.left_moves_of_lists SetTheory.PGame.leftMoves_ofLists
-/

#print SetTheory.PGame.rightMoves_ofLists /-
theorem SetTheory.PGame.rightMoves_ofLists (L R : List SetTheory.PGame) :
    (SetTheory.PGame.ofLists L R).RightMoves = ULift (Fin R.length) :=
  rfl
#align pgame.right_moves_of_lists SetTheory.PGame.rightMoves_ofLists
-/

#print SetTheory.PGame.toOfListsLeftMoves /-
/-- Converts a number into a left move for `of_lists`. -/
def SetTheory.PGame.toOfListsLeftMoves {L R : List SetTheory.PGame} :
    Fin L.length ≃ (SetTheory.PGame.ofLists L R).LeftMoves :=
  ((Equiv.cast (SetTheory.PGame.leftMoves_ofLists L R).symm).trans Equiv.ulift).symm
#align pgame.to_of_lists_left_moves SetTheory.PGame.toOfListsLeftMoves
-/

#print SetTheory.PGame.toOfListsRightMoves /-
/-- Converts a number into a right move for `of_lists`. -/
def SetTheory.PGame.toOfListsRightMoves {L R : List SetTheory.PGame} :
    Fin R.length ≃ (SetTheory.PGame.ofLists L R).RightMoves :=
  ((Equiv.cast (SetTheory.PGame.rightMoves_ofLists L R).symm).trans Equiv.ulift).symm
#align pgame.to_of_lists_right_moves SetTheory.PGame.toOfListsRightMoves
-/

#print SetTheory.PGame.ofLists_moveLeft /-
theorem SetTheory.PGame.ofLists_moveLeft {L R : List SetTheory.PGame} (i : Fin L.length) :
    (SetTheory.PGame.ofLists L R).moveLeft (SetTheory.PGame.toOfListsLeftMoves i) =
      L.nthLe i i.is_lt :=
  rfl
#align pgame.of_lists_move_left SetTheory.PGame.ofLists_moveLeft
-/

#print SetTheory.PGame.ofLists_moveLeft' /-
@[simp]
theorem SetTheory.PGame.ofLists_moveLeft' {L R : List SetTheory.PGame}
    (i : (SetTheory.PGame.ofLists L R).LeftMoves) :
    (SetTheory.PGame.ofLists L R).moveLeft i =
      L.nthLe (SetTheory.PGame.toOfListsLeftMoves.symm i)
        (SetTheory.PGame.toOfListsLeftMoves.symm i).is_lt :=
  rfl
#align pgame.of_lists_move_left' SetTheory.PGame.ofLists_moveLeft'
-/

#print SetTheory.PGame.ofLists_moveRight /-
theorem SetTheory.PGame.ofLists_moveRight {L R : List SetTheory.PGame} (i : Fin R.length) :
    (SetTheory.PGame.ofLists L R).moveRight (SetTheory.PGame.toOfListsRightMoves i) =
      R.nthLe i i.is_lt :=
  rfl
#align pgame.of_lists_move_right SetTheory.PGame.ofLists_moveRight
-/

#print SetTheory.PGame.ofLists_moveRight' /-
@[simp]
theorem SetTheory.PGame.ofLists_moveRight' {L R : List SetTheory.PGame}
    (i : (SetTheory.PGame.ofLists L R).RightMoves) :
    (SetTheory.PGame.ofLists L R).moveRight i =
      R.nthLe (SetTheory.PGame.toOfListsRightMoves.symm i)
        (SetTheory.PGame.toOfListsRightMoves.symm i).is_lt :=
  rfl
#align pgame.of_lists_move_right' SetTheory.PGame.ofLists_moveRight'
-/

#print SetTheory.PGame.moveRecOn /-
/-- A variant of `pgame.rec_on` expressed in terms of `pgame.move_left` and `pgame.move_right`.

Both this and `pgame.rec_on` describe Conway induction on games. -/
@[elab_as_elim]
def SetTheory.PGame.moveRecOn {C : SetTheory.PGame → Sort _} (x : SetTheory.PGame)
    (IH : ∀ y : SetTheory.PGame, (∀ i, C (y.moveLeft i)) → (∀ j, C (y.moveRight j)) → C y) : C x :=
  x.recOn fun yl yr yL yR => IH (SetTheory.PGame.mk yl yr yL yR)
#align pgame.move_rec_on SetTheory.PGame.moveRecOn
-/

#print SetTheory.PGame.IsOption /-
/-- `is_option x y` means that `x` is either a left or right option for `y`. -/
@[mk_iff]
inductive SetTheory.PGame.IsOption : SetTheory.PGame → SetTheory.PGame → Prop
  | move_left {x : SetTheory.PGame} (i : x.LeftMoves) : is_option (x.moveLeft i) x
  | move_right {x : SetTheory.PGame} (i : x.RightMoves) : is_option (x.moveRight i) x
#align pgame.is_option SetTheory.PGame.IsOption
-/

#print SetTheory.PGame.IsOption.mk_left /-
theorem SetTheory.PGame.IsOption.mk_left {xl xr : Type u} (xL : xl → SetTheory.PGame)
    (xR : xr → SetTheory.PGame) (i : xl) : (xL i).IsOption (SetTheory.PGame.mk xl xr xL xR) :=
  @SetTheory.PGame.IsOption.moveLeft (SetTheory.PGame.mk _ _ _ _) i
#align pgame.is_option.mk_left SetTheory.PGame.IsOption.mk_left
-/

#print SetTheory.PGame.IsOption.mk_right /-
theorem SetTheory.PGame.IsOption.mk_right {xl xr : Type u} (xL : xl → SetTheory.PGame)
    (xR : xr → SetTheory.PGame) (i : xr) : (xR i).IsOption (SetTheory.PGame.mk xl xr xL xR) :=
  @SetTheory.PGame.IsOption.moveRight (SetTheory.PGame.mk _ _ _ _) i
#align pgame.is_option.mk_right SetTheory.PGame.IsOption.mk_right
-/

#print SetTheory.PGame.wf_isOption /-
theorem SetTheory.PGame.wf_isOption : WellFounded SetTheory.PGame.IsOption :=
  ⟨fun x =>
    SetTheory.PGame.moveRecOn x fun x IHl IHr =>
      Acc.intro x fun y h => by
        induction' h with _ i _ j
        · exact IHl i
        · exact IHr j⟩
#align pgame.wf_is_option SetTheory.PGame.wf_isOption
-/

#print SetTheory.PGame.Subsequent /-
/-- `subsequent x y` says that `x` can be obtained by playing some nonempty sequence of moves from
`y`. It is the transitive closure of `is_option`. -/
def SetTheory.PGame.Subsequent : SetTheory.PGame → SetTheory.PGame → Prop :=
  TransGen SetTheory.PGame.IsOption
#align pgame.subsequent SetTheory.PGame.Subsequent
-/

instance : IsTrans _ SetTheory.PGame.Subsequent :=
  TransGen.isTrans

#print SetTheory.PGame.Subsequent.trans /-
@[trans]
theorem SetTheory.PGame.Subsequent.trans {x y z} :
    SetTheory.PGame.Subsequent x y →
      SetTheory.PGame.Subsequent y z → SetTheory.PGame.Subsequent x z :=
  TransGen.trans
#align pgame.subsequent.trans SetTheory.PGame.Subsequent.trans
-/

#print SetTheory.PGame.wf_subsequent /-
theorem SetTheory.PGame.wf_subsequent : WellFounded SetTheory.PGame.Subsequent :=
  SetTheory.PGame.wf_isOption.TransGen
#align pgame.wf_subsequent SetTheory.PGame.wf_subsequent
-/

instance : WellFoundedRelation SetTheory.PGame :=
  ⟨_, SetTheory.PGame.wf_subsequent⟩

#print SetTheory.PGame.Subsequent.moveLeft /-
theorem SetTheory.PGame.Subsequent.moveLeft {x : SetTheory.PGame} (i : x.LeftMoves) :
    SetTheory.PGame.Subsequent (x.moveLeft i) x :=
  TransGen.single (SetTheory.PGame.IsOption.moveLeft i)
#align pgame.subsequent.move_left SetTheory.PGame.Subsequent.moveLeft
-/

#print SetTheory.PGame.Subsequent.moveRight /-
theorem SetTheory.PGame.Subsequent.moveRight {x : SetTheory.PGame} (j : x.RightMoves) :
    SetTheory.PGame.Subsequent (x.moveRight j) x :=
  TransGen.single (SetTheory.PGame.IsOption.moveRight j)
#align pgame.subsequent.move_right SetTheory.PGame.Subsequent.moveRight
-/

#print SetTheory.PGame.Subsequent.mk_left /-
theorem SetTheory.PGame.Subsequent.mk_left {xl xr} (xL : xl → SetTheory.PGame)
    (xR : xr → SetTheory.PGame) (i : xl) :
    SetTheory.PGame.Subsequent (xL i) (SetTheory.PGame.mk xl xr xL xR) :=
  @SetTheory.PGame.Subsequent.moveLeft (SetTheory.PGame.mk _ _ _ _) i
#align pgame.subsequent.mk_left SetTheory.PGame.Subsequent.mk_left
-/

#print SetTheory.PGame.Subsequent.mk_right /-
theorem SetTheory.PGame.Subsequent.mk_right {xl xr} (xL : xl → SetTheory.PGame)
    (xR : xr → SetTheory.PGame) (j : xr) :
    SetTheory.PGame.Subsequent (xR j) (SetTheory.PGame.mk xl xr xL xR) :=
  @SetTheory.PGame.Subsequent.moveRight (SetTheory.PGame.mk _ _ _ _) j
#align pgame.subsequent.mk_right SetTheory.PGame.Subsequent.mk_right
-/

/- ././././Mathport/Syntax/Translate/Expr.lean:338:4: warning: unsupported (TODO): `[tacs] -/
/-- A local tactic for proving well-foundedness of recursive definitions involving pregames. -/
unsafe def pgame_wf_tac :=
  sorry
#align pgame.pgame_wf_tac pgame.pgame_wf_tac

/-! ### Basic pre-games -/


/-- The pre-game `zero` is defined by `0 = { | }`. -/
instance : Zero SetTheory.PGame :=
  ⟨⟨PEmpty, PEmpty, PEmpty.elim, PEmpty.elim⟩⟩

#print SetTheory.PGame.zero_leftMoves /-
@[simp]
theorem SetTheory.PGame.zero_leftMoves : SetTheory.PGame.LeftMoves 0 = PEmpty :=
  rfl
#align pgame.zero_left_moves SetTheory.PGame.zero_leftMoves
-/

#print SetTheory.PGame.zero_rightMoves /-
@[simp]
theorem SetTheory.PGame.zero_rightMoves : SetTheory.PGame.RightMoves 0 = PEmpty :=
  rfl
#align pgame.zero_right_moves SetTheory.PGame.zero_rightMoves
-/

#print SetTheory.PGame.isEmpty_zero_leftMoves /-
instance SetTheory.PGame.isEmpty_zero_leftMoves : IsEmpty (SetTheory.PGame.LeftMoves 0) :=
  PEmpty.isEmpty
#align pgame.is_empty_zero_left_moves SetTheory.PGame.isEmpty_zero_leftMoves
-/

#print SetTheory.PGame.isEmpty_zero_rightMoves /-
instance SetTheory.PGame.isEmpty_zero_rightMoves : IsEmpty (SetTheory.PGame.RightMoves 0) :=
  PEmpty.isEmpty
#align pgame.is_empty_zero_right_moves SetTheory.PGame.isEmpty_zero_rightMoves
-/

instance : Inhabited SetTheory.PGame :=
  ⟨0⟩

/-- The pre-game `one` is defined by `1 = { 0 | }`. -/
instance : One SetTheory.PGame :=
  ⟨⟨PUnit, PEmpty, fun _ => 0, PEmpty.elim⟩⟩

#print SetTheory.PGame.one_leftMoves /-
@[simp]
theorem SetTheory.PGame.one_leftMoves : SetTheory.PGame.LeftMoves 1 = PUnit :=
  rfl
#align pgame.one_left_moves SetTheory.PGame.one_leftMoves
-/

#print SetTheory.PGame.one_moveLeft /-
@[simp]
theorem SetTheory.PGame.one_moveLeft (x) : SetTheory.PGame.moveLeft 1 x = 0 :=
  rfl
#align pgame.one_move_left SetTheory.PGame.one_moveLeft
-/

#print SetTheory.PGame.one_rightMoves /-
@[simp]
theorem SetTheory.PGame.one_rightMoves : SetTheory.PGame.RightMoves 1 = PEmpty :=
  rfl
#align pgame.one_right_moves SetTheory.PGame.one_rightMoves
-/

#print SetTheory.PGame.uniqueOneLeftMoves /-
instance SetTheory.PGame.uniqueOneLeftMoves : Unique (SetTheory.PGame.LeftMoves 1) :=
  PUnit.unique
#align pgame.unique_one_left_moves SetTheory.PGame.uniqueOneLeftMoves
-/

#print SetTheory.PGame.isEmpty_one_rightMoves /-
instance SetTheory.PGame.isEmpty_one_rightMoves : IsEmpty (SetTheory.PGame.RightMoves 1) :=
  PEmpty.isEmpty
#align pgame.is_empty_one_right_moves SetTheory.PGame.isEmpty_one_rightMoves
-/

/-! ### Pre-game order relations -/


/-- The less or equal relation on pre-games.

If `0 ≤ x`, then Left can win `x` as the second player. -/
instance : LE SetTheory.PGame :=
  ⟨Sym2.GameAdd.fix SetTheory.PGame.wf_isOption fun x y le =>
      (∀ i, ¬le y (x.moveLeft i) (Sym2.GameAdd.snd_fst <| SetTheory.PGame.IsOption.moveLeft i)) ∧
        ∀ j, ¬le (y.moveRight j) x (Sym2.GameAdd.fst_snd <| SetTheory.PGame.IsOption.moveRight j)⟩

#print SetTheory.PGame.LF /-
/-- The less or fuzzy relation on pre-games.

If `0 ⧏ x`, then Left can win `x` as the first player. -/
def SetTheory.PGame.LF (x y : SetTheory.PGame) : Prop :=
  ¬y ≤ x
#align pgame.lf SetTheory.PGame.LF
-/

scoped infixl:50 " ⧏ " => SetTheory.PGame.LF

#print SetTheory.PGame.not_le /-
@[simp]
protected theorem SetTheory.PGame.not_le {x y : SetTheory.PGame} : ¬x ≤ y ↔ y ⧏ x :=
  Iff.rfl
#align pgame.not_le SetTheory.PGame.not_le
-/

#print SetTheory.PGame.not_lf /-
@[simp]
theorem SetTheory.PGame.not_lf {x y : SetTheory.PGame} : ¬x ⧏ y ↔ y ≤ x :=
  Classical.not_not
#align pgame.not_lf SetTheory.PGame.not_lf
-/

#print LE.le.not_gf /-
theorem LE.le.not_gf {x y : SetTheory.PGame} : x ≤ y → ¬y ⧏ x :=
  SetTheory.PGame.not_lf.2
#align has_le.le.not_gf LE.le.not_gf
-/

#print SetTheory.PGame.LF.not_ge /-
theorem SetTheory.PGame.LF.not_ge {x y : SetTheory.PGame} : x ⧏ y → ¬y ≤ x :=
  id
#align pgame.lf.not_ge SetTheory.PGame.LF.not_ge
-/

#print SetTheory.PGame.le_iff_forall_lf /-
/-- Definition of `x ≤ y` on pre-games, in terms of `⧏`.

The ordering here is chosen so that `and.left` refer to moves by Left, and `and.right` refer to
moves by Right. -/
theorem SetTheory.PGame.le_iff_forall_lf {x y : SetTheory.PGame} :
    x ≤ y ↔ (∀ i, x.moveLeft i ⧏ y) ∧ ∀ j, x ⧏ y.moveRight j := by unfold LE.le;
  rw [Sym2.GameAdd.fix_eq]; rfl
#align pgame.le_iff_forall_lf SetTheory.PGame.le_iff_forall_lf
-/

#print SetTheory.PGame.mk_le_mk /-
/-- Definition of `x ≤ y` on pre-games built using the constructor. -/
@[simp]
theorem SetTheory.PGame.mk_le_mk {xl xr xL xR yl yr yL yR} :
    SetTheory.PGame.mk xl xr xL xR ≤ SetTheory.PGame.mk yl yr yL yR ↔
      (∀ i, xL i ⧏ SetTheory.PGame.mk yl yr yL yR) ∧ ∀ j, SetTheory.PGame.mk xl xr xL xR ⧏ yR j :=
  SetTheory.PGame.le_iff_forall_lf
#align pgame.mk_le_mk SetTheory.PGame.mk_le_mk
-/

#print SetTheory.PGame.le_of_forall_lf /-
theorem SetTheory.PGame.le_of_forall_lf {x y : SetTheory.PGame} (h₁ : ∀ i, x.moveLeft i ⧏ y)
    (h₂ : ∀ j, x ⧏ y.moveRight j) : x ≤ y :=
  SetTheory.PGame.le_iff_forall_lf.2 ⟨h₁, h₂⟩
#align pgame.le_of_forall_lf SetTheory.PGame.le_of_forall_lf
-/

#print SetTheory.PGame.lf_iff_exists_le /-
/-- Definition of `x ⧏ y` on pre-games, in terms of `≤`.

The ordering here is chosen so that `or.inl` refer to moves by Left, and `or.inr` refer to
moves by Right. -/
theorem SetTheory.PGame.lf_iff_exists_le {x y : SetTheory.PGame} :
    x ⧏ y ↔ (∃ i, x ≤ y.moveLeft i) ∨ ∃ j, x.moveRight j ≤ y := by
  rw [lf, le_iff_forall_lf, not_and_or]; simp
#align pgame.lf_iff_exists_le SetTheory.PGame.lf_iff_exists_le
-/

#print SetTheory.PGame.mk_lf_mk /-
/-- Definition of `x ⧏ y` on pre-games built using the constructor. -/
@[simp]
theorem SetTheory.PGame.mk_lf_mk {xl xr xL xR yl yr yL yR} :
    SetTheory.PGame.mk xl xr xL xR ⧏ SetTheory.PGame.mk yl yr yL yR ↔
      (∃ i, SetTheory.PGame.mk xl xr xL xR ≤ yL i) ∨ ∃ j, xR j ≤ SetTheory.PGame.mk yl yr yL yR :=
  SetTheory.PGame.lf_iff_exists_le
#align pgame.mk_lf_mk SetTheory.PGame.mk_lf_mk
-/

#print SetTheory.PGame.le_or_gf /-
theorem SetTheory.PGame.le_or_gf (x y : SetTheory.PGame) : x ≤ y ∨ y ⧏ x := by
  rw [← SetTheory.PGame.not_le]; apply em
#align pgame.le_or_gf SetTheory.PGame.le_or_gf
-/

#print SetTheory.PGame.moveLeft_lf_of_le /-
theorem SetTheory.PGame.moveLeft_lf_of_le {x y : SetTheory.PGame} (h : x ≤ y) (i) :
    x.moveLeft i ⧏ y :=
  (SetTheory.PGame.le_iff_forall_lf.1 h).1 i
#align pgame.move_left_lf_of_le SetTheory.PGame.moveLeft_lf_of_le
-/

alias _root_.has_le.le.move_left_lf := move_left_lf_of_le
#align has_le.le.move_left_lf LE.le.moveLeft_lf

#print SetTheory.PGame.lf_moveRight_of_le /-
theorem SetTheory.PGame.lf_moveRight_of_le {x y : SetTheory.PGame} (h : x ≤ y) (j) :
    x ⧏ y.moveRight j :=
  (SetTheory.PGame.le_iff_forall_lf.1 h).2 j
#align pgame.lf_move_right_of_le SetTheory.PGame.lf_moveRight_of_le
-/

alias _root_.has_le.le.lf_move_right := lf_move_right_of_le
#align has_le.le.lf_move_right LE.le.lf_moveRight

#print SetTheory.PGame.lf_of_moveRight_le /-
theorem SetTheory.PGame.lf_of_moveRight_le {x y : SetTheory.PGame} {j} (h : x.moveRight j ≤ y) :
    x ⧏ y :=
  SetTheory.PGame.lf_iff_exists_le.2 <| Or.inr ⟨j, h⟩
#align pgame.lf_of_move_right_le SetTheory.PGame.lf_of_moveRight_le
-/

#print SetTheory.PGame.lf_of_le_moveLeft /-
theorem SetTheory.PGame.lf_of_le_moveLeft {x y : SetTheory.PGame} {i} (h : x ≤ y.moveLeft i) :
    x ⧏ y :=
  SetTheory.PGame.lf_iff_exists_le.2 <| Or.inl ⟨i, h⟩
#align pgame.lf_of_le_move_left SetTheory.PGame.lf_of_le_moveLeft
-/

#print SetTheory.PGame.lf_of_le_mk /-
theorem SetTheory.PGame.lf_of_le_mk {xl xr xL xR y} :
    SetTheory.PGame.mk xl xr xL xR ≤ y → ∀ i, xL i ⧏ y :=
  SetTheory.PGame.moveLeft_lf_of_le
#align pgame.lf_of_le_mk SetTheory.PGame.lf_of_le_mk
-/

#print SetTheory.PGame.lf_of_mk_le /-
theorem SetTheory.PGame.lf_of_mk_le {x yl yr yL yR} :
    x ≤ SetTheory.PGame.mk yl yr yL yR → ∀ j, x ⧏ yR j :=
  SetTheory.PGame.lf_moveRight_of_le
#align pgame.lf_of_mk_le SetTheory.PGame.lf_of_mk_le
-/

#print SetTheory.PGame.mk_lf_of_le /-
theorem SetTheory.PGame.mk_lf_of_le {xl xr y j} (xL) {xR : xr → SetTheory.PGame} :
    xR j ≤ y → SetTheory.PGame.mk xl xr xL xR ⧏ y :=
  @SetTheory.PGame.lf_of_moveRight_le (SetTheory.PGame.mk _ _ _ _) y j
#align pgame.mk_lf_of_le SetTheory.PGame.mk_lf_of_le
-/

#print SetTheory.PGame.lf_mk_of_le /-
theorem SetTheory.PGame.lf_mk_of_le {x yl yr} {yL : yl → SetTheory.PGame} (yR) {i} :
    x ≤ yL i → x ⧏ SetTheory.PGame.mk yl yr yL yR :=
  @SetTheory.PGame.lf_of_le_moveLeft x (SetTheory.PGame.mk _ _ _ _) i
#align pgame.lf_mk_of_le SetTheory.PGame.lf_mk_of_le
-/

/- We prove that `x ≤ y → y ≤ z ← x ≤ z` inductively, by also simultaneously proving its cyclic
reorderings. This auxiliary lemma is used during said induction. -/
private theorem le_trans_aux {x y z : SetTheory.PGame}
    (h₁ : ∀ {i}, y ≤ z → z ≤ x.moveLeft i → y ≤ x.moveLeft i)
    (h₂ : ∀ {j}, z.moveRight j ≤ x → x ≤ y → z.moveRight j ≤ y) (hxy : x ≤ y) (hyz : y ≤ z) :
    x ≤ z :=
  SetTheory.PGame.le_of_forall_lf
    (fun i => SetTheory.PGame.not_le.1 fun h => (h₁ hyz h).not_gf <| hxy.moveLeft_lf i) fun j =>
    SetTheory.PGame.not_le.1 fun h => (h₂ h hxy).not_gf <| hyz.lf_moveRight j

instance : Preorder SetTheory.PGame :=
  {
    SetTheory.PGame.hasLe with
    le_refl := fun x => by
      induction' x with _ _ _ _ IHl IHr
      exact
        le_of_forall_lf (fun i => lf_of_le_move_left (IHl i)) fun i => lf_of_move_right_le (IHr i)
    le_trans :=
      by
      suffices :
        ∀ {x y z : SetTheory.PGame},
          (x ≤ y → y ≤ z → x ≤ z) ∧ (y ≤ z → z ≤ x → y ≤ x) ∧ (z ≤ x → x ≤ y → z ≤ y)
      exact fun x y z => this.1
      intro x y z
      induction' x with xl xr xL xR IHxl IHxr generalizing y z
      induction' y with yl yr yL yR IHyl IHyr generalizing z
      induction' z with zl zr zL zR IHzl IHzr
      exact
        ⟨le_trans_aux (fun i => (IHxl i).2.1) fun j => (IHzr j).2.2,
          le_trans_aux (fun i => (IHyl i).2.2) fun j => (IHxr j).1,
          le_trans_aux (fun i => (IHzl i).1) fun j => (IHyr j).2.1⟩
    lt := fun x y => x ≤ y ∧ x ⧏ y }

#print SetTheory.PGame.lt_iff_le_and_lf /-
theorem SetTheory.PGame.lt_iff_le_and_lf {x y : SetTheory.PGame} : x < y ↔ x ≤ y ∧ x ⧏ y :=
  Iff.rfl
#align pgame.lt_iff_le_and_lf SetTheory.PGame.lt_iff_le_and_lf
-/

#print SetTheory.PGame.lt_of_le_of_lf /-
theorem SetTheory.PGame.lt_of_le_of_lf {x y : SetTheory.PGame} (h₁ : x ≤ y) (h₂ : x ⧏ y) : x < y :=
  ⟨h₁, h₂⟩
#align pgame.lt_of_le_of_lf SetTheory.PGame.lt_of_le_of_lf
-/

#print SetTheory.PGame.lf_of_lt /-
theorem SetTheory.PGame.lf_of_lt {x y : SetTheory.PGame} (h : x < y) : x ⧏ y :=
  h.2
#align pgame.lf_of_lt SetTheory.PGame.lf_of_lt
-/

alias _root_.has_lt.lt.lf := lf_of_lt
#align has_lt.lt.lf LT.lt.lf

#print SetTheory.PGame.lf_irrefl /-
theorem SetTheory.PGame.lf_irrefl (x : SetTheory.PGame) : ¬x ⧏ x :=
  le_rfl.not_gf
#align pgame.lf_irrefl SetTheory.PGame.lf_irrefl
-/

instance : IsIrrefl _ (· ⧏ ·) :=
  ⟨SetTheory.PGame.lf_irrefl⟩

#print SetTheory.PGame.lf_of_le_of_lf /-
@[trans]
theorem SetTheory.PGame.lf_of_le_of_lf {x y z : SetTheory.PGame} (h₁ : x ≤ y) (h₂ : y ⧏ z) :
    x ⧏ z := by rw [← SetTheory.PGame.not_le] at h₂ ⊢; exact fun h₃ => h₂ (h₃.trans h₁)
#align pgame.lf_of_le_of_lf SetTheory.PGame.lf_of_le_of_lf
-/

#print SetTheory.PGame.lf_of_lf_of_le /-
@[trans]
theorem SetTheory.PGame.lf_of_lf_of_le {x y z : SetTheory.PGame} (h₁ : x ⧏ y) (h₂ : y ≤ z) :
    x ⧏ z := by rw [← SetTheory.PGame.not_le] at h₁ ⊢; exact fun h₃ => h₁ (h₂.trans h₃)
#align pgame.lf_of_lf_of_le SetTheory.PGame.lf_of_lf_of_le
-/

alias _root_.has_le.le.trans_lf := lf_of_le_of_lf
#align has_le.le.trans_lf LE.le.trans_lf

alias lf.trans_le := lf_of_lf_of_le
#align pgame.lf.trans_le SetTheory.PGame.LF.trans_le

#print SetTheory.PGame.lf_of_lt_of_lf /-
@[trans]
theorem SetTheory.PGame.lf_of_lt_of_lf {x y z : SetTheory.PGame} (h₁ : x < y) (h₂ : y ⧏ z) :
    x ⧏ z :=
  h₁.le.trans_lf h₂
#align pgame.lf_of_lt_of_lf SetTheory.PGame.lf_of_lt_of_lf
-/

#print SetTheory.PGame.lf_of_lf_of_lt /-
@[trans]
theorem SetTheory.PGame.lf_of_lf_of_lt {x y z : SetTheory.PGame} (h₁ : x ⧏ y) (h₂ : y < z) :
    x ⧏ z :=
  h₁.trans_le h₂.le
#align pgame.lf_of_lf_of_lt SetTheory.PGame.lf_of_lf_of_lt
-/

alias _root_.has_lt.lt.trans_lf := lf_of_lt_of_lf
#align has_lt.lt.trans_lf LT.lt.trans_lf

alias lf.trans_lt := lf_of_lf_of_lt
#align pgame.lf.trans_lt SetTheory.PGame.LF.trans_lt

#print SetTheory.PGame.moveLeft_lf /-
theorem SetTheory.PGame.moveLeft_lf {x : SetTheory.PGame} : ∀ i, x.moveLeft i ⧏ x :=
  le_rfl.moveLeft_lf
#align pgame.move_left_lf SetTheory.PGame.moveLeft_lf
-/

#print SetTheory.PGame.lf_moveRight /-
theorem SetTheory.PGame.lf_moveRight {x : SetTheory.PGame} : ∀ j, x ⧏ x.moveRight j :=
  le_rfl.lf_moveRight
#align pgame.lf_move_right SetTheory.PGame.lf_moveRight
-/

#print SetTheory.PGame.lf_mk /-
theorem SetTheory.PGame.lf_mk {xl xr} (xL : xl → SetTheory.PGame) (xR : xr → SetTheory.PGame) (i) :
    xL i ⧏ SetTheory.PGame.mk xl xr xL xR :=
  @SetTheory.PGame.moveLeft_lf (SetTheory.PGame.mk _ _ _ _) i
#align pgame.lf_mk SetTheory.PGame.lf_mk
-/

#print SetTheory.PGame.mk_lf /-
theorem SetTheory.PGame.mk_lf {xl xr} (xL : xl → SetTheory.PGame) (xR : xr → SetTheory.PGame) (j) :
    SetTheory.PGame.mk xl xr xL xR ⧏ xR j :=
  @SetTheory.PGame.lf_moveRight (SetTheory.PGame.mk _ _ _ _) j
#align pgame.mk_lf SetTheory.PGame.mk_lf
-/

#print SetTheory.PGame.le_of_forall_lt /-
/-- This special case of `pgame.le_of_forall_lf` is useful when dealing with surreals, where `<` is
preferred over `⧏`. -/
theorem SetTheory.PGame.le_of_forall_lt {x y : SetTheory.PGame} (h₁ : ∀ i, x.moveLeft i < y)
    (h₂ : ∀ j, x < y.moveRight j) : x ≤ y :=
  SetTheory.PGame.le_of_forall_lf (fun i => (h₁ i).LF) fun i => (h₂ i).LF
#align pgame.le_of_forall_lt SetTheory.PGame.le_of_forall_lt
-/

#print SetTheory.PGame.le_def /-
/-- The definition of `x ≤ y` on pre-games, in terms of `≤` two moves later. -/
theorem SetTheory.PGame.le_def {x y : SetTheory.PGame} :
    x ≤ y ↔
      (∀ i, (∃ i', x.moveLeft i ≤ y.moveLeft i') ∨ ∃ j, (x.moveLeft i).moveRight j ≤ y) ∧
        ∀ j, (∃ i, x ≤ (y.moveRight j).moveLeft i) ∨ ∃ j', x.moveRight j' ≤ y.moveRight j :=
  by rw [le_iff_forall_lf];
  conv =>
    lhs
    simp only [lf_iff_exists_le]
#align pgame.le_def SetTheory.PGame.le_def
-/

#print SetTheory.PGame.lf_def /-
/-- The definition of `x ⧏ y` on pre-games, in terms of `⧏` two moves later. -/
theorem SetTheory.PGame.lf_def {x y : SetTheory.PGame} :
    x ⧏ y ↔
      (∃ i, (∀ i', x.moveLeft i' ⧏ y.moveLeft i) ∧ ∀ j, x ⧏ (y.moveLeft i).moveRight j) ∨
        ∃ j, (∀ i, (x.moveRight j).moveLeft i ⧏ y) ∧ ∀ j', x.moveRight j ⧏ y.moveRight j' :=
  by rw [lf_iff_exists_le];
  conv =>
    lhs
    simp only [le_iff_forall_lf]
#align pgame.lf_def SetTheory.PGame.lf_def
-/

#print SetTheory.PGame.zero_le_lf /-
/-- The definition of `0 ≤ x` on pre-games, in terms of `0 ⧏`. -/
theorem SetTheory.PGame.zero_le_lf {x : SetTheory.PGame} : 0 ≤ x ↔ ∀ j, 0 ⧏ x.moveRight j := by
  rw [le_iff_forall_lf]; simp
#align pgame.zero_le_lf SetTheory.PGame.zero_le_lf
-/

#print SetTheory.PGame.le_zero_lf /-
/-- The definition of `x ≤ 0` on pre-games, in terms of `⧏ 0`. -/
theorem SetTheory.PGame.le_zero_lf {x : SetTheory.PGame} : x ≤ 0 ↔ ∀ i, x.moveLeft i ⧏ 0 := by
  rw [le_iff_forall_lf]; simp
#align pgame.le_zero_lf SetTheory.PGame.le_zero_lf
-/

#print SetTheory.PGame.zero_lf_le /-
/-- The definition of `0 ⧏ x` on pre-games, in terms of `0 ≤`. -/
theorem SetTheory.PGame.zero_lf_le {x : SetTheory.PGame} : 0 ⧏ x ↔ ∃ i, 0 ≤ x.moveLeft i := by
  rw [lf_iff_exists_le]; simp
#align pgame.zero_lf_le SetTheory.PGame.zero_lf_le
-/

#print SetTheory.PGame.lf_zero_le /-
/-- The definition of `x ⧏ 0` on pre-games, in terms of `≤ 0`. -/
theorem SetTheory.PGame.lf_zero_le {x : SetTheory.PGame} : x ⧏ 0 ↔ ∃ j, x.moveRight j ≤ 0 := by
  rw [lf_iff_exists_le]; simp
#align pgame.lf_zero_le SetTheory.PGame.lf_zero_le
-/

#print SetTheory.PGame.zero_le /-
/-- The definition of `0 ≤ x` on pre-games, in terms of `0 ≤` two moves later. -/
theorem SetTheory.PGame.zero_le {x : SetTheory.PGame} :
    0 ≤ x ↔ ∀ j, ∃ i, 0 ≤ (x.moveRight j).moveLeft i := by rw [le_def]; simp
#align pgame.zero_le SetTheory.PGame.zero_le
-/

#print SetTheory.PGame.le_zero /-
/-- The definition of `x ≤ 0` on pre-games, in terms of `≤ 0` two moves later. -/
theorem SetTheory.PGame.le_zero {x : SetTheory.PGame} :
    x ≤ 0 ↔ ∀ i, ∃ j, (x.moveLeft i).moveRight j ≤ 0 := by rw [le_def]; simp
#align pgame.le_zero SetTheory.PGame.le_zero
-/

#print SetTheory.PGame.zero_lf /-
/-- The definition of `0 ⧏ x` on pre-games, in terms of `0 ⧏` two moves later. -/
theorem SetTheory.PGame.zero_lf {x : SetTheory.PGame} :
    0 ⧏ x ↔ ∃ i, ∀ j, 0 ⧏ (x.moveLeft i).moveRight j := by rw [lf_def]; simp
#align pgame.zero_lf SetTheory.PGame.zero_lf
-/

#print SetTheory.PGame.lf_zero /-
/-- The definition of `x ⧏ 0` on pre-games, in terms of `⧏ 0` two moves later. -/
theorem SetTheory.PGame.lf_zero {x : SetTheory.PGame} :
    x ⧏ 0 ↔ ∃ j, ∀ i, (x.moveRight j).moveLeft i ⧏ 0 := by rw [lf_def]; simp
#align pgame.lf_zero SetTheory.PGame.lf_zero
-/

#print SetTheory.PGame.zero_le_of_isEmpty_rightMoves /-
@[simp]
theorem SetTheory.PGame.zero_le_of_isEmpty_rightMoves (x : SetTheory.PGame) [IsEmpty x.RightMoves] :
    0 ≤ x :=
  SetTheory.PGame.zero_le.2 isEmptyElim
#align pgame.zero_le_of_is_empty_right_moves SetTheory.PGame.zero_le_of_isEmpty_rightMoves
-/

#print SetTheory.PGame.le_zero_of_isEmpty_leftMoves /-
@[simp]
theorem SetTheory.PGame.le_zero_of_isEmpty_leftMoves (x : SetTheory.PGame) [IsEmpty x.LeftMoves] :
    x ≤ 0 :=
  SetTheory.PGame.le_zero.2 isEmptyElim
#align pgame.le_zero_of_is_empty_left_moves SetTheory.PGame.le_zero_of_isEmpty_leftMoves
-/

#print SetTheory.PGame.rightResponse /-
/-- Given a game won by the right player when they play second, provide a response to any move by
left. -/
noncomputable def SetTheory.PGame.rightResponse {x : SetTheory.PGame} (h : x ≤ 0)
    (i : x.LeftMoves) : (x.moveLeft i).RightMoves :=
  Classical.choose <| (SetTheory.PGame.le_zero.1 h) i
#align pgame.right_response SetTheory.PGame.rightResponse
-/

#print SetTheory.PGame.rightResponse_spec /-
/-- Show that the response for right provided by `right_response` preserves the right-player-wins
condition. -/
theorem SetTheory.PGame.rightResponse_spec {x : SetTheory.PGame} (h : x ≤ 0) (i : x.LeftMoves) :
    (x.moveLeft i).moveRight (SetTheory.PGame.rightResponse h i) ≤ 0 :=
  Classical.choose_spec <| (SetTheory.PGame.le_zero.1 h) i
#align pgame.right_response_spec SetTheory.PGame.rightResponse_spec
-/

#print SetTheory.PGame.leftResponse /-
/-- Given a game won by the left player when they play second, provide a response to any move by
right. -/
noncomputable def SetTheory.PGame.leftResponse {x : SetTheory.PGame} (h : 0 ≤ x)
    (j : x.RightMoves) : (x.moveRight j).LeftMoves :=
  Classical.choose <| (SetTheory.PGame.zero_le.1 h) j
#align pgame.left_response SetTheory.PGame.leftResponse
-/

#print SetTheory.PGame.leftResponse_spec /-
/-- Show that the response for left provided by `left_response` preserves the left-player-wins
condition. -/
theorem SetTheory.PGame.leftResponse_spec {x : SetTheory.PGame} (h : 0 ≤ x) (j : x.RightMoves) :
    0 ≤ (x.moveRight j).moveLeft (SetTheory.PGame.leftResponse h j) :=
  Classical.choose_spec <| (SetTheory.PGame.zero_le.1 h) j
#align pgame.left_response_spec SetTheory.PGame.leftResponse_spec
-/

/-- An explicit upper bound for a family of pre-games, whose left moves are the union of the left
moves of all the pre-games in the family. -/
def SetTheory.PGame.upperBound {ι : Type u} (f : ι → SetTheory.PGame.{u}) : SetTheory.PGame :=
  ⟨Σ i, (f i).LeftMoves, PEmpty, fun x => SetTheory.PGame.moveLeft _ x.2, PEmpty.elim⟩
#align pgame.upper_bound SetTheory.PGame.upperBound

instance SetTheory.PGame.upperBound_rightMoves_empty {ι : Type u} (f : ι → SetTheory.PGame.{u}) :
    IsEmpty (SetTheory.PGame.upperBound f).RightMoves :=
  PEmpty.isEmpty
#align pgame.upper_bound_right_moves_empty SetTheory.PGame.upperBound_rightMoves_empty

theorem SetTheory.PGame.le_upperBound {ι : Type u} (f : ι → SetTheory.PGame.{u}) (i : ι) :
    f i ≤ SetTheory.PGame.upperBound f :=
  by
  rw [upper_bound, le_iff_forall_lf]
  dsimp
  simp only [and_true_iff, IsEmpty.forall_iff]
  exact fun j => @move_left_lf (upper_bound f) ⟨i, j⟩
#align pgame.le_upper_bound SetTheory.PGame.le_upperBound

theorem SetTheory.PGame.upperBound_mem_upperBounds (s : Set SetTheory.PGame.{u}) [Small.{u} s] :
    SetTheory.PGame.upperBound (Subtype.val ∘ (equivShrink s).symm) ∈ upperBounds s := fun i hi =>
  by simpa using le_upper_bound (Subtype.val ∘ (equivShrink s).symm) (equivShrink s ⟨i, hi⟩)
#align pgame.upper_bound_mem_upper_bounds SetTheory.PGame.upperBound_mem_upperBounds

#print SetTheory.PGame.bddAbove_of_small /-
/-- A small set `s` of pre-games is bounded above. -/
theorem SetTheory.PGame.bddAbove_of_small (s : Set SetTheory.PGame.{u}) [Small.{u} s] :
    BddAbove s :=
  ⟨_, SetTheory.PGame.upperBound_mem_upperBounds s⟩
#align pgame.bdd_above_of_small SetTheory.PGame.bddAbove_of_small
-/

/-- An explicit lower bound for a family of pre-games, whose right moves are the union of the right
moves of all the pre-games in the family. -/
def SetTheory.PGame.lowerBound {ι : Type u} (f : ι → SetTheory.PGame.{u}) : SetTheory.PGame :=
  ⟨PEmpty, Σ i, (f i).RightMoves, PEmpty.elim, fun x => SetTheory.PGame.moveRight _ x.2⟩
#align pgame.lower_bound SetTheory.PGame.lowerBound

instance SetTheory.PGame.lowerBound_leftMoves_empty {ι : Type u} (f : ι → SetTheory.PGame.{u}) :
    IsEmpty (SetTheory.PGame.lowerBound f).LeftMoves :=
  PEmpty.isEmpty
#align pgame.lower_bound_left_moves_empty SetTheory.PGame.lowerBound_leftMoves_empty

theorem SetTheory.PGame.lowerBound_le {ι : Type u} (f : ι → SetTheory.PGame.{u}) (i : ι) :
    SetTheory.PGame.lowerBound f ≤ f i :=
  by
  rw [lower_bound, le_iff_forall_lf]
  dsimp
  simp only [IsEmpty.forall_iff, true_and_iff]
  exact fun j => @lf_move_right (lower_bound f) ⟨i, j⟩
#align pgame.lower_bound_le SetTheory.PGame.lowerBound_le

theorem SetTheory.PGame.lowerBound_mem_lowerBounds (s : Set SetTheory.PGame.{u}) [Small.{u} s] :
    SetTheory.PGame.lowerBound (Subtype.val ∘ (equivShrink s).symm) ∈ lowerBounds s := fun i hi =>
  by simpa using lower_bound_le (Subtype.val ∘ (equivShrink s).symm) (equivShrink s ⟨i, hi⟩)
#align pgame.lower_bound_mem_lower_bounds SetTheory.PGame.lowerBound_mem_lowerBounds

#print SetTheory.PGame.bddBelow_of_small /-
/-- A small set `s` of pre-games is bounded below. -/
theorem SetTheory.PGame.bddBelow_of_small (s : Set SetTheory.PGame.{u}) [Small.{u} s] :
    BddBelow s :=
  ⟨_, SetTheory.PGame.lowerBound_mem_lowerBounds s⟩
#align pgame.bdd_below_of_small SetTheory.PGame.bddBelow_of_small
-/

#print SetTheory.PGame.Equiv /-
/-- The equivalence relation on pre-games. Two pre-games `x`, `y` are equivalent if `x ≤ y` and
`y ≤ x`.

If `x ≈ 0`, then the second player can always win `x`. -/
def SetTheory.PGame.Equiv (x y : SetTheory.PGame) : Prop :=
  x ≤ y ∧ y ≤ x
#align pgame.equiv SetTheory.PGame.Equiv
-/

scoped infixl:0 " ≈ " => SetTheory.PGame.Equiv

instance : IsEquiv _ (· ≈ ·) where
  refl x := ⟨le_rfl, le_rfl⟩
  trans := fun x y z ⟨xy, yx⟩ ⟨yz, zy⟩ => ⟨xy.trans yz, zy.trans yx⟩
  symm x y := And.symm

#print SetTheory.PGame.Equiv.le /-
theorem SetTheory.PGame.Equiv.le {x y : SetTheory.PGame} (h : x ≈ y) : x ≤ y :=
  h.1
#align pgame.equiv.le SetTheory.PGame.Equiv.le
-/

#print SetTheory.PGame.Equiv.ge /-
theorem SetTheory.PGame.Equiv.ge {x y : SetTheory.PGame} (h : x ≈ y) : y ≤ x :=
  h.2
#align pgame.equiv.ge SetTheory.PGame.Equiv.ge
-/

#print SetTheory.PGame.equiv_rfl /-
@[refl, simp]
theorem SetTheory.PGame.equiv_rfl {x} : x ≈ x :=
  refl x
#align pgame.equiv_rfl SetTheory.PGame.equiv_rfl
-/

#print SetTheory.PGame.equiv_refl /-
theorem SetTheory.PGame.equiv_refl (x) : x ≈ x :=
  refl x
#align pgame.equiv_refl SetTheory.PGame.equiv_refl
-/

#print SetTheory.PGame.Equiv.symm /-
@[symm]
protected theorem SetTheory.PGame.Equiv.symm {x y} : (x ≈ y) → (y ≈ x) :=
  symm
#align pgame.equiv.symm SetTheory.PGame.Equiv.symm
-/

#print SetTheory.PGame.Equiv.trans /-
@[trans]
protected theorem SetTheory.PGame.Equiv.trans {x y z} : (x ≈ y) → (y ≈ z) → (x ≈ z) :=
  trans
#align pgame.equiv.trans SetTheory.PGame.Equiv.trans
-/

#print SetTheory.PGame.equiv_comm /-
protected theorem SetTheory.PGame.equiv_comm {x y} : (x ≈ y) ↔ (y ≈ x) :=
  comm
#align pgame.equiv_comm SetTheory.PGame.equiv_comm
-/

#print SetTheory.PGame.equiv_of_eq /-
theorem SetTheory.PGame.equiv_of_eq {x y} (h : x = y) : x ≈ y := by subst h
#align pgame.equiv_of_eq SetTheory.PGame.equiv_of_eq
-/

#print SetTheory.PGame.le_of_le_of_equiv /-
@[trans]
theorem SetTheory.PGame.le_of_le_of_equiv {x y z} (h₁ : x ≤ y) (h₂ : y ≈ z) : x ≤ z :=
  h₁.trans h₂.1
#align pgame.le_of_le_of_equiv SetTheory.PGame.le_of_le_of_equiv
-/

#print SetTheory.PGame.le_of_equiv_of_le /-
@[trans]
theorem SetTheory.PGame.le_of_equiv_of_le {x y z} (h₁ : x ≈ y) : y ≤ z → x ≤ z :=
  h₁.1.trans
#align pgame.le_of_equiv_of_le SetTheory.PGame.le_of_equiv_of_le
-/

#print SetTheory.PGame.LF.not_equiv /-
theorem SetTheory.PGame.LF.not_equiv {x y} (h : x ⧏ y) : ¬(x ≈ y) := fun h' => h.not_ge h'.2
#align pgame.lf.not_equiv SetTheory.PGame.LF.not_equiv
-/

#print SetTheory.PGame.LF.not_equiv' /-
theorem SetTheory.PGame.LF.not_equiv' {x y} (h : x ⧏ y) : ¬(y ≈ x) := fun h' => h.not_ge h'.1
#align pgame.lf.not_equiv' SetTheory.PGame.LF.not_equiv'
-/

#print SetTheory.PGame.LF.not_gt /-
theorem SetTheory.PGame.LF.not_gt {x y} (h : x ⧏ y) : ¬y < x := fun h' => h.not_ge h'.le
#align pgame.lf.not_gt SetTheory.PGame.LF.not_gt
-/

#print SetTheory.PGame.le_congr_imp /-
theorem SetTheory.PGame.le_congr_imp {x₁ y₁ x₂ y₂} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) (h : x₁ ≤ y₁) :
    x₂ ≤ y₂ :=
  hx.2.trans (h.trans hy.1)
#align pgame.le_congr_imp SetTheory.PGame.le_congr_imp
-/

#print SetTheory.PGame.le_congr /-
theorem SetTheory.PGame.le_congr {x₁ y₁ x₂ y₂} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ≤ y₁ ↔ x₂ ≤ y₂ :=
  ⟨SetTheory.PGame.le_congr_imp hx hy, SetTheory.PGame.le_congr_imp hx.symm hy.symm⟩
#align pgame.le_congr SetTheory.PGame.le_congr
-/

#print SetTheory.PGame.le_congr_left /-
theorem SetTheory.PGame.le_congr_left {x₁ x₂ y} (hx : x₁ ≈ x₂) : x₁ ≤ y ↔ x₂ ≤ y :=
  SetTheory.PGame.le_congr hx SetTheory.PGame.equiv_rfl
#align pgame.le_congr_left SetTheory.PGame.le_congr_left
-/

#print SetTheory.PGame.le_congr_right /-
theorem SetTheory.PGame.le_congr_right {x y₁ y₂} (hy : y₁ ≈ y₂) : x ≤ y₁ ↔ x ≤ y₂ :=
  SetTheory.PGame.le_congr SetTheory.PGame.equiv_rfl hy
#align pgame.le_congr_right SetTheory.PGame.le_congr_right
-/

#print SetTheory.PGame.lf_congr /-
theorem SetTheory.PGame.lf_congr {x₁ y₁ x₂ y₂} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ⧏ y₁ ↔ x₂ ⧏ y₂ :=
  SetTheory.PGame.not_le.symm.trans <|
    (not_congr (SetTheory.PGame.le_congr hy hx)).trans SetTheory.PGame.not_le
#align pgame.lf_congr SetTheory.PGame.lf_congr
-/

#print SetTheory.PGame.lf_congr_imp /-
theorem SetTheory.PGame.lf_congr_imp {x₁ y₁ x₂ y₂} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) :
    x₁ ⧏ y₁ → x₂ ⧏ y₂ :=
  (SetTheory.PGame.lf_congr hx hy).1
#align pgame.lf_congr_imp SetTheory.PGame.lf_congr_imp
-/

#print SetTheory.PGame.lf_congr_left /-
theorem SetTheory.PGame.lf_congr_left {x₁ x₂ y} (hx : x₁ ≈ x₂) : x₁ ⧏ y ↔ x₂ ⧏ y :=
  SetTheory.PGame.lf_congr hx SetTheory.PGame.equiv_rfl
#align pgame.lf_congr_left SetTheory.PGame.lf_congr_left
-/

#print SetTheory.PGame.lf_congr_right /-
theorem SetTheory.PGame.lf_congr_right {x y₁ y₂} (hy : y₁ ≈ y₂) : x ⧏ y₁ ↔ x ⧏ y₂ :=
  SetTheory.PGame.lf_congr SetTheory.PGame.equiv_rfl hy
#align pgame.lf_congr_right SetTheory.PGame.lf_congr_right
-/

#print SetTheory.PGame.lf_of_lf_of_equiv /-
@[trans]
theorem SetTheory.PGame.lf_of_lf_of_equiv {x y z} (h₁ : x ⧏ y) (h₂ : y ≈ z) : x ⧏ z :=
  SetTheory.PGame.lf_congr_imp SetTheory.PGame.equiv_rfl h₂ h₁
#align pgame.lf_of_lf_of_equiv SetTheory.PGame.lf_of_lf_of_equiv
-/

#print SetTheory.PGame.lf_of_equiv_of_lf /-
@[trans]
theorem SetTheory.PGame.lf_of_equiv_of_lf {x y z} (h₁ : x ≈ y) : y ⧏ z → x ⧏ z :=
  SetTheory.PGame.lf_congr_imp h₁.symm SetTheory.PGame.equiv_rfl
#align pgame.lf_of_equiv_of_lf SetTheory.PGame.lf_of_equiv_of_lf
-/

#print SetTheory.PGame.lt_of_lt_of_equiv /-
@[trans]
theorem SetTheory.PGame.lt_of_lt_of_equiv {x y z} (h₁ : x < y) (h₂ : y ≈ z) : x < z :=
  h₁.trans_le h₂.1
#align pgame.lt_of_lt_of_equiv SetTheory.PGame.lt_of_lt_of_equiv
-/

#print SetTheory.PGame.lt_of_equiv_of_lt /-
@[trans]
theorem SetTheory.PGame.lt_of_equiv_of_lt {x y z} (h₁ : x ≈ y) : y < z → x < z :=
  h₁.1.trans_lt
#align pgame.lt_of_equiv_of_lt SetTheory.PGame.lt_of_equiv_of_lt
-/

#print SetTheory.PGame.lt_congr_imp /-
theorem SetTheory.PGame.lt_congr_imp {x₁ y₁ x₂ y₂} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) (h : x₁ < y₁) :
    x₂ < y₂ :=
  hx.2.trans_lt (h.trans_le hy.1)
#align pgame.lt_congr_imp SetTheory.PGame.lt_congr_imp
-/

#print SetTheory.PGame.lt_congr /-
theorem SetTheory.PGame.lt_congr {x₁ y₁ x₂ y₂} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ < y₁ ↔ x₂ < y₂ :=
  ⟨SetTheory.PGame.lt_congr_imp hx hy, SetTheory.PGame.lt_congr_imp hx.symm hy.symm⟩
#align pgame.lt_congr SetTheory.PGame.lt_congr
-/

#print SetTheory.PGame.lt_congr_left /-
theorem SetTheory.PGame.lt_congr_left {x₁ x₂ y} (hx : x₁ ≈ x₂) : x₁ < y ↔ x₂ < y :=
  SetTheory.PGame.lt_congr hx SetTheory.PGame.equiv_rfl
#align pgame.lt_congr_left SetTheory.PGame.lt_congr_left
-/

#print SetTheory.PGame.lt_congr_right /-
theorem SetTheory.PGame.lt_congr_right {x y₁ y₂} (hy : y₁ ≈ y₂) : x < y₁ ↔ x < y₂ :=
  SetTheory.PGame.lt_congr SetTheory.PGame.equiv_rfl hy
#align pgame.lt_congr_right SetTheory.PGame.lt_congr_right
-/

#print SetTheory.PGame.lt_or_equiv_of_le /-
theorem SetTheory.PGame.lt_or_equiv_of_le {x y : SetTheory.PGame} (h : x ≤ y) : x < y ∨ (x ≈ y) :=
  and_or_left.mp ⟨h, (em <| y ≤ x).symm.imp_left SetTheory.PGame.not_le.1⟩
#align pgame.lt_or_equiv_of_le SetTheory.PGame.lt_or_equiv_of_le
-/

#print SetTheory.PGame.lf_or_equiv_or_gf /-
theorem SetTheory.PGame.lf_or_equiv_or_gf (x y : SetTheory.PGame) : x ⧏ y ∨ (x ≈ y) ∨ y ⧏ x :=
  by
  by_cases h : x ⧏ y
  · exact Or.inl h
  · right
    cases' lt_or_equiv_of_le (SetTheory.PGame.not_lf.1 h) with h' h'
    · exact Or.inr h'.lf
    · exact Or.inl h'.symm
#align pgame.lf_or_equiv_or_gf SetTheory.PGame.lf_or_equiv_or_gf
-/

#print SetTheory.PGame.equiv_congr_left /-
theorem SetTheory.PGame.equiv_congr_left {y₁ y₂} : (y₁ ≈ y₂) ↔ ∀ x₁, (x₁ ≈ y₁) ↔ (x₁ ≈ y₂) :=
  ⟨fun h x₁ => ⟨fun h' => h'.trans h, fun h' => h'.trans h.symm⟩, fun h =>
    (h y₁).1 <| SetTheory.PGame.equiv_rfl⟩
#align pgame.equiv_congr_left SetTheory.PGame.equiv_congr_left
-/

#print SetTheory.PGame.equiv_congr_right /-
theorem SetTheory.PGame.equiv_congr_right {x₁ x₂} : (x₁ ≈ x₂) ↔ ∀ y₁, (x₁ ≈ y₁) ↔ (x₂ ≈ y₁) :=
  ⟨fun h y₁ => ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩, fun h =>
    (h x₂).2 <| SetTheory.PGame.equiv_rfl⟩
#align pgame.equiv_congr_right SetTheory.PGame.equiv_congr_right
-/

#print SetTheory.PGame.equiv_of_mk_equiv /-
theorem SetTheory.PGame.equiv_of_mk_equiv {x y : SetTheory.PGame} (L : x.LeftMoves ≃ y.LeftMoves)
    (R : x.RightMoves ≃ y.RightMoves) (hl : ∀ i, x.moveLeft i ≈ y.moveLeft (L i))
    (hr : ∀ j, x.moveRight j ≈ y.moveRight (R j)) : x ≈ y :=
  by
  fconstructor <;> rw [le_def]
  · exact ⟨fun i => Or.inl ⟨_, (hl i).1⟩, fun j => Or.inr ⟨_, by simpa using (hr (R.symm j)).1⟩⟩
  · exact ⟨fun i => Or.inl ⟨_, by simpa using (hl (L.symm i)).2⟩, fun j => Or.inr ⟨_, (hr j).2⟩⟩
#align pgame.equiv_of_mk_equiv SetTheory.PGame.equiv_of_mk_equiv
-/

#print SetTheory.PGame.Fuzzy /-
/-- The fuzzy, confused, or incomparable relation on pre-games.

If `x ‖ 0`, then the first player can always win `x`. -/
def SetTheory.PGame.Fuzzy (x y : SetTheory.PGame) : Prop :=
  x ⧏ y ∧ y ⧏ x
#align pgame.fuzzy SetTheory.PGame.Fuzzy
-/

scoped infixl:50 " ‖ " => SetTheory.PGame.Fuzzy

#print SetTheory.PGame.Fuzzy.swap /-
@[symm]
theorem SetTheory.PGame.Fuzzy.swap {x y : SetTheory.PGame} : x ‖ y → y ‖ x :=
  And.symm
#align pgame.fuzzy.swap SetTheory.PGame.Fuzzy.swap
-/

instance : IsSymm _ (· ‖ ·) :=
  ⟨fun x y => SetTheory.PGame.Fuzzy.swap⟩

#print SetTheory.PGame.Fuzzy.swap_iff /-
theorem SetTheory.PGame.Fuzzy.swap_iff {x y : SetTheory.PGame} : x ‖ y ↔ y ‖ x :=
  ⟨SetTheory.PGame.Fuzzy.swap, SetTheory.PGame.Fuzzy.swap⟩
#align pgame.fuzzy.swap_iff SetTheory.PGame.Fuzzy.swap_iff
-/

#print SetTheory.PGame.fuzzy_irrefl /-
theorem SetTheory.PGame.fuzzy_irrefl (x : SetTheory.PGame) : ¬x ‖ x := fun h =>
  SetTheory.PGame.lf_irrefl x h.1
#align pgame.fuzzy_irrefl SetTheory.PGame.fuzzy_irrefl
-/

instance : IsIrrefl _ (· ‖ ·) :=
  ⟨SetTheory.PGame.fuzzy_irrefl⟩

#print SetTheory.PGame.lf_iff_lt_or_fuzzy /-
theorem SetTheory.PGame.lf_iff_lt_or_fuzzy {x y : SetTheory.PGame} : x ⧏ y ↔ x < y ∨ x ‖ y := by
  simp only [lt_iff_le_and_lf, fuzzy, ← SetTheory.PGame.not_le]; tauto
#align pgame.lf_iff_lt_or_fuzzy SetTheory.PGame.lf_iff_lt_or_fuzzy
-/

#print SetTheory.PGame.lf_of_fuzzy /-
theorem SetTheory.PGame.lf_of_fuzzy {x y : SetTheory.PGame} (h : x ‖ y) : x ⧏ y :=
  SetTheory.PGame.lf_iff_lt_or_fuzzy.2 (Or.inr h)
#align pgame.lf_of_fuzzy SetTheory.PGame.lf_of_fuzzy
-/

alias fuzzy.lf := lf_of_fuzzy
#align pgame.fuzzy.lf SetTheory.PGame.Fuzzy.lf

#print SetTheory.PGame.lt_or_fuzzy_of_lf /-
theorem SetTheory.PGame.lt_or_fuzzy_of_lf {x y : SetTheory.PGame} : x ⧏ y → x < y ∨ x ‖ y :=
  SetTheory.PGame.lf_iff_lt_or_fuzzy.1
#align pgame.lt_or_fuzzy_of_lf SetTheory.PGame.lt_or_fuzzy_of_lf
-/

#print SetTheory.PGame.Fuzzy.not_equiv /-
theorem SetTheory.PGame.Fuzzy.not_equiv {x y : SetTheory.PGame} (h : x ‖ y) : ¬(x ≈ y) := fun h' =>
  h'.1.not_gf h.2
#align pgame.fuzzy.not_equiv SetTheory.PGame.Fuzzy.not_equiv
-/

#print SetTheory.PGame.Fuzzy.not_equiv' /-
theorem SetTheory.PGame.Fuzzy.not_equiv' {x y : SetTheory.PGame} (h : x ‖ y) : ¬(y ≈ x) := fun h' =>
  h'.2.not_gf h.2
#align pgame.fuzzy.not_equiv' SetTheory.PGame.Fuzzy.not_equiv'
-/

#print SetTheory.PGame.not_fuzzy_of_le /-
theorem SetTheory.PGame.not_fuzzy_of_le {x y : SetTheory.PGame} (h : x ≤ y) : ¬x ‖ y := fun h' =>
  h'.2.not_ge h
#align pgame.not_fuzzy_of_le SetTheory.PGame.not_fuzzy_of_le
-/

#print SetTheory.PGame.not_fuzzy_of_ge /-
theorem SetTheory.PGame.not_fuzzy_of_ge {x y : SetTheory.PGame} (h : y ≤ x) : ¬x ‖ y := fun h' =>
  h'.1.not_ge h
#align pgame.not_fuzzy_of_ge SetTheory.PGame.not_fuzzy_of_ge
-/

#print SetTheory.PGame.Equiv.not_fuzzy /-
theorem SetTheory.PGame.Equiv.not_fuzzy {x y : SetTheory.PGame} (h : x ≈ y) : ¬x ‖ y :=
  SetTheory.PGame.not_fuzzy_of_le h.1
#align pgame.equiv.not_fuzzy SetTheory.PGame.Equiv.not_fuzzy
-/

#print SetTheory.PGame.Equiv.not_fuzzy' /-
theorem SetTheory.PGame.Equiv.not_fuzzy' {x y : SetTheory.PGame} (h : x ≈ y) : ¬y ‖ x :=
  SetTheory.PGame.not_fuzzy_of_le h.2
#align pgame.equiv.not_fuzzy' SetTheory.PGame.Equiv.not_fuzzy'
-/

#print SetTheory.PGame.fuzzy_congr /-
theorem SetTheory.PGame.fuzzy_congr {x₁ y₁ x₂ y₂ : SetTheory.PGame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) :
    x₁ ‖ y₁ ↔ x₂ ‖ y₂ :=
  show _ ∧ _ ↔ _ ∧ _ by rw [lf_congr hx hy, lf_congr hy hx]
#align pgame.fuzzy_congr SetTheory.PGame.fuzzy_congr
-/

#print SetTheory.PGame.fuzzy_congr_imp /-
theorem SetTheory.PGame.fuzzy_congr_imp {x₁ y₁ x₂ y₂ : SetTheory.PGame} (hx : x₁ ≈ x₂)
    (hy : y₁ ≈ y₂) : x₁ ‖ y₁ → x₂ ‖ y₂ :=
  (SetTheory.PGame.fuzzy_congr hx hy).1
#align pgame.fuzzy_congr_imp SetTheory.PGame.fuzzy_congr_imp
-/

#print SetTheory.PGame.fuzzy_congr_left /-
theorem SetTheory.PGame.fuzzy_congr_left {x₁ x₂ y} (hx : x₁ ≈ x₂) : x₁ ‖ y ↔ x₂ ‖ y :=
  SetTheory.PGame.fuzzy_congr hx SetTheory.PGame.equiv_rfl
#align pgame.fuzzy_congr_left SetTheory.PGame.fuzzy_congr_left
-/

#print SetTheory.PGame.fuzzy_congr_right /-
theorem SetTheory.PGame.fuzzy_congr_right {x y₁ y₂} (hy : y₁ ≈ y₂) : x ‖ y₁ ↔ x ‖ y₂ :=
  SetTheory.PGame.fuzzy_congr SetTheory.PGame.equiv_rfl hy
#align pgame.fuzzy_congr_right SetTheory.PGame.fuzzy_congr_right
-/

#print SetTheory.PGame.fuzzy_of_fuzzy_of_equiv /-
@[trans]
theorem SetTheory.PGame.fuzzy_of_fuzzy_of_equiv {x y z} (h₁ : x ‖ y) (h₂ : y ≈ z) : x ‖ z :=
  (SetTheory.PGame.fuzzy_congr_right h₂).1 h₁
#align pgame.fuzzy_of_fuzzy_of_equiv SetTheory.PGame.fuzzy_of_fuzzy_of_equiv
-/

#print SetTheory.PGame.fuzzy_of_equiv_of_fuzzy /-
@[trans]
theorem SetTheory.PGame.fuzzy_of_equiv_of_fuzzy {x y z} (h₁ : x ≈ y) (h₂ : y ‖ z) : x ‖ z :=
  (SetTheory.PGame.fuzzy_congr_left h₁).2 h₂
#align pgame.fuzzy_of_equiv_of_fuzzy SetTheory.PGame.fuzzy_of_equiv_of_fuzzy
-/

#print SetTheory.PGame.lt_or_equiv_or_gt_or_fuzzy /-
/-- Exactly one of the following is true (although we don't prove this here). -/
theorem SetTheory.PGame.lt_or_equiv_or_gt_or_fuzzy (x y : SetTheory.PGame) :
    x < y ∨ (x ≈ y) ∨ y < x ∨ x ‖ y :=
  by
  cases' le_or_gf x y with h₁ h₁ <;> cases' le_or_gf y x with h₂ h₂
  · right; left; exact ⟨h₁, h₂⟩
  · left; exact ⟨h₁, h₂⟩
  · right; right; left; exact ⟨h₂, h₁⟩
  · right; right; right; exact ⟨h₂, h₁⟩
#align pgame.lt_or_equiv_or_gt_or_fuzzy SetTheory.PGame.lt_or_equiv_or_gt_or_fuzzy
-/

#print SetTheory.PGame.lt_or_equiv_or_gf /-
theorem SetTheory.PGame.lt_or_equiv_or_gf (x y : SetTheory.PGame) : x < y ∨ (x ≈ y) ∨ y ⧏ x :=
  by
  rw [lf_iff_lt_or_fuzzy, fuzzy.swap_iff]
  exact lt_or_equiv_or_gt_or_fuzzy x y
#align pgame.lt_or_equiv_or_gf SetTheory.PGame.lt_or_equiv_or_gf
-/

/-! ### Relabellings -/


#print SetTheory.PGame.Relabelling /-
/-- `relabelling x y` says that `x` and `y` are really the same game, just dressed up differently.
Specifically, there is a bijection between the moves for Left in `x` and in `y`, and similarly
for Right, and under these bijections we inductively have `relabelling`s for the consequent games.
-/
inductive SetTheory.PGame.Relabelling : SetTheory.PGame.{u} → SetTheory.PGame.{u} → Type (u + 1)
  |
  mk :
    ∀ {x y : SetTheory.PGame} (L : x.LeftMoves ≃ y.LeftMoves) (R : x.RightMoves ≃ y.RightMoves),
      (∀ i, relabelling (x.moveLeft i) (y.moveLeft (L i))) →
        (∀ j, relabelling (x.moveRight j) (y.moveRight (R j))) → relabelling x y
#align pgame.relabelling SetTheory.PGame.Relabelling
-/

scoped infixl:50 " ≡r " => SetTheory.PGame.Relabelling

namespace Relabelling

variable {x y : SetTheory.PGame.{u}}

#print SetTheory.PGame.Relabelling.mk' /-
/-- A constructor for relabellings swapping the equivalences. -/
def SetTheory.PGame.Relabelling.mk' (L : y.LeftMoves ≃ x.LeftMoves)
    (R : y.RightMoves ≃ x.RightMoves) (hL : ∀ i, x.moveLeft (L i) ≡r y.moveLeft i)
    (hR : ∀ j, x.moveRight (R j) ≡r y.moveRight j) : x ≡r y :=
  ⟨L.symm, R.symm, fun i => by simpa using hL (L.symm i), fun j => by simpa using hR (R.symm j)⟩
#align pgame.relabelling.mk' SetTheory.PGame.Relabelling.mk'
-/

#print SetTheory.PGame.Relabelling.leftMovesEquiv /-
/-- The equivalence between left moves of `x` and `y` given by the relabelling. -/
def SetTheory.PGame.Relabelling.leftMovesEquiv : ∀ r : x ≡r y, x.LeftMoves ≃ y.LeftMoves
  | ⟨L, R, hL, hR⟩ => L
#align pgame.relabelling.left_moves_equiv SetTheory.PGame.Relabelling.leftMovesEquiv
-/

#print SetTheory.PGame.Relabelling.mk_leftMovesEquiv /-
@[simp]
theorem SetTheory.PGame.Relabelling.mk_leftMovesEquiv {x y L R hL hR} :
    (@SetTheory.PGame.Relabelling.mk x y L R hL hR).leftMovesEquiv = L :=
  rfl
#align pgame.relabelling.mk_left_moves_equiv SetTheory.PGame.Relabelling.mk_leftMovesEquiv
-/

#print SetTheory.PGame.Relabelling.mk'_leftMovesEquiv /-
@[simp]
theorem SetTheory.PGame.Relabelling.mk'_leftMovesEquiv {x y L R hL hR} :
    (@SetTheory.PGame.Relabelling.mk' x y L R hL hR).leftMovesEquiv = L.symm :=
  rfl
#align pgame.relabelling.mk'_left_moves_equiv SetTheory.PGame.Relabelling.mk'_leftMovesEquiv
-/

#print SetTheory.PGame.Relabelling.rightMovesEquiv /-
/-- The equivalence between right moves of `x` and `y` given by the relabelling. -/
def SetTheory.PGame.Relabelling.rightMovesEquiv : ∀ r : x ≡r y, x.RightMoves ≃ y.RightMoves
  | ⟨L, R, hL, hR⟩ => R
#align pgame.relabelling.right_moves_equiv SetTheory.PGame.Relabelling.rightMovesEquiv
-/

#print SetTheory.PGame.Relabelling.mk_rightMovesEquiv /-
@[simp]
theorem SetTheory.PGame.Relabelling.mk_rightMovesEquiv {x y L R hL hR} :
    (@SetTheory.PGame.Relabelling.mk x y L R hL hR).rightMovesEquiv = R :=
  rfl
#align pgame.relabelling.mk_right_moves_equiv SetTheory.PGame.Relabelling.mk_rightMovesEquiv
-/

#print SetTheory.PGame.Relabelling.mk'_rightMovesEquiv /-
@[simp]
theorem SetTheory.PGame.Relabelling.mk'_rightMovesEquiv {x y L R hL hR} :
    (@SetTheory.PGame.Relabelling.mk' x y L R hL hR).rightMovesEquiv = R.symm :=
  rfl
#align pgame.relabelling.mk'_right_moves_equiv SetTheory.PGame.Relabelling.mk'_rightMovesEquiv
-/

#print SetTheory.PGame.Relabelling.moveLeft /-
/-- A left move of `x` is a relabelling of a left move of `y`. -/
def SetTheory.PGame.Relabelling.moveLeft :
    ∀ (r : x ≡r y) (i : x.LeftMoves), x.moveLeft i ≡r y.moveLeft (r.leftMovesEquiv i)
  | ⟨L, R, hL, hR⟩ => hL
#align pgame.relabelling.move_left SetTheory.PGame.Relabelling.moveLeft
-/

#print SetTheory.PGame.Relabelling.moveLeftSymm /-
/-- A left move of `y` is a relabelling of a left move of `x`. -/
def SetTheory.PGame.Relabelling.moveLeftSymm :
    ∀ (r : x ≡r y) (i : y.LeftMoves), x.moveLeft (r.leftMovesEquiv.symm i) ≡r y.moveLeft i
  | ⟨L, R, hL, hR⟩, i => by simpa using hL (L.symm i)
#align pgame.relabelling.move_left_symm SetTheory.PGame.Relabelling.moveLeftSymm
-/

#print SetTheory.PGame.Relabelling.moveRight /-
/-- A right move of `x` is a relabelling of a right move of `y`. -/
def SetTheory.PGame.Relabelling.moveRight :
    ∀ (r : x ≡r y) (i : x.RightMoves), x.moveRight i ≡r y.moveRight (r.rightMovesEquiv i)
  | ⟨L, R, hL, hR⟩ => hR
#align pgame.relabelling.move_right SetTheory.PGame.Relabelling.moveRight
-/

#print SetTheory.PGame.Relabelling.moveRightSymm /-
/-- A right move of `y` is a relabelling of a right move of `x`. -/
def SetTheory.PGame.Relabelling.moveRightSymm :
    ∀ (r : x ≡r y) (i : y.RightMoves), x.moveRight (r.rightMovesEquiv.symm i) ≡r y.moveRight i
  | ⟨L, R, hL, hR⟩, i => by simpa using hR (R.symm i)
#align pgame.relabelling.move_right_symm SetTheory.PGame.Relabelling.moveRightSymm
-/

#print SetTheory.PGame.Relabelling.refl /-
/-- The identity relabelling. -/
@[refl]
def SetTheory.PGame.Relabelling.refl : ∀ x : SetTheory.PGame, x ≡r x
  | x => ⟨Equiv.refl _, Equiv.refl _, fun i => refl _, fun j => refl _⟩
decreasing_by pgame_wf_tac
#align pgame.relabelling.refl SetTheory.PGame.Relabelling.refl
-/

instance (x : SetTheory.PGame) : Inhabited (x ≡r x) :=
  ⟨SetTheory.PGame.Relabelling.refl _⟩

#print SetTheory.PGame.Relabelling.symm /-
/-- Flip a relabelling. -/
@[symm]
def SetTheory.PGame.Relabelling.symm : ∀ {x y : SetTheory.PGame}, x ≡r y → y ≡r x
  | x, y, ⟨L, R, hL, hR⟩ =>
    SetTheory.PGame.Relabelling.mk' L R (fun i => (hL i).symm) fun j => (hR j).symm
#align pgame.relabelling.symm SetTheory.PGame.Relabelling.symm
-/

#print SetTheory.PGame.Relabelling.le /-
theorem SetTheory.PGame.Relabelling.le : ∀ {x y : SetTheory.PGame} (r : x ≡r y), x ≤ y
  | x, y, r =>
    SetTheory.PGame.le_def.2
      ⟨fun i => Or.inl ⟨_, (r.moveLeft i).le⟩, fun j => Or.inr ⟨_, (r.moveRightSymm j).le⟩⟩
decreasing_by pgame_wf_tac
#align pgame.relabelling.le SetTheory.PGame.Relabelling.le
-/

#print SetTheory.PGame.Relabelling.ge /-
theorem SetTheory.PGame.Relabelling.ge {x y : SetTheory.PGame} (r : x ≡r y) : y ≤ x :=
  r.symm.le
#align pgame.relabelling.ge SetTheory.PGame.Relabelling.ge
-/

#print SetTheory.PGame.Relabelling.equiv /-
/-- A relabelling lets us prove equivalence of games. -/
theorem SetTheory.PGame.Relabelling.equiv (r : x ≡r y) : x ≈ y :=
  ⟨r.le, r.ge⟩
#align pgame.relabelling.equiv SetTheory.PGame.Relabelling.equiv
-/

#print SetTheory.PGame.Relabelling.trans /-
/-- Transitivity of relabelling. -/
@[trans]
def SetTheory.PGame.Relabelling.trans : ∀ {x y z : SetTheory.PGame}, x ≡r y → y ≡r z → x ≡r z
  | x, y, z, ⟨L₁, R₁, hL₁, hR₁⟩, ⟨L₂, R₂, hL₂, hR₂⟩ =>
    ⟨L₁.trans L₂, R₁.trans R₂, fun i => (hL₁ i).trans (hL₂ _), fun j => (hR₁ j).trans (hR₂ _)⟩
#align pgame.relabelling.trans SetTheory.PGame.Relabelling.trans
-/

#print SetTheory.PGame.Relabelling.isEmpty /-
/-- Any game without left or right moves is a relabelling of 0. -/
def SetTheory.PGame.Relabelling.isEmpty (x : SetTheory.PGame) [IsEmpty x.LeftMoves]
    [IsEmpty x.RightMoves] : x ≡r 0 :=
  ⟨Equiv.equivPEmpty _, Equiv.equivOfIsEmpty _ _, isEmptyElim, isEmptyElim⟩
#align pgame.relabelling.is_empty SetTheory.PGame.Relabelling.isEmpty
-/

end Relabelling

#print SetTheory.PGame.Equiv.isEmpty /-
theorem SetTheory.PGame.Equiv.isEmpty (x : SetTheory.PGame) [IsEmpty x.LeftMoves]
    [IsEmpty x.RightMoves] : x ≈ 0 :=
  (SetTheory.PGame.Relabelling.isEmpty x).Equiv
#align pgame.equiv.is_empty SetTheory.PGame.Equiv.isEmpty
-/

instance {x y : SetTheory.PGame} : Coe (x ≡r y) (x ≈ y) :=
  ⟨SetTheory.PGame.Relabelling.equiv⟩

#print SetTheory.PGame.relabel /-
/-- Replace the types indexing the next moves for Left and Right by equivalent types. -/
def SetTheory.PGame.relabel {x : SetTheory.PGame} {xl' xr'} (el : xl' ≃ x.LeftMoves)
    (er : xr' ≃ x.RightMoves) : SetTheory.PGame :=
  ⟨xl', xr', x.moveLeft ∘ el, x.moveRight ∘ er⟩
#align pgame.relabel SetTheory.PGame.relabel
-/

#print SetTheory.PGame.relabel_moveLeft' /-
@[simp]
theorem SetTheory.PGame.relabel_moveLeft' {x : SetTheory.PGame} {xl' xr'} (el : xl' ≃ x.LeftMoves)
    (er : xr' ≃ x.RightMoves) (i : xl') :
    SetTheory.PGame.moveLeft (SetTheory.PGame.relabel el er) i = x.moveLeft (el i) :=
  rfl
#align pgame.relabel_move_left' SetTheory.PGame.relabel_moveLeft'
-/

#print SetTheory.PGame.relabel_moveLeft /-
@[simp]
theorem SetTheory.PGame.relabel_moveLeft {x : SetTheory.PGame} {xl' xr'} (el : xl' ≃ x.LeftMoves)
    (er : xr' ≃ x.RightMoves) (i : x.LeftMoves) :
    SetTheory.PGame.moveLeft (SetTheory.PGame.relabel el er) (el.symm i) = x.moveLeft i := by simp
#align pgame.relabel_move_left SetTheory.PGame.relabel_moveLeft
-/

#print SetTheory.PGame.relabel_moveRight' /-
@[simp]
theorem SetTheory.PGame.relabel_moveRight' {x : SetTheory.PGame} {xl' xr'} (el : xl' ≃ x.LeftMoves)
    (er : xr' ≃ x.RightMoves) (j : xr') :
    SetTheory.PGame.moveRight (SetTheory.PGame.relabel el er) j = x.moveRight (er j) :=
  rfl
#align pgame.relabel_move_right' SetTheory.PGame.relabel_moveRight'
-/

#print SetTheory.PGame.relabel_moveRight /-
@[simp]
theorem SetTheory.PGame.relabel_moveRight {x : SetTheory.PGame} {xl' xr'} (el : xl' ≃ x.LeftMoves)
    (er : xr' ≃ x.RightMoves) (j : x.RightMoves) :
    SetTheory.PGame.moveRight (SetTheory.PGame.relabel el er) (er.symm j) = x.moveRight j := by simp
#align pgame.relabel_move_right SetTheory.PGame.relabel_moveRight
-/

#print SetTheory.PGame.relabelRelabelling /-
/-- The game obtained by relabelling the next moves is a relabelling of the original game. -/
def SetTheory.PGame.relabelRelabelling {x : SetTheory.PGame} {xl' xr'} (el : xl' ≃ x.LeftMoves)
    (er : xr' ≃ x.RightMoves) : x ≡r SetTheory.PGame.relabel el er :=
  SetTheory.PGame.Relabelling.mk' el er (fun i => by simp) fun j => by simp
#align pgame.relabel_relabelling SetTheory.PGame.relabelRelabelling
-/

/-! ### Negation -/


#print SetTheory.PGame.neg /-
/-- The negation of `{L | R}` is `{-R | -L}`. -/
def SetTheory.PGame.neg : SetTheory.PGame → SetTheory.PGame
  | ⟨l, r, L, R⟩ => ⟨r, l, fun i => neg (R i), fun i => neg (L i)⟩
#align pgame.neg SetTheory.PGame.neg
-/

instance : Neg SetTheory.PGame :=
  ⟨SetTheory.PGame.neg⟩

#print SetTheory.PGame.neg_def /-
@[simp]
theorem SetTheory.PGame.neg_def {xl xr xL xR} :
    -SetTheory.PGame.mk xl xr xL xR = SetTheory.PGame.mk xr xl (fun j => -xR j) fun i => -xL i :=
  rfl
#align pgame.neg_def SetTheory.PGame.neg_def
-/

instance : InvolutiveNeg SetTheory.PGame :=
  { SetTheory.PGame.hasNeg with
    neg_neg := fun x => by
      induction' x with xl xr xL xR ihL ihR
      simp_rw [neg_def, ihL, ihR]
      exact ⟨rfl, rfl, HEq.rfl, HEq.rfl⟩ }

instance : NegZeroClass SetTheory.PGame :=
  { SetTheory.PGame.hasZero, SetTheory.PGame.hasNeg with
    neg_zero := by
      dsimp [Zero.zero, Neg.neg, neg]
      congr <;> funext i <;> cases i }

#print SetTheory.PGame.neg_ofLists /-
@[simp]
theorem SetTheory.PGame.neg_ofLists (L R : List SetTheory.PGame) :
    -SetTheory.PGame.ofLists L R =
      SetTheory.PGame.ofLists (R.map fun x => -x) (L.map fun x => -x) :=
  by
  simp only [of_lists, neg_def, List.length_map, List.nthLe_map', eq_self_iff_true, true_and_iff]
  constructor;
  all_goals
    apply hfunext
    · simp
    · intro a a' ha
      congr 2
      have :
        ∀ {m n} (h₁ : m = n) {b : ULift (Fin m)} {c : ULift (Fin n)} (h₂ : HEq b c),
          (b.down : ℕ) = ↑c.down :=
        by rintro m n rfl b c rfl; rfl
      exact this (List.length_map _ _).symm ha
#align pgame.neg_of_lists SetTheory.PGame.neg_ofLists
-/

#print SetTheory.PGame.isOption_neg /-
theorem SetTheory.PGame.isOption_neg {x y : SetTheory.PGame} :
    SetTheory.PGame.IsOption x (-y) ↔ SetTheory.PGame.IsOption (-x) y :=
  by
  rw [is_option_iff, is_option_iff, or_comm]
  cases y; apply or_congr <;> · apply exists_congr; intro; rw [neg_eq_iff_eq_neg]; rfl
#align pgame.is_option_neg SetTheory.PGame.isOption_neg
-/

#print SetTheory.PGame.isOption_neg_neg /-
@[simp]
theorem SetTheory.PGame.isOption_neg_neg {x y : SetTheory.PGame} :
    SetTheory.PGame.IsOption (-x) (-y) ↔ SetTheory.PGame.IsOption x y := by
  rw [is_option_neg, neg_neg]
#align pgame.is_option_neg_neg SetTheory.PGame.isOption_neg_neg
-/

#print SetTheory.PGame.leftMoves_neg /-
theorem SetTheory.PGame.leftMoves_neg : ∀ x : SetTheory.PGame, (-x).LeftMoves = x.RightMoves
  | ⟨_, _, _, _⟩ => rfl
#align pgame.left_moves_neg SetTheory.PGame.leftMoves_neg
-/

#print SetTheory.PGame.rightMoves_neg /-
theorem SetTheory.PGame.rightMoves_neg : ∀ x : SetTheory.PGame, (-x).RightMoves = x.LeftMoves
  | ⟨_, _, _, _⟩ => rfl
#align pgame.right_moves_neg SetTheory.PGame.rightMoves_neg
-/

#print SetTheory.PGame.toLeftMovesNeg /-
/-- Turns a right move for `x` into a left move for `-x` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def SetTheory.PGame.toLeftMovesNeg {x : SetTheory.PGame} : x.RightMoves ≃ (-x).LeftMoves :=
  Equiv.cast (SetTheory.PGame.leftMoves_neg x).symm
#align pgame.to_left_moves_neg SetTheory.PGame.toLeftMovesNeg
-/

#print SetTheory.PGame.toRightMovesNeg /-
/-- Turns a left move for `x` into a right move for `-x` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def SetTheory.PGame.toRightMovesNeg {x : SetTheory.PGame} : x.LeftMoves ≃ (-x).RightMoves :=
  Equiv.cast (SetTheory.PGame.rightMoves_neg x).symm
#align pgame.to_right_moves_neg SetTheory.PGame.toRightMovesNeg
-/

#print SetTheory.PGame.moveLeft_neg /-
theorem SetTheory.PGame.moveLeft_neg {x : SetTheory.PGame} (i) :
    (-x).moveLeft (SetTheory.PGame.toLeftMovesNeg i) = -x.moveRight i := by cases x; rfl
#align pgame.move_left_neg SetTheory.PGame.moveLeft_neg
-/

#print SetTheory.PGame.moveLeft_neg' /-
@[simp]
theorem SetTheory.PGame.moveLeft_neg' {x : SetTheory.PGame} (i) :
    (-x).moveLeft i = -x.moveRight (SetTheory.PGame.toLeftMovesNeg.symm i) := by cases x; rfl
#align pgame.move_left_neg' SetTheory.PGame.moveLeft_neg'
-/

#print SetTheory.PGame.moveRight_neg /-
theorem SetTheory.PGame.moveRight_neg {x : SetTheory.PGame} (i) :
    (-x).moveRight (SetTheory.PGame.toRightMovesNeg i) = -x.moveLeft i := by cases x; rfl
#align pgame.move_right_neg SetTheory.PGame.moveRight_neg
-/

#print SetTheory.PGame.moveRight_neg' /-
@[simp]
theorem SetTheory.PGame.moveRight_neg' {x : SetTheory.PGame} (i) :
    (-x).moveRight i = -x.moveLeft (SetTheory.PGame.toRightMovesNeg.symm i) := by cases x; rfl
#align pgame.move_right_neg' SetTheory.PGame.moveRight_neg'
-/

#print SetTheory.PGame.moveLeft_neg_symm /-
theorem SetTheory.PGame.moveLeft_neg_symm {x : SetTheory.PGame} (i) :
    x.moveLeft (SetTheory.PGame.toRightMovesNeg.symm i) = -(-x).moveRight i := by simp
#align pgame.move_left_neg_symm SetTheory.PGame.moveLeft_neg_symm
-/

#print SetTheory.PGame.moveLeft_neg_symm' /-
theorem SetTheory.PGame.moveLeft_neg_symm' {x : SetTheory.PGame} (i) :
    x.moveLeft i = -(-x).moveRight (SetTheory.PGame.toRightMovesNeg i) := by simp
#align pgame.move_left_neg_symm' SetTheory.PGame.moveLeft_neg_symm'
-/

#print SetTheory.PGame.moveRight_neg_symm /-
theorem SetTheory.PGame.moveRight_neg_symm {x : SetTheory.PGame} (i) :
    x.moveRight (SetTheory.PGame.toLeftMovesNeg.symm i) = -(-x).moveLeft i := by simp
#align pgame.move_right_neg_symm SetTheory.PGame.moveRight_neg_symm
-/

#print SetTheory.PGame.moveRight_neg_symm' /-
theorem SetTheory.PGame.moveRight_neg_symm' {x : SetTheory.PGame} (i) :
    x.moveRight i = -(-x).moveLeft (SetTheory.PGame.toLeftMovesNeg i) := by simp
#align pgame.move_right_neg_symm' SetTheory.PGame.moveRight_neg_symm'
-/

#print SetTheory.PGame.Relabelling.negCongr /-
/-- If `x` has the same moves as `y`, then `-x` has the sames moves as `-y`. -/
def SetTheory.PGame.Relabelling.negCongr : ∀ {x y : SetTheory.PGame}, x ≡r y → -x ≡r -y
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩, ⟨L, R, hL, hR⟩ =>
    ⟨R, L, fun j => (hR j).negCongr, fun i => (hL i).negCongr⟩
#align pgame.relabelling.neg_congr SetTheory.PGame.Relabelling.negCongr
-/

private theorem neg_le_lf_neg_iff :
    ∀ {x y : SetTheory.PGame.{u}}, (-y ≤ -x ↔ x ≤ y) ∧ (-y ⧏ -x ↔ x ⧏ y)
  | mk xl xr xL xR, mk yl yr yL yR =>
    by
    simp_rw [neg_def, mk_le_mk, mk_lf_mk, ← neg_def]
    constructor
    · rw [and_comm]; apply and_congr <;> exact forall_congr' fun _ => neg_le_lf_neg_iff.2
    · rw [or_comm]; apply or_congr <;> exact exists_congr fun _ => neg_le_lf_neg_iff.1
decreasing_by pgame_wf_tac

#print SetTheory.PGame.neg_le_neg_iff /-
@[simp]
theorem SetTheory.PGame.neg_le_neg_iff {x y : SetTheory.PGame} : -y ≤ -x ↔ x ≤ y :=
  neg_le_lF_neg_iff.1
#align pgame.neg_le_neg_iff SetTheory.PGame.neg_le_neg_iff
-/

#print SetTheory.PGame.neg_lf_neg_iff /-
@[simp]
theorem SetTheory.PGame.neg_lf_neg_iff {x y : SetTheory.PGame} : -y ⧏ -x ↔ x ⧏ y :=
  neg_le_lF_neg_iff.2
#align pgame.neg_lf_neg_iff SetTheory.PGame.neg_lf_neg_iff
-/

#print SetTheory.PGame.neg_lt_neg_iff /-
@[simp]
theorem SetTheory.PGame.neg_lt_neg_iff {x y : SetTheory.PGame} : -y < -x ↔ x < y := by
  rw [lt_iff_le_and_lf, lt_iff_le_and_lf, neg_le_neg_iff, neg_lf_neg_iff]
#align pgame.neg_lt_neg_iff SetTheory.PGame.neg_lt_neg_iff
-/

#print SetTheory.PGame.neg_equiv_neg_iff /-
@[simp]
theorem SetTheory.PGame.neg_equiv_neg_iff {x y : SetTheory.PGame} : (-x ≈ -y) ↔ (x ≈ y) := by
  rw [Equiv, Equiv, neg_le_neg_iff, neg_le_neg_iff, and_comm]
#align pgame.neg_equiv_neg_iff SetTheory.PGame.neg_equiv_neg_iff
-/

#print SetTheory.PGame.neg_fuzzy_neg_iff /-
@[simp]
theorem SetTheory.PGame.neg_fuzzy_neg_iff {x y : SetTheory.PGame} : -x ‖ -y ↔ x ‖ y := by
  rw [fuzzy, fuzzy, neg_lf_neg_iff, neg_lf_neg_iff, and_comm]
#align pgame.neg_fuzzy_neg_iff SetTheory.PGame.neg_fuzzy_neg_iff
-/

#print SetTheory.PGame.neg_le_iff /-
theorem SetTheory.PGame.neg_le_iff {x y : SetTheory.PGame} : -y ≤ x ↔ -x ≤ y := by
  rw [← neg_neg x, neg_le_neg_iff, neg_neg]
#align pgame.neg_le_iff SetTheory.PGame.neg_le_iff
-/

#print SetTheory.PGame.neg_lf_iff /-
theorem SetTheory.PGame.neg_lf_iff {x y : SetTheory.PGame} : -y ⧏ x ↔ -x ⧏ y := by
  rw [← neg_neg x, neg_lf_neg_iff, neg_neg]
#align pgame.neg_lf_iff SetTheory.PGame.neg_lf_iff
-/

#print SetTheory.PGame.neg_lt_iff /-
theorem SetTheory.PGame.neg_lt_iff {x y : SetTheory.PGame} : -y < x ↔ -x < y := by
  rw [← neg_neg x, neg_lt_neg_iff, neg_neg]
#align pgame.neg_lt_iff SetTheory.PGame.neg_lt_iff
-/

#print SetTheory.PGame.neg_equiv_iff /-
theorem SetTheory.PGame.neg_equiv_iff {x y : SetTheory.PGame} : (-x ≈ y) ↔ (x ≈ -y) := by
  rw [← neg_neg y, neg_equiv_neg_iff, neg_neg]
#align pgame.neg_equiv_iff SetTheory.PGame.neg_equiv_iff
-/

#print SetTheory.PGame.neg_fuzzy_iff /-
theorem SetTheory.PGame.neg_fuzzy_iff {x y : SetTheory.PGame} : -x ‖ y ↔ x ‖ -y := by
  rw [← neg_neg y, neg_fuzzy_neg_iff, neg_neg]
#align pgame.neg_fuzzy_iff SetTheory.PGame.neg_fuzzy_iff
-/

#print SetTheory.PGame.le_neg_iff /-
theorem SetTheory.PGame.le_neg_iff {x y : SetTheory.PGame} : y ≤ -x ↔ x ≤ -y := by
  rw [← neg_neg x, neg_le_neg_iff, neg_neg]
#align pgame.le_neg_iff SetTheory.PGame.le_neg_iff
-/

#print SetTheory.PGame.lf_neg_iff /-
theorem SetTheory.PGame.lf_neg_iff {x y : SetTheory.PGame} : y ⧏ -x ↔ x ⧏ -y := by
  rw [← neg_neg x, neg_lf_neg_iff, neg_neg]
#align pgame.lf_neg_iff SetTheory.PGame.lf_neg_iff
-/

#print SetTheory.PGame.lt_neg_iff /-
theorem SetTheory.PGame.lt_neg_iff {x y : SetTheory.PGame} : y < -x ↔ x < -y := by
  rw [← neg_neg x, neg_lt_neg_iff, neg_neg]
#align pgame.lt_neg_iff SetTheory.PGame.lt_neg_iff
-/

#print SetTheory.PGame.neg_le_zero_iff /-
@[simp]
theorem SetTheory.PGame.neg_le_zero_iff {x : SetTheory.PGame} : -x ≤ 0 ↔ 0 ≤ x := by
  rw [neg_le_iff, neg_zero]
#align pgame.neg_le_zero_iff SetTheory.PGame.neg_le_zero_iff
-/

#print SetTheory.PGame.zero_le_neg_iff /-
@[simp]
theorem SetTheory.PGame.zero_le_neg_iff {x : SetTheory.PGame} : 0 ≤ -x ↔ x ≤ 0 := by
  rw [le_neg_iff, neg_zero]
#align pgame.zero_le_neg_iff SetTheory.PGame.zero_le_neg_iff
-/

#print SetTheory.PGame.neg_lf_zero_iff /-
@[simp]
theorem SetTheory.PGame.neg_lf_zero_iff {x : SetTheory.PGame} : -x ⧏ 0 ↔ 0 ⧏ x := by
  rw [neg_lf_iff, neg_zero]
#align pgame.neg_lf_zero_iff SetTheory.PGame.neg_lf_zero_iff
-/

#print SetTheory.PGame.zero_lf_neg_iff /-
@[simp]
theorem SetTheory.PGame.zero_lf_neg_iff {x : SetTheory.PGame} : 0 ⧏ -x ↔ x ⧏ 0 := by
  rw [lf_neg_iff, neg_zero]
#align pgame.zero_lf_neg_iff SetTheory.PGame.zero_lf_neg_iff
-/

#print SetTheory.PGame.neg_lt_zero_iff /-
@[simp]
theorem SetTheory.PGame.neg_lt_zero_iff {x : SetTheory.PGame} : -x < 0 ↔ 0 < x := by
  rw [neg_lt_iff, neg_zero]
#align pgame.neg_lt_zero_iff SetTheory.PGame.neg_lt_zero_iff
-/

#print SetTheory.PGame.zero_lt_neg_iff /-
@[simp]
theorem SetTheory.PGame.zero_lt_neg_iff {x : SetTheory.PGame} : 0 < -x ↔ x < 0 := by
  rw [lt_neg_iff, neg_zero]
#align pgame.zero_lt_neg_iff SetTheory.PGame.zero_lt_neg_iff
-/

#print SetTheory.PGame.neg_equiv_zero_iff /-
@[simp]
theorem SetTheory.PGame.neg_equiv_zero_iff {x : SetTheory.PGame} : (-x ≈ 0) ↔ (x ≈ 0) := by
  rw [neg_equiv_iff, neg_zero]
#align pgame.neg_equiv_zero_iff SetTheory.PGame.neg_equiv_zero_iff
-/

#print SetTheory.PGame.neg_fuzzy_zero_iff /-
@[simp]
theorem SetTheory.PGame.neg_fuzzy_zero_iff {x : SetTheory.PGame} : -x ‖ 0 ↔ x ‖ 0 := by
  rw [neg_fuzzy_iff, neg_zero]
#align pgame.neg_fuzzy_zero_iff SetTheory.PGame.neg_fuzzy_zero_iff
-/

#print SetTheory.PGame.zero_equiv_neg_iff /-
@[simp]
theorem SetTheory.PGame.zero_equiv_neg_iff {x : SetTheory.PGame} : (0 ≈ -x) ↔ (0 ≈ x) := by
  rw [← neg_equiv_iff, neg_zero]
#align pgame.zero_equiv_neg_iff SetTheory.PGame.zero_equiv_neg_iff
-/

#print SetTheory.PGame.zero_fuzzy_neg_iff /-
@[simp]
theorem SetTheory.PGame.zero_fuzzy_neg_iff {x : SetTheory.PGame} : 0 ‖ -x ↔ 0 ‖ x := by
  rw [← neg_fuzzy_iff, neg_zero]
#align pgame.zero_fuzzy_neg_iff SetTheory.PGame.zero_fuzzy_neg_iff
-/

/-! ### Addition and subtraction -/


/-- The sum of `x = {xL | xR}` and `y = {yL | yR}` is `{xL + y, x + yL | xR + y, x + yR}`. -/
instance : Add SetTheory.PGame.{u} :=
  ⟨fun x y => by
    induction' x with xl xr xL xR IHxl IHxr generalizing y
    induction' y with yl yr yL yR IHyl IHyr
    have y := mk yl yr yL yR
    refine' ⟨Sum xl yl, Sum xr yr, Sum.rec _ _, Sum.rec _ _⟩
    · exact fun i => IHxl i y
    · exact IHyl
    · exact fun i => IHxr i y
    · exact IHyr⟩

/-- The pre-game `((0+1)+⋯)+1`. -/
instance : NatCast SetTheory.PGame :=
  ⟨Nat.unaryCast⟩

#print SetTheory.PGame.nat_succ /-
@[simp]
protected theorem SetTheory.PGame.nat_succ (n : ℕ) : ((n + 1 : ℕ) : SetTheory.PGame) = n + 1 :=
  rfl
#align pgame.nat_succ SetTheory.PGame.nat_succ
-/

#print SetTheory.PGame.isEmpty_leftMoves_add /-
instance SetTheory.PGame.isEmpty_leftMoves_add (x y : SetTheory.PGame.{u}) [IsEmpty x.LeftMoves]
    [IsEmpty y.LeftMoves] : IsEmpty (x + y).LeftMoves :=
  by
  cases x; cases y
  apply isEmpty_sum.2 ⟨_, _⟩
  assumption'
#align pgame.is_empty_left_moves_add SetTheory.PGame.isEmpty_leftMoves_add
-/

#print SetTheory.PGame.isEmpty_rightMoves_add /-
instance SetTheory.PGame.isEmpty_rightMoves_add (x y : SetTheory.PGame.{u}) [IsEmpty x.RightMoves]
    [IsEmpty y.RightMoves] : IsEmpty (x + y).RightMoves :=
  by
  cases x; cases y
  apply isEmpty_sum.2 ⟨_, _⟩
  assumption'
#align pgame.is_empty_right_moves_add SetTheory.PGame.isEmpty_rightMoves_add
-/

#print SetTheory.PGame.addZeroRelabelling /-
/-- `x + 0` has exactly the same moves as `x`. -/
def SetTheory.PGame.addZeroRelabelling : ∀ x : SetTheory.PGame.{u}, x + 0 ≡r x
  | ⟨xl, xr, xL, xR⟩ => by
    refine' ⟨Equiv.sumEmpty xl PEmpty, Equiv.sumEmpty xr PEmpty, _, _⟩ <;> rintro (⟨i⟩ | ⟨⟨⟩⟩) <;>
      apply add_zero_relabelling
#align pgame.add_zero_relabelling SetTheory.PGame.addZeroRelabelling
-/

#print SetTheory.PGame.add_zero_equiv /-
/-- `x + 0` is equivalent to `x`. -/
theorem SetTheory.PGame.add_zero_equiv (x : SetTheory.PGame.{u}) : x + 0 ≈ x :=
  (SetTheory.PGame.addZeroRelabelling x).Equiv
#align pgame.add_zero_equiv SetTheory.PGame.add_zero_equiv
-/

#print SetTheory.PGame.zeroAddRelabelling /-
/-- `0 + x` has exactly the same moves as `x`. -/
def SetTheory.PGame.zeroAddRelabelling : ∀ x : SetTheory.PGame.{u}, 0 + x ≡r x
  | ⟨xl, xr, xL, xR⟩ => by
    refine' ⟨Equiv.emptySum PEmpty xl, Equiv.emptySum PEmpty xr, _, _⟩ <;> rintro (⟨⟨⟩⟩ | ⟨i⟩) <;>
      apply zero_add_relabelling
#align pgame.zero_add_relabelling SetTheory.PGame.zeroAddRelabelling
-/

#print SetTheory.PGame.zero_add_equiv /-
/-- `0 + x` is equivalent to `x`. -/
theorem SetTheory.PGame.zero_add_equiv (x : SetTheory.PGame.{u}) : 0 + x ≈ x :=
  (SetTheory.PGame.zeroAddRelabelling x).Equiv
#align pgame.zero_add_equiv SetTheory.PGame.zero_add_equiv
-/

#print SetTheory.PGame.leftMoves_add /-
theorem SetTheory.PGame.leftMoves_add :
    ∀ x y : SetTheory.PGame.{u}, (x + y).LeftMoves = Sum x.LeftMoves y.LeftMoves
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩ => rfl
#align pgame.left_moves_add SetTheory.PGame.leftMoves_add
-/

#print SetTheory.PGame.rightMoves_add /-
theorem SetTheory.PGame.rightMoves_add :
    ∀ x y : SetTheory.PGame.{u}, (x + y).RightMoves = Sum x.RightMoves y.RightMoves
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩ => rfl
#align pgame.right_moves_add SetTheory.PGame.rightMoves_add
-/

#print SetTheory.PGame.toLeftMovesAdd /-
/-- Converts a left move for `x` or `y` into a left move for `x + y` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def SetTheory.PGame.toLeftMovesAdd {x y : SetTheory.PGame} :
    Sum x.LeftMoves y.LeftMoves ≃ (x + y).LeftMoves :=
  Equiv.cast (SetTheory.PGame.leftMoves_add x y).symm
#align pgame.to_left_moves_add SetTheory.PGame.toLeftMovesAdd
-/

#print SetTheory.PGame.toRightMovesAdd /-
/-- Converts a right move for `x` or `y` into a right move for `x + y` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def SetTheory.PGame.toRightMovesAdd {x y : SetTheory.PGame} :
    Sum x.RightMoves y.RightMoves ≃ (x + y).RightMoves :=
  Equiv.cast (SetTheory.PGame.rightMoves_add x y).symm
#align pgame.to_right_moves_add SetTheory.PGame.toRightMovesAdd
-/

#print SetTheory.PGame.mk_add_moveLeft_inl /-
@[simp]
theorem SetTheory.PGame.mk_add_moveLeft_inl {xl xr yl yr} {xL xR yL yR} {i} :
    (SetTheory.PGame.mk xl xr xL xR + SetTheory.PGame.mk yl yr yL yR).moveLeft (Sum.inl i) =
      (SetTheory.PGame.mk xl xr xL xR).moveLeft i + SetTheory.PGame.mk yl yr yL yR :=
  rfl
#align pgame.mk_add_move_left_inl SetTheory.PGame.mk_add_moveLeft_inl
-/

#print SetTheory.PGame.add_moveLeft_inl /-
@[simp]
theorem SetTheory.PGame.add_moveLeft_inl {x : SetTheory.PGame} (y : SetTheory.PGame) (i) :
    (x + y).moveLeft (SetTheory.PGame.toLeftMovesAdd (Sum.inl i)) = x.moveLeft i + y := by cases x;
  cases y; rfl
#align pgame.add_move_left_inl SetTheory.PGame.add_moveLeft_inl
-/

#print SetTheory.PGame.mk_add_moveRight_inl /-
@[simp]
theorem SetTheory.PGame.mk_add_moveRight_inl {xl xr yl yr} {xL xR yL yR} {i} :
    (SetTheory.PGame.mk xl xr xL xR + SetTheory.PGame.mk yl yr yL yR).moveRight (Sum.inl i) =
      (SetTheory.PGame.mk xl xr xL xR).moveRight i + SetTheory.PGame.mk yl yr yL yR :=
  rfl
#align pgame.mk_add_move_right_inl SetTheory.PGame.mk_add_moveRight_inl
-/

#print SetTheory.PGame.add_moveRight_inl /-
@[simp]
theorem SetTheory.PGame.add_moveRight_inl {x : SetTheory.PGame} (y : SetTheory.PGame) (i) :
    (x + y).moveRight (SetTheory.PGame.toRightMovesAdd (Sum.inl i)) = x.moveRight i + y := by
  cases x; cases y; rfl
#align pgame.add_move_right_inl SetTheory.PGame.add_moveRight_inl
-/

#print SetTheory.PGame.mk_add_moveLeft_inr /-
@[simp]
theorem SetTheory.PGame.mk_add_moveLeft_inr {xl xr yl yr} {xL xR yL yR} {i} :
    (SetTheory.PGame.mk xl xr xL xR + SetTheory.PGame.mk yl yr yL yR).moveLeft (Sum.inr i) =
      SetTheory.PGame.mk xl xr xL xR + (SetTheory.PGame.mk yl yr yL yR).moveLeft i :=
  rfl
#align pgame.mk_add_move_left_inr SetTheory.PGame.mk_add_moveLeft_inr
-/

#print SetTheory.PGame.add_moveLeft_inr /-
@[simp]
theorem SetTheory.PGame.add_moveLeft_inr (x : SetTheory.PGame) {y : SetTheory.PGame} (i) :
    (x + y).moveLeft (SetTheory.PGame.toLeftMovesAdd (Sum.inr i)) = x + y.moveLeft i := by cases x;
  cases y; rfl
#align pgame.add_move_left_inr SetTheory.PGame.add_moveLeft_inr
-/

#print SetTheory.PGame.mk_add_moveRight_inr /-
@[simp]
theorem SetTheory.PGame.mk_add_moveRight_inr {xl xr yl yr} {xL xR yL yR} {i} :
    (SetTheory.PGame.mk xl xr xL xR + SetTheory.PGame.mk yl yr yL yR).moveRight (Sum.inr i) =
      SetTheory.PGame.mk xl xr xL xR + (SetTheory.PGame.mk yl yr yL yR).moveRight i :=
  rfl
#align pgame.mk_add_move_right_inr SetTheory.PGame.mk_add_moveRight_inr
-/

#print SetTheory.PGame.add_moveRight_inr /-
@[simp]
theorem SetTheory.PGame.add_moveRight_inr (x : SetTheory.PGame) {y : SetTheory.PGame} (i) :
    (x + y).moveRight (SetTheory.PGame.toRightMovesAdd (Sum.inr i)) = x + y.moveRight i := by
  cases x; cases y; rfl
#align pgame.add_move_right_inr SetTheory.PGame.add_moveRight_inr
-/

#print SetTheory.PGame.leftMoves_add_cases /-
theorem SetTheory.PGame.leftMoves_add_cases {x y : SetTheory.PGame} (k)
    {P : (x + y).LeftMoves → Prop} (hl : ∀ i, P <| SetTheory.PGame.toLeftMovesAdd (Sum.inl i))
    (hr : ∀ i, P <| SetTheory.PGame.toLeftMovesAdd (Sum.inr i)) : P k :=
  by
  rw [← to_left_moves_add.apply_symm_apply k]
  cases' to_left_moves_add.symm k with i i
  · exact hl i
  · exact hr i
#align pgame.left_moves_add_cases SetTheory.PGame.leftMoves_add_cases
-/

#print SetTheory.PGame.rightMoves_add_cases /-
theorem SetTheory.PGame.rightMoves_add_cases {x y : SetTheory.PGame} (k)
    {P : (x + y).RightMoves → Prop} (hl : ∀ j, P <| SetTheory.PGame.toRightMovesAdd (Sum.inl j))
    (hr : ∀ j, P <| SetTheory.PGame.toRightMovesAdd (Sum.inr j)) : P k :=
  by
  rw [← to_right_moves_add.apply_symm_apply k]
  cases' to_right_moves_add.symm k with i i
  · exact hl i
  · exact hr i
#align pgame.right_moves_add_cases SetTheory.PGame.rightMoves_add_cases
-/

#print SetTheory.PGame.isEmpty_nat_rightMoves /-
instance SetTheory.PGame.isEmpty_nat_rightMoves : ∀ n : ℕ, IsEmpty (SetTheory.PGame.RightMoves n)
  | 0 => PEmpty.isEmpty
  | n + 1 => by
    haveI := is_empty_nat_right_moves n
    rw [SetTheory.PGame.nat_succ, right_moves_add]
    infer_instance
#align pgame.is_empty_nat_right_moves SetTheory.PGame.isEmpty_nat_rightMoves
-/

#print SetTheory.PGame.Relabelling.addCongr /-
/-- If `w` has the same moves as `x` and `y` has the same moves as `z`,
then `w + y` has the same moves as `x + z`. -/
def SetTheory.PGame.Relabelling.addCongr :
    ∀ {w x y z : SetTheory.PGame.{u}}, w ≡r x → y ≡r z → w + y ≡r x + z
  | ⟨wl, wr, wL, wR⟩, ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩, ⟨zl, zr, zL, zR⟩, ⟨L₁, R₁, hL₁, hR₁⟩,
    ⟨L₂, R₂, hL₂, hR₂⟩ =>
    by
    let Hwx : ⟨wl, wr, wL, wR⟩ ≡r ⟨xl, xr, xL, xR⟩ := ⟨L₁, R₁, hL₁, hR₁⟩
    let Hyz : ⟨yl, yr, yL, yR⟩ ≡r ⟨zl, zr, zL, zR⟩ := ⟨L₂, R₂, hL₂, hR₂⟩
    refine' ⟨Equiv.sumCongr L₁ L₂, Equiv.sumCongr R₁ R₂, _, _⟩ <;> rintro (i | j)
    · exact (hL₁ i).addCongr Hyz
    · exact Hwx.add_congr (hL₂ j)
    · exact (hR₁ i).addCongr Hyz
    · exact Hwx.add_congr (hR₂ j)
decreasing_by pgame_wf_tac
#align pgame.relabelling.add_congr SetTheory.PGame.Relabelling.addCongr
-/

instance : Sub SetTheory.PGame :=
  ⟨fun x y => x + -y⟩

#print SetTheory.PGame.sub_zero /-
@[simp]
theorem SetTheory.PGame.sub_zero (x : SetTheory.PGame) : x - 0 = x + 0 :=
  show x + -0 = x + 0 by rw [neg_zero]
#align pgame.sub_zero SetTheory.PGame.sub_zero
-/

#print SetTheory.PGame.Relabelling.subCongr /-
/-- If `w` has the same moves as `x` and `y` has the same moves as `z`,
then `w - y` has the same moves as `x - z`. -/
def SetTheory.PGame.Relabelling.subCongr {w x y z : SetTheory.PGame} (h₁ : w ≡r x) (h₂ : y ≡r z) :
    w - y ≡r x - z :=
  h₁.addCongr h₂.negCongr
#align pgame.relabelling.sub_congr SetTheory.PGame.Relabelling.subCongr
-/

#print SetTheory.PGame.negAddRelabelling /-
/-- `-(x + y)` has exactly the same moves as `-x + -y`. -/
def SetTheory.PGame.negAddRelabelling : ∀ x y : SetTheory.PGame, -(x + y) ≡r -x + -y
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩ =>
    by
    refine' ⟨Equiv.refl _, Equiv.refl _, _, _⟩
    all_goals
      exact fun j =>
        Sum.casesOn j (fun j => neg_add_relabelling _ _) fun j =>
          neg_add_relabelling ⟨xl, xr, xL, xR⟩ _
decreasing_by pgame_wf_tac
#align pgame.neg_add_relabelling SetTheory.PGame.negAddRelabelling
-/

#print SetTheory.PGame.neg_add_le /-
theorem SetTheory.PGame.neg_add_le {x y : SetTheory.PGame} : -(x + y) ≤ -x + -y :=
  (SetTheory.PGame.negAddRelabelling x y).le
#align pgame.neg_add_le SetTheory.PGame.neg_add_le
-/

#print SetTheory.PGame.addCommRelabelling /-
/-- `x + y` has exactly the same moves as `y + x`. -/
def SetTheory.PGame.addCommRelabelling : ∀ x y : SetTheory.PGame.{u}, x + y ≡r y + x
  | mk xl xr xL xR, mk yl yr yL yR => by
    refine' ⟨Equiv.sumComm _ _, Equiv.sumComm _ _, _, _⟩ <;> rintro (_ | _) <;>
      · dsimp [left_moves_add, right_moves_add]; apply add_comm_relabelling
decreasing_by pgame_wf_tac
#align pgame.add_comm_relabelling SetTheory.PGame.addCommRelabelling
-/

#print SetTheory.PGame.add_comm_le /-
theorem SetTheory.PGame.add_comm_le {x y : SetTheory.PGame} : x + y ≤ y + x :=
  (SetTheory.PGame.addCommRelabelling x y).le
#align pgame.add_comm_le SetTheory.PGame.add_comm_le
-/

#print SetTheory.PGame.add_comm_equiv /-
theorem SetTheory.PGame.add_comm_equiv {x y : SetTheory.PGame} : x + y ≈ y + x :=
  (SetTheory.PGame.addCommRelabelling x y).Equiv
#align pgame.add_comm_equiv SetTheory.PGame.add_comm_equiv
-/

#print SetTheory.PGame.addAssocRelabelling /-
/-- `(x + y) + z` has exactly the same moves as `x + (y + z)`. -/
def SetTheory.PGame.addAssocRelabelling : ∀ x y z : SetTheory.PGame.{u}, x + y + z ≡r x + (y + z)
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩, ⟨zl, zr, zL, zR⟩ =>
    by
    refine' ⟨Equiv.sumAssoc _ _ _, Equiv.sumAssoc _ _ _, _, _⟩
    all_goals
      first
      | rintro (⟨i | i⟩ | i)
      | rintro (j | ⟨j | j⟩)
      · apply add_assoc_relabelling
      · apply add_assoc_relabelling ⟨xl, xr, xL, xR⟩
      · apply add_assoc_relabelling ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩
decreasing_by pgame_wf_tac
#align pgame.add_assoc_relabelling SetTheory.PGame.addAssocRelabelling
-/

#print SetTheory.PGame.add_assoc_equiv /-
theorem SetTheory.PGame.add_assoc_equiv {x y z : SetTheory.PGame} : x + y + z ≈ x + (y + z) :=
  (SetTheory.PGame.addAssocRelabelling x y z).Equiv
#align pgame.add_assoc_equiv SetTheory.PGame.add_assoc_equiv
-/

#print SetTheory.PGame.add_left_neg_le_zero /-
theorem SetTheory.PGame.add_left_neg_le_zero : ∀ x : SetTheory.PGame, -x + x ≤ 0
  | ⟨xl, xr, xL, xR⟩ =>
    SetTheory.PGame.le_zero.2 fun i => by
      cases i
      · -- If Left played in -x, Right responds with the same move in x.
        refine' ⟨@to_right_moves_add _ ⟨_, _, _, _⟩ (Sum.inr i), _⟩
        convert @add_left_neg_le_zero (xR i)
        apply add_move_right_inr
      · -- If Left in x, Right responds with the same move in -x.
        dsimp
        refine' ⟨@to_right_moves_add ⟨_, _, _, _⟩ _ (Sum.inl i), _⟩
        convert @add_left_neg_le_zero (xL i)
        apply add_move_right_inl
#align pgame.add_left_neg_le_zero SetTheory.PGame.add_left_neg_le_zero
-/

#print SetTheory.PGame.zero_le_add_left_neg /-
theorem SetTheory.PGame.zero_le_add_left_neg (x : SetTheory.PGame) : 0 ≤ -x + x :=
  by
  rw [← neg_le_neg_iff, neg_zero]
  exact neg_add_le.trans (add_left_neg_le_zero _)
#align pgame.zero_le_add_left_neg SetTheory.PGame.zero_le_add_left_neg
-/

#print SetTheory.PGame.add_left_neg_equiv /-
theorem SetTheory.PGame.add_left_neg_equiv (x : SetTheory.PGame) : -x + x ≈ 0 :=
  ⟨SetTheory.PGame.add_left_neg_le_zero x, SetTheory.PGame.zero_le_add_left_neg x⟩
#align pgame.add_left_neg_equiv SetTheory.PGame.add_left_neg_equiv
-/

#print SetTheory.PGame.add_right_neg_le_zero /-
theorem SetTheory.PGame.add_right_neg_le_zero (x : SetTheory.PGame) : x + -x ≤ 0 :=
  SetTheory.PGame.add_comm_le.trans (SetTheory.PGame.add_left_neg_le_zero x)
#align pgame.add_right_neg_le_zero SetTheory.PGame.add_right_neg_le_zero
-/

#print SetTheory.PGame.zero_le_add_right_neg /-
theorem SetTheory.PGame.zero_le_add_right_neg (x : SetTheory.PGame) : 0 ≤ x + -x :=
  (SetTheory.PGame.zero_le_add_left_neg x).trans SetTheory.PGame.add_comm_le
#align pgame.zero_le_add_right_neg SetTheory.PGame.zero_le_add_right_neg
-/

#print SetTheory.PGame.add_right_neg_equiv /-
theorem SetTheory.PGame.add_right_neg_equiv (x : SetTheory.PGame) : x + -x ≈ 0 :=
  ⟨SetTheory.PGame.add_right_neg_le_zero x, SetTheory.PGame.zero_le_add_right_neg x⟩
#align pgame.add_right_neg_equiv SetTheory.PGame.add_right_neg_equiv
-/

#print SetTheory.PGame.sub_self_equiv /-
theorem SetTheory.PGame.sub_self_equiv : ∀ x, x - x ≈ 0 :=
  SetTheory.PGame.add_right_neg_equiv
#align pgame.sub_self_equiv SetTheory.PGame.sub_self_equiv
-/

private theorem add_le_add_right' : ∀ {x y z : SetTheory.PGame} (h : x ≤ y), x + z ≤ y + z
  | mk xl xr xL xR, mk yl yr yL yR, mk zl zr zL zR => fun h =>
    by
    refine' le_def.2 ⟨fun i => _, fun i => _⟩ <;> cases i
    · rw [le_def] at h
      cases h
      rcases h_left i with (⟨i', ih⟩ | ⟨j, jh⟩)
      · exact Or.inl ⟨to_left_moves_add (Sum.inl i'), add_le_add_right' ih⟩
      · refine' Or.inr ⟨to_right_moves_add (Sum.inl j), _⟩
        convert add_le_add_right' jh
        apply add_move_right_inl
    · exact Or.inl ⟨@to_left_moves_add _ ⟨_, _, _, _⟩ (Sum.inr i), add_le_add_right' h⟩
    · rw [le_def] at h
      cases h
      rcases h_right i with (⟨i, ih⟩ | ⟨j', jh⟩)
      · refine' Or.inl ⟨to_left_moves_add (Sum.inl i), _⟩
        convert add_le_add_right' ih
        apply add_move_left_inl
      · exact Or.inr ⟨to_right_moves_add (Sum.inl j'), add_le_add_right' jh⟩
    · exact Or.inr ⟨@to_right_moves_add _ ⟨_, _, _, _⟩ (Sum.inr i), add_le_add_right' h⟩
decreasing_by pgame_wf_tac

#print SetTheory.PGame.covariantClass_swap_add_le /-
instance SetTheory.PGame.covariantClass_swap_add_le :
    CovariantClass SetTheory.PGame SetTheory.PGame (swap (· + ·)) (· ≤ ·) :=
  ⟨fun x y z => add_le_add_right'⟩
#align pgame.covariant_class_swap_add_le SetTheory.PGame.covariantClass_swap_add_le
-/

#print SetTheory.PGame.covariantClass_add_le /-
instance SetTheory.PGame.covariantClass_add_le :
    CovariantClass SetTheory.PGame SetTheory.PGame (· + ·) (· ≤ ·) :=
  ⟨fun x y z h =>
    (SetTheory.PGame.add_comm_le.trans (add_le_add_right h x)).trans SetTheory.PGame.add_comm_le⟩
#align pgame.covariant_class_add_le SetTheory.PGame.covariantClass_add_le
-/

#print SetTheory.PGame.add_lf_add_right /-
theorem SetTheory.PGame.add_lf_add_right {y z : SetTheory.PGame} (h : y ⧏ z) (x) : y + x ⧏ z + x :=
  suffices z + x ≤ y + x → z ≤ y by rw [← SetTheory.PGame.not_le] at h ⊢; exact mt this h
  fun w =>
  calc
    z ≤ z + 0 := (SetTheory.PGame.addZeroRelabelling _).symm.le
    _ ≤ z + (x + -x) := (add_le_add_left (SetTheory.PGame.zero_le_add_right_neg x) _)
    _ ≤ z + x + -x := (SetTheory.PGame.addAssocRelabelling _ _ _).symm.le
    _ ≤ y + x + -x := (add_le_add_right w _)
    _ ≤ y + (x + -x) := (SetTheory.PGame.addAssocRelabelling _ _ _).le
    _ ≤ y + 0 := (add_le_add_left (SetTheory.PGame.add_right_neg_le_zero x) _)
    _ ≤ y := (SetTheory.PGame.addZeroRelabelling _).le
#align pgame.add_lf_add_right SetTheory.PGame.add_lf_add_right
-/

#print SetTheory.PGame.add_lf_add_left /-
theorem SetTheory.PGame.add_lf_add_left {y z : SetTheory.PGame} (h : y ⧏ z) (x) : x + y ⧏ x + z :=
  by rw [lf_congr add_comm_equiv add_comm_equiv]; apply add_lf_add_right h
#align pgame.add_lf_add_left SetTheory.PGame.add_lf_add_left
-/

#print SetTheory.PGame.covariantClass_swap_add_lt /-
instance SetTheory.PGame.covariantClass_swap_add_lt :
    CovariantClass SetTheory.PGame SetTheory.PGame (swap (· + ·)) (· < ·) :=
  ⟨fun x y z h => ⟨add_le_add_right h.1 x, SetTheory.PGame.add_lf_add_right h.2 x⟩⟩
#align pgame.covariant_class_swap_add_lt SetTheory.PGame.covariantClass_swap_add_lt
-/

#print SetTheory.PGame.covariantClass_add_lt /-
instance SetTheory.PGame.covariantClass_add_lt :
    CovariantClass SetTheory.PGame SetTheory.PGame (· + ·) (· < ·) :=
  ⟨fun x y z h => ⟨add_le_add_left h.1 x, SetTheory.PGame.add_lf_add_left h.2 x⟩⟩
#align pgame.covariant_class_add_lt SetTheory.PGame.covariantClass_add_lt
-/

#print SetTheory.PGame.add_lf_add_of_lf_of_le /-
theorem SetTheory.PGame.add_lf_add_of_lf_of_le {w x y z : SetTheory.PGame} (hwx : w ⧏ x)
    (hyz : y ≤ z) : w + y ⧏ x + z :=
  SetTheory.PGame.lf_of_lf_of_le (SetTheory.PGame.add_lf_add_right hwx y) (add_le_add_left hyz x)
#align pgame.add_lf_add_of_lf_of_le SetTheory.PGame.add_lf_add_of_lf_of_le
-/

#print SetTheory.PGame.add_lf_add_of_le_of_lf /-
theorem SetTheory.PGame.add_lf_add_of_le_of_lf {w x y z : SetTheory.PGame} (hwx : w ≤ x)
    (hyz : y ⧏ z) : w + y ⧏ x + z :=
  SetTheory.PGame.lf_of_le_of_lf (add_le_add_right hwx y) (SetTheory.PGame.add_lf_add_left hyz x)
#align pgame.add_lf_add_of_le_of_lf SetTheory.PGame.add_lf_add_of_le_of_lf
-/

#print SetTheory.PGame.add_congr /-
theorem SetTheory.PGame.add_congr {w x y z : SetTheory.PGame} (h₁ : w ≈ x) (h₂ : y ≈ z) :
    w + y ≈ x + z :=
  ⟨(add_le_add_left h₂.1 w).trans (add_le_add_right h₁.1 z),
    (add_le_add_left h₂.2 x).trans (add_le_add_right h₁.2 y)⟩
#align pgame.add_congr SetTheory.PGame.add_congr
-/

#print SetTheory.PGame.add_congr_left /-
theorem SetTheory.PGame.add_congr_left {x y z : SetTheory.PGame} (h : x ≈ y) : x + z ≈ y + z :=
  SetTheory.PGame.add_congr h SetTheory.PGame.equiv_rfl
#align pgame.add_congr_left SetTheory.PGame.add_congr_left
-/

#print SetTheory.PGame.add_congr_right /-
theorem SetTheory.PGame.add_congr_right {x y z : SetTheory.PGame} : (y ≈ z) → (x + y ≈ x + z) :=
  SetTheory.PGame.add_congr SetTheory.PGame.equiv_rfl
#align pgame.add_congr_right SetTheory.PGame.add_congr_right
-/

#print SetTheory.PGame.sub_congr /-
theorem SetTheory.PGame.sub_congr {w x y z : SetTheory.PGame} (h₁ : w ≈ x) (h₂ : y ≈ z) :
    w - y ≈ x - z :=
  SetTheory.PGame.add_congr h₁ (SetTheory.PGame.neg_equiv_neg_iff.2 h₂)
#align pgame.sub_congr SetTheory.PGame.sub_congr
-/

#print SetTheory.PGame.sub_congr_left /-
theorem SetTheory.PGame.sub_congr_left {x y z : SetTheory.PGame} (h : x ≈ y) : x - z ≈ y - z :=
  SetTheory.PGame.sub_congr h SetTheory.PGame.equiv_rfl
#align pgame.sub_congr_left SetTheory.PGame.sub_congr_left
-/

#print SetTheory.PGame.sub_congr_right /-
theorem SetTheory.PGame.sub_congr_right {x y z : SetTheory.PGame} : (y ≈ z) → (x - y ≈ x - z) :=
  SetTheory.PGame.sub_congr SetTheory.PGame.equiv_rfl
#align pgame.sub_congr_right SetTheory.PGame.sub_congr_right
-/

#print SetTheory.PGame.le_iff_sub_nonneg /-
theorem SetTheory.PGame.le_iff_sub_nonneg {x y : SetTheory.PGame} : x ≤ y ↔ 0 ≤ y - x :=
  ⟨fun h => (SetTheory.PGame.zero_le_add_right_neg x).trans (add_le_add_right h _), fun h =>
    calc
      x ≤ 0 + x := (SetTheory.PGame.zeroAddRelabelling x).symm.le
      _ ≤ y - x + x := (add_le_add_right h _)
      _ ≤ y + (-x + x) := (SetTheory.PGame.addAssocRelabelling _ _ _).le
      _ ≤ y + 0 := (add_le_add_left (SetTheory.PGame.add_left_neg_le_zero x) _)
      _ ≤ y := (SetTheory.PGame.addZeroRelabelling y).le⟩
#align pgame.le_iff_sub_nonneg SetTheory.PGame.le_iff_sub_nonneg
-/

#print SetTheory.PGame.lf_iff_sub_zero_lf /-
theorem SetTheory.PGame.lf_iff_sub_zero_lf {x y : SetTheory.PGame} : x ⧏ y ↔ 0 ⧏ y - x :=
  ⟨fun h =>
    (SetTheory.PGame.zero_le_add_right_neg x).trans_lf (SetTheory.PGame.add_lf_add_right h _),
    fun h =>
    calc
      x ≤ 0 + x := (SetTheory.PGame.zeroAddRelabelling x).symm.le
      _ ⧏ y - x + x := (SetTheory.PGame.add_lf_add_right h _)
      _ ≤ y + (-x + x) := (SetTheory.PGame.addAssocRelabelling _ _ _).le
      _ ≤ y + 0 := (add_le_add_left (SetTheory.PGame.add_left_neg_le_zero x) _)
      _ ≤ y := (SetTheory.PGame.addZeroRelabelling y).le⟩
#align pgame.lf_iff_sub_zero_lf SetTheory.PGame.lf_iff_sub_zero_lf
-/

#print SetTheory.PGame.lt_iff_sub_pos /-
theorem SetTheory.PGame.lt_iff_sub_pos {x y : SetTheory.PGame} : x < y ↔ 0 < y - x :=
  ⟨fun h => lt_of_le_of_lt (SetTheory.PGame.zero_le_add_right_neg x) (add_lt_add_right h _),
    fun h =>
    calc
      x ≤ 0 + x := (SetTheory.PGame.zeroAddRelabelling x).symm.le
      _ < y - x + x := (add_lt_add_right h _)
      _ ≤ y + (-x + x) := (SetTheory.PGame.addAssocRelabelling _ _ _).le
      _ ≤ y + 0 := (add_le_add_left (SetTheory.PGame.add_left_neg_le_zero x) _)
      _ ≤ y := (SetTheory.PGame.addZeroRelabelling y).le⟩
#align pgame.lt_iff_sub_pos SetTheory.PGame.lt_iff_sub_pos
-/

/-! ### Special pre-games -/


#print SetTheory.PGame.star /-
/-- The pre-game `star`, which is fuzzy with zero. -/
def SetTheory.PGame.star : SetTheory.PGame.{u} :=
  ⟨PUnit, PUnit, fun _ => 0, fun _ => 0⟩
#align pgame.star SetTheory.PGame.star
-/

#print SetTheory.PGame.star_leftMoves /-
@[simp]
theorem SetTheory.PGame.star_leftMoves : SetTheory.PGame.star.LeftMoves = PUnit :=
  rfl
#align pgame.star_left_moves SetTheory.PGame.star_leftMoves
-/

#print SetTheory.PGame.star_rightMoves /-
@[simp]
theorem SetTheory.PGame.star_rightMoves : SetTheory.PGame.star.RightMoves = PUnit :=
  rfl
#align pgame.star_right_moves SetTheory.PGame.star_rightMoves
-/

#print SetTheory.PGame.star_moveLeft /-
@[simp]
theorem SetTheory.PGame.star_moveLeft (x) : SetTheory.PGame.star.moveLeft x = 0 :=
  rfl
#align pgame.star_move_left SetTheory.PGame.star_moveLeft
-/

#print SetTheory.PGame.star_moveRight /-
@[simp]
theorem SetTheory.PGame.star_moveRight (x) : SetTheory.PGame.star.moveRight x = 0 :=
  rfl
#align pgame.star_move_right SetTheory.PGame.star_moveRight
-/

#print SetTheory.PGame.uniqueStarLeftMoves /-
instance SetTheory.PGame.uniqueStarLeftMoves : Unique SetTheory.PGame.star.LeftMoves :=
  PUnit.unique
#align pgame.unique_star_left_moves SetTheory.PGame.uniqueStarLeftMoves
-/

#print SetTheory.PGame.uniqueStarRightMoves /-
instance SetTheory.PGame.uniqueStarRightMoves : Unique SetTheory.PGame.star.RightMoves :=
  PUnit.unique
#align pgame.unique_star_right_moves SetTheory.PGame.uniqueStarRightMoves
-/

#print SetTheory.PGame.star_fuzzy_zero /-
theorem SetTheory.PGame.star_fuzzy_zero : SetTheory.PGame.star ‖ 0 :=
  ⟨by rw [lf_zero]; use default; rintro ⟨⟩, by rw [zero_lf]; use default; rintro ⟨⟩⟩
#align pgame.star_fuzzy_zero SetTheory.PGame.star_fuzzy_zero
-/

#print SetTheory.PGame.neg_star /-
@[simp]
theorem SetTheory.PGame.neg_star : -SetTheory.PGame.star = SetTheory.PGame.star := by simp [star]
#align pgame.neg_star SetTheory.PGame.neg_star
-/

#print SetTheory.PGame.zero_lt_one /-
@[simp]
protected theorem SetTheory.PGame.zero_lt_one : (0 : SetTheory.PGame) < 1 :=
  SetTheory.PGame.lt_of_le_of_lf (SetTheory.PGame.zero_le_of_isEmpty_rightMoves 1)
    (SetTheory.PGame.zero_lf_le.2 ⟨default, le_rfl⟩)
#align pgame.zero_lt_one SetTheory.PGame.zero_lt_one
-/

instance : ZeroLEOneClass SetTheory.PGame :=
  ⟨SetTheory.PGame.zero_lt_one.le⟩

#print SetTheory.PGame.zero_lf_one /-
@[simp]
theorem SetTheory.PGame.zero_lf_one : (0 : SetTheory.PGame) ⧏ 1 :=
  SetTheory.PGame.zero_lt_one.LF
#align pgame.zero_lf_one SetTheory.PGame.zero_lf_one
-/

end SetTheory.PGame

