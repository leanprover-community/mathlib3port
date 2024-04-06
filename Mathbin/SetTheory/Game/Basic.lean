/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Isabel Longbottom, Scott Morrison, Apurva Nakade
-/
import SetTheory.Game.PGame
import Tactic.Abel

#align_import set_theory.game.basic from "leanprover-community/mathlib"@"8900d545017cd21961daa2a1734bb658ef52c618"

/-!
# Combinatorial games.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define the quotient of pre-games by the equivalence relation
`p ≈ q ↔ p ≤ q ∧ q ≤ p` (its `antisymmetrization`), and construct an instance `add_comm_group game`,
as well as an instance `partial_order game`.

## Multiplication on pre-games

We define the operations of multiplication and inverse on pre-games, and prove a few basic theorems
about them. Multiplication is not well-behaved under equivalence of pre-games i.e. `x ≈ y` does not
imply `x * z ≈ y * z`. Hence, multiplication is not a well-defined operation on games. Nevertheless,
the abelian group structure on games allows us to simplify many proofs for pre-games.
-/


open Function SetTheory.PGame

open scoped SetTheory.PGame

universe u

#print SetTheory.PGame.setoid /-
instance SetTheory.PGame.setoid : Setoid SetTheory.PGame :=
  ⟨(· ≈ ·), SetTheory.PGame.equiv_refl, @SetTheory.PGame.Equiv.symm, @SetTheory.PGame.Equiv.trans⟩
#align pgame.setoid SetTheory.PGame.setoid
-/

#print SetTheory.Game /-
/-- The type of combinatorial games. In ZFC, a combinatorial game is constructed from
  two sets of combinatorial games that have been constructed at an earlier
  stage. To do this in type theory, we say that a combinatorial pre-game is built
  inductively from two families of combinatorial games indexed over any type
  in Type u. The resulting type `pgame.{u}` lives in `Type (u+1)`,
  reflecting that it is a proper class in ZFC.
  A combinatorial game is then constructed by quotienting by the equivalence
  `x ≈ y ↔ x ≤ y ∧ y ≤ x`. -/
abbrev SetTheory.Game :=
  Quotient SetTheory.PGame.setoid
#align game SetTheory.Game
-/

namespace SetTheory.Game

instance : AddCommGroupWithOne SetTheory.Game
    where
  zero := ⟦0⟧
  one := ⟦1⟧
  neg :=
    Quot.lift (fun x => ⟦-x⟧) fun x y h => Quot.sound ((@SetTheory.PGame.neg_equiv_neg_iff x y).2 h)
  add :=
    Quotient.lift₂ (fun x y : SetTheory.PGame => ⟦x + y⟧) fun x₁ y₁ x₂ y₂ hx hy =>
      Quot.sound (SetTheory.PGame.add_congr hx hy)
  add_zero := by rintro ⟨x⟩; exact Quot.sound (add_zero_equiv x)
  zero_add := by rintro ⟨x⟩; exact Quot.sound (zero_add_equiv x)
  add_assoc := by rintro ⟨x⟩ ⟨y⟩ ⟨z⟩; exact Quot.sound add_assoc_equiv
  add_left_neg := by rintro ⟨x⟩; exact Quot.sound (add_left_neg_equiv x)
  add_comm := by rintro ⟨x⟩ ⟨y⟩; exact Quot.sound add_comm_equiv

instance : Inhabited SetTheory.Game :=
  ⟨0⟩

instance : PartialOrder SetTheory.Game
    where
  le := Quotient.lift₂ (· ≤ ·) fun x₁ y₁ x₂ y₂ hx hy => propext (SetTheory.PGame.le_congr hx hy)
  le_refl := by rintro ⟨x⟩; exact le_refl x
  le_trans := by rintro ⟨x⟩ ⟨y⟩ ⟨z⟩; exact @le_trans _ _ x y z
  le_antisymm := by rintro ⟨x⟩ ⟨y⟩ h₁ h₂; apply Quot.sound; exact ⟨h₁, h₂⟩
  lt := Quotient.lift₂ (· < ·) fun x₁ y₁ x₂ y₂ hx hy => propext (SetTheory.PGame.lt_congr hx hy)
  lt_iff_le_not_le := by rintro ⟨x⟩ ⟨y⟩; exact @lt_iff_le_not_le _ _ x y

#print SetTheory.Game.LF /-
/-- The less or fuzzy relation on games.

If `0 ⧏ x` (less or fuzzy with), then Left can win `x` as the first player. -/
def SetTheory.Game.LF : SetTheory.Game → SetTheory.Game → Prop :=
  Quotient.lift₂ SetTheory.PGame.LF fun x₁ y₁ x₂ y₂ hx hy =>
    propext (SetTheory.PGame.lf_congr hx hy)
#align game.lf SetTheory.Game.LF
-/

local infixl:50 " ⧏ " => SetTheory.Game.LF

#print SetTheory.Game.not_le /-
/-- On `game`, simp-normal inequalities should use as few negations as possible. -/
@[simp]
theorem SetTheory.Game.not_le : ∀ {x y : SetTheory.Game}, ¬x ≤ y ↔ y ⧏ x := by rintro ⟨x⟩ ⟨y⟩;
  exact SetTheory.PGame.not_le
#align game.not_le SetTheory.Game.not_le
-/

#print SetTheory.Game.not_lf /-
/-- On `game`, simp-normal inequalities should use as few negations as possible. -/
@[simp]
theorem SetTheory.Game.not_lf : ∀ {x y : SetTheory.Game}, ¬x ⧏ y ↔ y ≤ x := by rintro ⟨x⟩ ⟨y⟩;
  exact not_lf
#align game.not_lf SetTheory.Game.not_lf
-/

instance : IsTrichotomous SetTheory.Game (· ⧏ ·) :=
  ⟨by rintro ⟨x⟩ ⟨y⟩; change _ ∨ ⟦x⟧ = ⟦y⟧ ∨ _; rw [Quotient.eq']; apply lf_or_equiv_or_gf⟩

/-! It can be useful to use these lemmas to turn `pgame` inequalities into `game` inequalities, as
the `add_comm_group` structure on `game` often simplifies many proofs. -/


theorem SetTheory.PGame.le_iff_game_le {x y : SetTheory.PGame} : x ≤ y ↔ ⟦x⟧ ≤ ⟦y⟧ :=
  Iff.rfl
#align pgame.le_iff_game_le SetTheory.PGame.le_iff_game_le

theorem SetTheory.PGame.lF_iff_game_lF {x y : SetTheory.PGame} :
    SetTheory.PGame.LF x y ↔ ⟦x⟧ ⧏ ⟦y⟧ :=
  Iff.rfl
#align pgame.lf_iff_game_lf SetTheory.PGame.lF_iff_game_lF

theorem SetTheory.PGame.lt_iff_game_lt {x y : SetTheory.PGame} : x < y ↔ ⟦x⟧ < ⟦y⟧ :=
  Iff.rfl
#align pgame.lt_iff_game_lt SetTheory.PGame.lt_iff_game_lt

theorem SetTheory.PGame.equiv_iff_game_eq {x y : SetTheory.PGame} : (x ≈ y) ↔ ⟦x⟧ = ⟦y⟧ :=
  (@Quotient.eq' _ _ x y).symm
#align pgame.equiv_iff_game_eq SetTheory.PGame.equiv_iff_game_eq

#print SetTheory.Game.Fuzzy /-
/-- The fuzzy, confused, or incomparable relation on games.

If `x ‖ 0`, then the first player can always win `x`. -/
def SetTheory.Game.Fuzzy : SetTheory.Game → SetTheory.Game → Prop :=
  Quotient.lift₂ SetTheory.PGame.Fuzzy fun x₁ y₁ x₂ y₂ hx hy =>
    propext (SetTheory.PGame.fuzzy_congr hx hy)
#align game.fuzzy SetTheory.Game.Fuzzy
-/

local infixl:50 " ‖ " => SetTheory.Game.Fuzzy

theorem SetTheory.PGame.fuzzy_iff_game_fuzzy {x y : SetTheory.PGame} :
    SetTheory.PGame.Fuzzy x y ↔ ⟦x⟧ ‖ ⟦y⟧ :=
  Iff.rfl
#align pgame.fuzzy_iff_game_fuzzy SetTheory.PGame.fuzzy_iff_game_fuzzy

#print SetTheory.Game.covariantClass_add_le /-
instance SetTheory.Game.covariantClass_add_le :
    CovariantClass SetTheory.Game SetTheory.Game (· + ·) (· ≤ ·) :=
  ⟨by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h; exact @add_le_add_left _ _ _ _ b c h a⟩
#align game.covariant_class_add_le SetTheory.Game.covariantClass_add_le
-/

#print SetTheory.Game.covariantClass_swap_add_le /-
instance SetTheory.Game.covariantClass_swap_add_le :
    CovariantClass SetTheory.Game SetTheory.Game (swap (· + ·)) (· ≤ ·) :=
  ⟨by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h; exact @add_le_add_right _ _ _ _ b c h a⟩
#align game.covariant_class_swap_add_le SetTheory.Game.covariantClass_swap_add_le
-/

#print SetTheory.Game.covariantClass_add_lt /-
instance SetTheory.Game.covariantClass_add_lt :
    CovariantClass SetTheory.Game SetTheory.Game (· + ·) (· < ·) :=
  ⟨by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h; exact @add_lt_add_left _ _ _ _ b c h a⟩
#align game.covariant_class_add_lt SetTheory.Game.covariantClass_add_lt
-/

#print SetTheory.Game.covariantClass_swap_add_lt /-
instance SetTheory.Game.covariantClass_swap_add_lt :
    CovariantClass SetTheory.Game SetTheory.Game (swap (· + ·)) (· < ·) :=
  ⟨by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h; exact @add_lt_add_right _ _ _ _ b c h a⟩
#align game.covariant_class_swap_add_lt SetTheory.Game.covariantClass_swap_add_lt
-/

#print SetTheory.Game.add_lf_add_right /-
theorem SetTheory.Game.add_lf_add_right : ∀ {b c : SetTheory.Game} (h : b ⧏ c) (a), b + a ⧏ c + a :=
  by rintro ⟨b⟩ ⟨c⟩ h ⟨a⟩; apply add_lf_add_right h
#align game.add_lf_add_right SetTheory.Game.add_lf_add_right
-/

#print SetTheory.Game.add_lf_add_left /-
theorem SetTheory.Game.add_lf_add_left : ∀ {b c : SetTheory.Game} (h : b ⧏ c) (a), a + b ⧏ a + c :=
  by rintro ⟨b⟩ ⟨c⟩ h ⟨a⟩; apply add_lf_add_left h
#align game.add_lf_add_left SetTheory.Game.add_lf_add_left
-/

#print SetTheory.Game.orderedAddCommGroup /-
instance SetTheory.Game.orderedAddCommGroup : OrderedAddCommGroup SetTheory.Game :=
  { SetTheory.Game.addCommGroupWithOne, SetTheory.Game.partialOrder with
    add_le_add_left := @add_le_add_left _ _ _ SetTheory.Game.covariantClass_add_le }
#align game.ordered_add_comm_group SetTheory.Game.orderedAddCommGroup
-/

#print SetTheory.Game.bddAbove_of_small /-
/-- A small set `s` of games is bounded above. -/
theorem SetTheory.Game.bddAbove_of_small (s : Set SetTheory.Game.{u}) [Small.{u} s] : BddAbove s :=
  ⟨_, fun i hi => by
    simpa using
      SetTheory.PGame.le_iff_game_le.1
        (upper_bound_mem_upper_bounds _ (Set.mem_image_of_mem Quotient.out hi))⟩
#align game.bdd_above_of_small SetTheory.Game.bddAbove_of_small
-/

#print SetTheory.Game.bddBelow_of_small /-
/-- A small set `s` of games is bounded below. -/
theorem SetTheory.Game.bddBelow_of_small (s : Set SetTheory.Game.{u}) [Small.{u} s] : BddBelow s :=
  ⟨_, fun i hi => by
    simpa using
      SetTheory.PGame.le_iff_game_le.1
        (lower_bound_mem_lower_bounds _ (Set.mem_image_of_mem Quotient.out hi))⟩
#align game.bdd_below_of_small SetTheory.Game.bddBelow_of_small
-/

end SetTheory.Game

namespace SetTheory.PGame

#print SetTheory.PGame.quot_neg /-
@[simp]
theorem SetTheory.PGame.quot_neg (a : SetTheory.PGame) : ⟦-a⟧ = -⟦a⟧ :=
  rfl
#align pgame.quot_neg SetTheory.PGame.quot_neg
-/

#print SetTheory.PGame.quot_add /-
@[simp]
theorem SetTheory.PGame.quot_add (a b : SetTheory.PGame) : ⟦a + b⟧ = ⟦a⟧ + ⟦b⟧ :=
  rfl
#align pgame.quot_add SetTheory.PGame.quot_add
-/

#print SetTheory.PGame.quot_sub /-
@[simp]
theorem SetTheory.PGame.quot_sub (a b : SetTheory.PGame) : ⟦a - b⟧ = ⟦a⟧ - ⟦b⟧ :=
  rfl
#align pgame.quot_sub SetTheory.PGame.quot_sub
-/

#print SetTheory.PGame.quot_eq_of_mk'_quot_eq /-
theorem SetTheory.PGame.quot_eq_of_mk'_quot_eq {x y : SetTheory.PGame}
    (L : x.LeftMoves ≃ y.LeftMoves) (R : x.RightMoves ≃ y.RightMoves)
    (hl : ∀ i, ⟦x.moveLeft i⟧ = ⟦y.moveLeft (L i)⟧)
    (hr : ∀ j, ⟦x.moveRight j⟧ = ⟦y.moveRight (R j)⟧) : ⟦x⟧ = ⟦y⟧ := by
  simp_rw [Quotient.eq'] at hl hr; exact Quot.sound (equiv_of_mk_equiv L R hl hr)
#align pgame.quot_eq_of_mk_quot_eq SetTheory.PGame.quot_eq_of_mk'_quot_eq
-/

/-! Multiplicative operations can be defined at the level of pre-games,
but to prove their properties we need to use the abelian group structure of games.
Hence we define them here. -/


/-- The product of `x = {xL | xR}` and `y = {yL | yR}` is
`{xL*y + x*yL - xL*yL, xR*y + x*yR - xR*yR | xL*y + x*yR - xL*yR, x*yL + xR*y - xR*yL }`. -/
instance : Mul SetTheory.PGame.{u} :=
  ⟨fun x y => by
    induction' x with xl xr xL xR IHxl IHxr generalizing y
    induction' y with yl yr yL yR IHyl IHyr
    have y := mk yl yr yL yR
    refine' ⟨Sum (xl × yl) (xr × yr), Sum (xl × yr) (xr × yl), _, _⟩ <;> rintro (⟨i, j⟩ | ⟨i, j⟩)
    · exact IHxl i y + IHyl j - IHxl i (yL j)
    · exact IHxr i y + IHyr j - IHxr i (yR j)
    · exact IHxl i y + IHyr j - IHxl i (yR j)
    · exact IHxr i y + IHyl j - IHxr i (yL j)⟩

#print SetTheory.PGame.leftMoves_mul /-
theorem SetTheory.PGame.leftMoves_mul :
    ∀ x y : SetTheory.PGame.{u},
      (x * y).LeftMoves = Sum (x.LeftMoves × y.LeftMoves) (x.RightMoves × y.RightMoves)
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩ => rfl
#align pgame.left_moves_mul SetTheory.PGame.leftMoves_mul
-/

#print SetTheory.PGame.rightMoves_mul /-
theorem SetTheory.PGame.rightMoves_mul :
    ∀ x y : SetTheory.PGame.{u},
      (x * y).RightMoves = Sum (x.LeftMoves × y.RightMoves) (x.RightMoves × y.LeftMoves)
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩ => rfl
#align pgame.right_moves_mul SetTheory.PGame.rightMoves_mul
-/

#print SetTheory.PGame.toLeftMovesMul /-
/-- Turns two left or right moves for `x` and `y` into a left move for `x * y` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def SetTheory.PGame.toLeftMovesMul {x y : SetTheory.PGame} :
    Sum (x.LeftMoves × y.LeftMoves) (x.RightMoves × y.RightMoves) ≃ (x * y).LeftMoves :=
  Equiv.cast (SetTheory.PGame.leftMoves_mul x y).symm
#align pgame.to_left_moves_mul SetTheory.PGame.toLeftMovesMul
-/

#print SetTheory.PGame.toRightMovesMul /-
/-- Turns a left and a right move for `x` and `y` into a right move for `x * y` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def SetTheory.PGame.toRightMovesMul {x y : SetTheory.PGame} :
    Sum (x.LeftMoves × y.RightMoves) (x.RightMoves × y.LeftMoves) ≃ (x * y).RightMoves :=
  Equiv.cast (SetTheory.PGame.rightMoves_mul x y).symm
#align pgame.to_right_moves_mul SetTheory.PGame.toRightMovesMul
-/

#print SetTheory.PGame.mk_mul_moveLeft_inl /-
@[simp]
theorem SetTheory.PGame.mk_mul_moveLeft_inl {xl xr yl yr} {xL xR yL yR} {i j} :
    (SetTheory.PGame.mk xl xr xL xR * SetTheory.PGame.mk yl yr yL yR).moveLeft (Sum.inl (i, j)) =
      xL i * SetTheory.PGame.mk yl yr yL yR + SetTheory.PGame.mk xl xr xL xR * yL j - xL i * yL j :=
  rfl
#align pgame.mk_mul_move_left_inl SetTheory.PGame.mk_mul_moveLeft_inl
-/

#print SetTheory.PGame.mul_moveLeft_inl /-
@[simp]
theorem SetTheory.PGame.mul_moveLeft_inl {x y : SetTheory.PGame} {i j} :
    (x * y).moveLeft (SetTheory.PGame.toLeftMovesMul (Sum.inl (i, j))) =
      x.moveLeft i * y + x * y.moveLeft j - x.moveLeft i * y.moveLeft j :=
  by cases x; cases y; rfl
#align pgame.mul_move_left_inl SetTheory.PGame.mul_moveLeft_inl
-/

#print SetTheory.PGame.mk_mul_moveLeft_inr /-
@[simp]
theorem SetTheory.PGame.mk_mul_moveLeft_inr {xl xr yl yr} {xL xR yL yR} {i j} :
    (SetTheory.PGame.mk xl xr xL xR * SetTheory.PGame.mk yl yr yL yR).moveLeft (Sum.inr (i, j)) =
      xR i * SetTheory.PGame.mk yl yr yL yR + SetTheory.PGame.mk xl xr xL xR * yR j - xR i * yR j :=
  rfl
#align pgame.mk_mul_move_left_inr SetTheory.PGame.mk_mul_moveLeft_inr
-/

#print SetTheory.PGame.mul_moveLeft_inr /-
@[simp]
theorem SetTheory.PGame.mul_moveLeft_inr {x y : SetTheory.PGame} {i j} :
    (x * y).moveLeft (SetTheory.PGame.toLeftMovesMul (Sum.inr (i, j))) =
      x.moveRight i * y + x * y.moveRight j - x.moveRight i * y.moveRight j :=
  by cases x; cases y; rfl
#align pgame.mul_move_left_inr SetTheory.PGame.mul_moveLeft_inr
-/

#print SetTheory.PGame.mk_mul_moveRight_inl /-
@[simp]
theorem SetTheory.PGame.mk_mul_moveRight_inl {xl xr yl yr} {xL xR yL yR} {i j} :
    (SetTheory.PGame.mk xl xr xL xR * SetTheory.PGame.mk yl yr yL yR).moveRight (Sum.inl (i, j)) =
      xL i * SetTheory.PGame.mk yl yr yL yR + SetTheory.PGame.mk xl xr xL xR * yR j - xL i * yR j :=
  rfl
#align pgame.mk_mul_move_right_inl SetTheory.PGame.mk_mul_moveRight_inl
-/

#print SetTheory.PGame.mul_moveRight_inl /-
@[simp]
theorem SetTheory.PGame.mul_moveRight_inl {x y : SetTheory.PGame} {i j} :
    (x * y).moveRight (SetTheory.PGame.toRightMovesMul (Sum.inl (i, j))) =
      x.moveLeft i * y + x * y.moveRight j - x.moveLeft i * y.moveRight j :=
  by cases x; cases y; rfl
#align pgame.mul_move_right_inl SetTheory.PGame.mul_moveRight_inl
-/

#print SetTheory.PGame.mk_mul_moveRight_inr /-
@[simp]
theorem SetTheory.PGame.mk_mul_moveRight_inr {xl xr yl yr} {xL xR yL yR} {i j} :
    (SetTheory.PGame.mk xl xr xL xR * SetTheory.PGame.mk yl yr yL yR).moveRight (Sum.inr (i, j)) =
      xR i * SetTheory.PGame.mk yl yr yL yR + SetTheory.PGame.mk xl xr xL xR * yL j - xR i * yL j :=
  rfl
#align pgame.mk_mul_move_right_inr SetTheory.PGame.mk_mul_moveRight_inr
-/

#print SetTheory.PGame.mul_moveRight_inr /-
@[simp]
theorem SetTheory.PGame.mul_moveRight_inr {x y : SetTheory.PGame} {i j} :
    (x * y).moveRight (SetTheory.PGame.toRightMovesMul (Sum.inr (i, j))) =
      x.moveRight i * y + x * y.moveLeft j - x.moveRight i * y.moveLeft j :=
  by cases x; cases y; rfl
#align pgame.mul_move_right_inr SetTheory.PGame.mul_moveRight_inr
-/

#print SetTheory.PGame.neg_mk_mul_moveLeft_inl /-
@[simp]
theorem SetTheory.PGame.neg_mk_mul_moveLeft_inl {xl xr yl yr} {xL xR yL yR} {i j} :
    (-(SetTheory.PGame.mk xl xr xL xR * SetTheory.PGame.mk yl yr yL yR)).moveLeft (Sum.inl (i, j)) =
      -(xL i * SetTheory.PGame.mk yl yr yL yR + SetTheory.PGame.mk xl xr xL xR * yR j -
          xL i * yR j) :=
  rfl
#align pgame.neg_mk_mul_move_left_inl SetTheory.PGame.neg_mk_mul_moveLeft_inl
-/

#print SetTheory.PGame.neg_mk_mul_moveLeft_inr /-
@[simp]
theorem SetTheory.PGame.neg_mk_mul_moveLeft_inr {xl xr yl yr} {xL xR yL yR} {i j} :
    (-(SetTheory.PGame.mk xl xr xL xR * SetTheory.PGame.mk yl yr yL yR)).moveLeft (Sum.inr (i, j)) =
      -(xR i * SetTheory.PGame.mk yl yr yL yR + SetTheory.PGame.mk xl xr xL xR * yL j -
          xR i * yL j) :=
  rfl
#align pgame.neg_mk_mul_move_left_inr SetTheory.PGame.neg_mk_mul_moveLeft_inr
-/

#print SetTheory.PGame.neg_mk_mul_moveRight_inl /-
@[simp]
theorem SetTheory.PGame.neg_mk_mul_moveRight_inl {xl xr yl yr} {xL xR yL yR} {i j} :
    (-(SetTheory.PGame.mk xl xr xL xR * SetTheory.PGame.mk yl yr yL yR)).moveRight
        (Sum.inl (i, j)) =
      -(xL i * SetTheory.PGame.mk yl yr yL yR + SetTheory.PGame.mk xl xr xL xR * yL j -
          xL i * yL j) :=
  rfl
#align pgame.neg_mk_mul_move_right_inl SetTheory.PGame.neg_mk_mul_moveRight_inl
-/

#print SetTheory.PGame.neg_mk_mul_moveRight_inr /-
@[simp]
theorem SetTheory.PGame.neg_mk_mul_moveRight_inr {xl xr yl yr} {xL xR yL yR} {i j} :
    (-(SetTheory.PGame.mk xl xr xL xR * SetTheory.PGame.mk yl yr yL yR)).moveRight
        (Sum.inr (i, j)) =
      -(xR i * SetTheory.PGame.mk yl yr yL yR + SetTheory.PGame.mk xl xr xL xR * yR j -
          xR i * yR j) :=
  rfl
#align pgame.neg_mk_mul_move_right_inr SetTheory.PGame.neg_mk_mul_moveRight_inr
-/

#print SetTheory.PGame.leftMoves_mul_cases /-
theorem SetTheory.PGame.leftMoves_mul_cases {x y : SetTheory.PGame} (k)
    {P : (x * y).LeftMoves → Prop}
    (hl : ∀ ix iy, P <| SetTheory.PGame.toLeftMovesMul (Sum.inl ⟨ix, iy⟩))
    (hr : ∀ jx jy, P <| SetTheory.PGame.toLeftMovesMul (Sum.inr ⟨jx, jy⟩)) : P k :=
  by
  rw [← to_left_moves_mul.apply_symm_apply k]
  rcases to_left_moves_mul.symm k with (⟨ix, iy⟩ | ⟨jx, jy⟩)
  · apply hl
  · apply hr
#align pgame.left_moves_mul_cases SetTheory.PGame.leftMoves_mul_cases
-/

#print SetTheory.PGame.rightMoves_mul_cases /-
theorem SetTheory.PGame.rightMoves_mul_cases {x y : SetTheory.PGame} (k)
    {P : (x * y).RightMoves → Prop}
    (hl : ∀ ix jy, P <| SetTheory.PGame.toRightMovesMul (Sum.inl ⟨ix, jy⟩))
    (hr : ∀ jx iy, P <| SetTheory.PGame.toRightMovesMul (Sum.inr ⟨jx, iy⟩)) : P k :=
  by
  rw [← to_right_moves_mul.apply_symm_apply k]
  rcases to_right_moves_mul.symm k with (⟨ix, iy⟩ | ⟨jx, jy⟩)
  · apply hl
  · apply hr
#align pgame.right_moves_mul_cases SetTheory.PGame.rightMoves_mul_cases
-/

#print SetTheory.PGame.mulCommRelabelling /-
/-- `x * y` and `y * x` have the same moves. -/
def SetTheory.PGame.mulCommRelabelling : ∀ x y : SetTheory.PGame.{u}, x * y ≡r y * x
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩ => by
    refine'
            ⟨Equiv.sumCongr (Equiv.prodComm _ _) (Equiv.prodComm _ _),
              (Equiv.sumComm _ _).trans (Equiv.sumCongr (Equiv.prodComm _ _) (Equiv.prodComm _ _)),
              _, _⟩ <;>
          rintro (⟨i, j⟩ | ⟨i, j⟩) <;>
        dsimp <;>
      exact
        ((add_comm_relabelling _ _).trans <|
              (mul_comm_relabelling _ _).addCongr (mul_comm_relabelling _ _)).subCongr
          (mul_comm_relabelling _ _)
decreasing_by pgame_wf_tac
#align pgame.mul_comm_relabelling SetTheory.PGame.mulCommRelabelling
-/

#print SetTheory.PGame.quot_mul_comm /-
theorem SetTheory.PGame.quot_mul_comm (x y : SetTheory.PGame.{u}) : ⟦x * y⟧ = ⟦y * x⟧ :=
  Quot.sound (SetTheory.PGame.mulCommRelabelling x y).Equiv
#align pgame.quot_mul_comm SetTheory.PGame.quot_mul_comm
-/

#print SetTheory.PGame.mul_comm_equiv /-
/-- `x * y` is equivalent to `y * x`. -/
theorem SetTheory.PGame.mul_comm_equiv (x y : SetTheory.PGame) : x * y ≈ y * x :=
  Quotient.exact <| SetTheory.PGame.quot_mul_comm _ _
#align pgame.mul_comm_equiv SetTheory.PGame.mul_comm_equiv
-/

#print SetTheory.PGame.isEmpty_mul_zero_leftMoves /-
instance SetTheory.PGame.isEmpty_mul_zero_leftMoves (x : SetTheory.PGame.{u}) :
    IsEmpty (x * 0).LeftMoves := by cases x; apply Sum.isEmpty
#align pgame.is_empty_mul_zero_left_moves SetTheory.PGame.isEmpty_mul_zero_leftMoves
-/

#print SetTheory.PGame.isEmpty_mul_zero_rightMoves /-
instance SetTheory.PGame.isEmpty_mul_zero_rightMoves (x : SetTheory.PGame.{u}) :
    IsEmpty (x * 0).RightMoves := by cases x; apply Sum.isEmpty
#align pgame.is_empty_mul_zero_right_moves SetTheory.PGame.isEmpty_mul_zero_rightMoves
-/

#print SetTheory.PGame.isEmpty_zero_mul_leftMoves /-
instance SetTheory.PGame.isEmpty_zero_mul_leftMoves (x : SetTheory.PGame.{u}) :
    IsEmpty (0 * x).LeftMoves := by cases x; apply Sum.isEmpty
#align pgame.is_empty_zero_mul_left_moves SetTheory.PGame.isEmpty_zero_mul_leftMoves
-/

#print SetTheory.PGame.isEmpty_zero_mul_rightMoves /-
instance SetTheory.PGame.isEmpty_zero_mul_rightMoves (x : SetTheory.PGame.{u}) :
    IsEmpty (0 * x).RightMoves := by cases x; apply Sum.isEmpty
#align pgame.is_empty_zero_mul_right_moves SetTheory.PGame.isEmpty_zero_mul_rightMoves
-/

#print SetTheory.PGame.mulZeroRelabelling /-
/-- `x * 0` has exactly the same moves as `0`. -/
def SetTheory.PGame.mulZeroRelabelling (x : SetTheory.PGame) : x * 0 ≡r 0 :=
  SetTheory.PGame.Relabelling.isEmpty _
#align pgame.mul_zero_relabelling SetTheory.PGame.mulZeroRelabelling
-/

#print SetTheory.PGame.mul_zero_equiv /-
/-- `x * 0` is equivalent to `0`. -/
theorem SetTheory.PGame.mul_zero_equiv (x : SetTheory.PGame) : x * 0 ≈ 0 :=
  (SetTheory.PGame.mulZeroRelabelling x).Equiv
#align pgame.mul_zero_equiv SetTheory.PGame.mul_zero_equiv
-/

#print SetTheory.PGame.quot_mul_zero /-
@[simp]
theorem SetTheory.PGame.quot_mul_zero (x : SetTheory.PGame) : ⟦x * 0⟧ = ⟦0⟧ :=
  @Quotient.sound _ _ (x * 0) _ x.mul_zero_equiv
#align pgame.quot_mul_zero SetTheory.PGame.quot_mul_zero
-/

#print SetTheory.PGame.zeroMulRelabelling /-
/-- `0 * x` has exactly the same moves as `0`. -/
def SetTheory.PGame.zeroMulRelabelling (x : SetTheory.PGame) : 0 * x ≡r 0 :=
  SetTheory.PGame.Relabelling.isEmpty _
#align pgame.zero_mul_relabelling SetTheory.PGame.zeroMulRelabelling
-/

#print SetTheory.PGame.zero_mul_equiv /-
/-- `0 * x` is equivalent to `0`. -/
theorem SetTheory.PGame.zero_mul_equiv (x : SetTheory.PGame) : 0 * x ≈ 0 :=
  (SetTheory.PGame.zeroMulRelabelling x).Equiv
#align pgame.zero_mul_equiv SetTheory.PGame.zero_mul_equiv
-/

#print SetTheory.PGame.quot_zero_mul /-
@[simp]
theorem SetTheory.PGame.quot_zero_mul (x : SetTheory.PGame) : ⟦0 * x⟧ = ⟦0⟧ :=
  @Quotient.sound _ _ (0 * x) _ x.zero_mul_equiv
#align pgame.quot_zero_mul SetTheory.PGame.quot_zero_mul
-/

#print SetTheory.PGame.negMulRelabelling /-
/-- `-x * y` and `-(x * y)` have the same moves. -/
def SetTheory.PGame.negMulRelabelling : ∀ x y : SetTheory.PGame.{u}, -x * y ≡r -(x * y)
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩ => by
    refine' ⟨Equiv.sumComm _ _, Equiv.sumComm _ _, _, _⟩ <;> rintro (⟨i, j⟩ | ⟨i, j⟩) <;> dsimp <;>
          apply ((neg_add_relabelling _ _).trans _).symm <;>
        apply ((neg_add_relabelling _ _).trans (relabelling.add_congr _ _)).subCongr <;>
      exact (neg_mul_relabelling _ _).symm
decreasing_by pgame_wf_tac
#align pgame.neg_mul_relabelling SetTheory.PGame.negMulRelabelling
-/

#print SetTheory.PGame.quot_neg_mul /-
@[simp]
theorem SetTheory.PGame.quot_neg_mul (x y : SetTheory.PGame) : ⟦-x * y⟧ = -⟦x * y⟧ :=
  Quot.sound (SetTheory.PGame.negMulRelabelling x y).Equiv
#align pgame.quot_neg_mul SetTheory.PGame.quot_neg_mul
-/

#print SetTheory.PGame.mulNegRelabelling /-
/-- `x * -y` and `-(x * y)` have the same moves. -/
def SetTheory.PGame.mulNegRelabelling (x y : SetTheory.PGame) : x * -y ≡r -(x * y) :=
  (SetTheory.PGame.mulCommRelabelling x _).trans <|
    (SetTheory.PGame.negMulRelabelling _ x).trans (SetTheory.PGame.mulCommRelabelling y x).negCongr
#align pgame.mul_neg_relabelling SetTheory.PGame.mulNegRelabelling
-/

#print SetTheory.PGame.quot_mul_neg /-
@[simp]
theorem SetTheory.PGame.quot_mul_neg (x y : SetTheory.PGame) : ⟦x * -y⟧ = -⟦x * y⟧ :=
  Quot.sound (SetTheory.PGame.mulNegRelabelling x y).Equiv
#align pgame.quot_mul_neg SetTheory.PGame.quot_mul_neg
-/

#print SetTheory.PGame.quot_left_distrib /-
@[simp]
theorem SetTheory.PGame.quot_left_distrib :
    ∀ x y z : SetTheory.PGame, ⟦x * (y + z)⟧ = ⟦x * y⟧ + ⟦x * z⟧
  | mk xl xr xL xR, mk yl yr yL yR, mk zl zr zL zR =>
    by
    let x := mk xl xr xL xR
    let y := mk yl yr yL yR
    let z := mk zl zr zL zR
    refine' quot_eq_of_mk_quot_eq _ _ _ _
    · fconstructor
      ·
        rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩) <;>
          solve_by_elim (config := { max_depth := 5 }) [Sum.inl, Sum.inr, Prod.mk]
      ·
        rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;>
          solve_by_elim (config := { max_depth := 5 }) [Sum.inl, Sum.inr, Prod.mk]
      · rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩) <;> rfl
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;> rfl
    · fconstructor
      ·
        rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩) <;>
          solve_by_elim (config := { max_depth := 5 }) [Sum.inl, Sum.inr, Prod.mk]
      ·
        rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;>
          solve_by_elim (config := { max_depth := 5 }) [Sum.inl, Sum.inr, Prod.mk]
      · rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩) <;> rfl
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;> rfl
    · rintro (⟨i, j | k⟩ | ⟨i, j | k⟩)
      · change
          ⟦xL i * (y + z) + x * (yL j + z) - xL i * (yL j + z)⟧ =
            ⟦xL i * y + x * yL j - xL i * yL j + x * z⟧
        simp [quot_left_distrib]; abel
      · change
          ⟦xL i * (y + z) + x * (y + zL k) - xL i * (y + zL k)⟧ =
            ⟦x * y + (xL i * z + x * zL k - xL i * zL k)⟧
        simp [quot_left_distrib]; abel
      · change
          ⟦xR i * (y + z) + x * (yR j + z) - xR i * (yR j + z)⟧ =
            ⟦xR i * y + x * yR j - xR i * yR j + x * z⟧
        simp [quot_left_distrib]; abel
      · change
          ⟦xR i * (y + z) + x * (y + zR k) - xR i * (y + zR k)⟧ =
            ⟦x * y + (xR i * z + x * zR k - xR i * zR k)⟧
        simp [quot_left_distrib]; abel
    · rintro (⟨i, j | k⟩ | ⟨i, j | k⟩)
      · change
          ⟦xL i * (y + z) + x * (yR j + z) - xL i * (yR j + z)⟧ =
            ⟦xL i * y + x * yR j - xL i * yR j + x * z⟧
        simp [quot_left_distrib]; abel
      · change
          ⟦xL i * (y + z) + x * (y + zR k) - xL i * (y + zR k)⟧ =
            ⟦x * y + (xL i * z + x * zR k - xL i * zR k)⟧
        simp [quot_left_distrib]; abel
      · change
          ⟦xR i * (y + z) + x * (yL j + z) - xR i * (yL j + z)⟧ =
            ⟦xR i * y + x * yL j - xR i * yL j + x * z⟧
        simp [quot_left_distrib]; abel
      · change
          ⟦xR i * (y + z) + x * (y + zL k) - xR i * (y + zL k)⟧ =
            ⟦x * y + (xR i * z + x * zL k - xR i * zL k)⟧
        simp [quot_left_distrib]; abel
decreasing_by pgame_wf_tac
#align pgame.quot_left_distrib SetTheory.PGame.quot_left_distrib
-/

#print SetTheory.PGame.left_distrib_equiv /-
/-- `x * (y + z)` is equivalent to `x * y + x * z.`-/
theorem SetTheory.PGame.left_distrib_equiv (x y z : SetTheory.PGame) :
    x * (y + z) ≈ x * y + x * z :=
  Quotient.exact <| SetTheory.PGame.quot_left_distrib _ _ _
#align pgame.left_distrib_equiv SetTheory.PGame.left_distrib_equiv
-/

#print SetTheory.PGame.quot_left_distrib_sub /-
@[simp]
theorem SetTheory.PGame.quot_left_distrib_sub (x y z : SetTheory.PGame) :
    ⟦x * (y - z)⟧ = ⟦x * y⟧ - ⟦x * z⟧ := by change ⟦x * (y + -z)⟧ = ⟦x * y⟧ + -⟦x * z⟧;
  rw [quot_left_distrib, quot_mul_neg]
#align pgame.quot_left_distrib_sub SetTheory.PGame.quot_left_distrib_sub
-/

#print SetTheory.PGame.quot_right_distrib /-
@[simp]
theorem SetTheory.PGame.quot_right_distrib (x y z : SetTheory.PGame) :
    ⟦(x + y) * z⟧ = ⟦x * z⟧ + ⟦y * z⟧ := by simp only [quot_mul_comm, quot_left_distrib]
#align pgame.quot_right_distrib SetTheory.PGame.quot_right_distrib
-/

#print SetTheory.PGame.right_distrib_equiv /-
/-- `(x + y) * z` is equivalent to `x * z + y * z.`-/
theorem SetTheory.PGame.right_distrib_equiv (x y z : SetTheory.PGame) :
    (x + y) * z ≈ x * z + y * z :=
  Quotient.exact <| SetTheory.PGame.quot_right_distrib _ _ _
#align pgame.right_distrib_equiv SetTheory.PGame.right_distrib_equiv
-/

#print SetTheory.PGame.quot_right_distrib_sub /-
@[simp]
theorem SetTheory.PGame.quot_right_distrib_sub (x y z : SetTheory.PGame) :
    ⟦(y - z) * x⟧ = ⟦y * x⟧ - ⟦z * x⟧ := by change ⟦(y + -z) * x⟧ = ⟦y * x⟧ + -⟦z * x⟧;
  rw [quot_right_distrib, quot_neg_mul]
#align pgame.quot_right_distrib_sub SetTheory.PGame.quot_right_distrib_sub
-/

#print SetTheory.PGame.mulOneRelabelling /-
/-- `x * 1` has the same moves as `x`. -/
def SetTheory.PGame.mulOneRelabelling : ∀ x : SetTheory.PGame.{u}, x * 1 ≡r x
  | ⟨xl, xr, xL, xR⟩ => by
    unfold One.one
    refine'
                  ⟨(Equiv.sumEmpty _ _).trans (Equiv.prodPUnit _),
                    (Equiv.emptySum _ _).trans (Equiv.prodPUnit _), _, _⟩ <;>
                try rintro (⟨i, ⟨⟩⟩ | ⟨i, ⟨⟩⟩) <;>
              try intro i <;>
            dsimp <;>
          apply (relabelling.sub_congr (relabelling.refl _) (mul_zero_relabelling _)).trans <;>
        rw [sub_zero] <;>
      exact
        (add_zero_relabelling _).trans
          (((mul_one_relabelling _).addCongr (mul_zero_relabelling _)).trans <|
            add_zero_relabelling _)
#align pgame.mul_one_relabelling SetTheory.PGame.mulOneRelabelling
-/

#print SetTheory.PGame.quot_mul_one /-
@[simp]
theorem SetTheory.PGame.quot_mul_one (x : SetTheory.PGame) : ⟦x * 1⟧ = ⟦x⟧ :=
  Quot.sound <| SetTheory.PGame.mulOneRelabelling x
#align pgame.quot_mul_one SetTheory.PGame.quot_mul_one
-/

#print SetTheory.PGame.mul_one_equiv /-
/-- `x * 1` is equivalent to `x`. -/
theorem SetTheory.PGame.mul_one_equiv (x : SetTheory.PGame) : x * 1 ≈ x :=
  Quotient.exact <| SetTheory.PGame.quot_mul_one x
#align pgame.mul_one_equiv SetTheory.PGame.mul_one_equiv
-/

#print SetTheory.PGame.oneMulRelabelling /-
/-- `1 * x` has the same moves as `x`. -/
def SetTheory.PGame.oneMulRelabelling (x : SetTheory.PGame) : 1 * x ≡r x :=
  (SetTheory.PGame.mulCommRelabelling 1 x).trans <| SetTheory.PGame.mulOneRelabelling x
#align pgame.one_mul_relabelling SetTheory.PGame.oneMulRelabelling
-/

#print SetTheory.PGame.quot_one_mul /-
@[simp]
theorem SetTheory.PGame.quot_one_mul (x : SetTheory.PGame) : ⟦1 * x⟧ = ⟦x⟧ :=
  Quot.sound <| SetTheory.PGame.oneMulRelabelling x
#align pgame.quot_one_mul SetTheory.PGame.quot_one_mul
-/

#print SetTheory.PGame.one_mul_equiv /-
/-- `1 * x` is equivalent to `x`. -/
theorem SetTheory.PGame.one_mul_equiv (x : SetTheory.PGame) : 1 * x ≈ x :=
  Quotient.exact <| SetTheory.PGame.quot_one_mul x
#align pgame.one_mul_equiv SetTheory.PGame.one_mul_equiv
-/

#print SetTheory.PGame.quot_mul_assoc /-
theorem SetTheory.PGame.quot_mul_assoc : ∀ x y z : SetTheory.PGame, ⟦x * y * z⟧ = ⟦x * (y * z)⟧
  | mk xl xr xL xR, mk yl yr yL yR, mk zl zr zL zR =>
    by
    let x := mk xl xr xL xR
    let y := mk yl yr yL yR
    let z := mk zl zr zL zR
    refine' quot_eq_of_mk_quot_eq _ _ _ _
    · fconstructor
      ·
        rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩) <;>
          solve_by_elim (config := { max_depth := 7 }) [Sum.inl, Sum.inr, Prod.mk]
      ·
        rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩) <;>
          solve_by_elim (config := { max_depth := 7 }) [Sum.inl, Sum.inr, Prod.mk]
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩) <;> rfl
      · rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩) <;> rfl
    · fconstructor
      ·
        rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩) <;>
          solve_by_elim (config := { max_depth := 7 }) [Sum.inl, Sum.inr, Prod.mk]
      ·
        rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩) <;>
          solve_by_elim (config := { max_depth := 7 }) [Sum.inl, Sum.inr, Prod.mk]
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩) <;> rfl
      · rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩) <;> rfl
    · rintro (⟨⟨i, j⟩ | ⟨i, j⟩, k⟩ | ⟨⟨i, j⟩ | ⟨i, j⟩, k⟩)
      · change
          ⟦(xL i * y + x * yL j - xL i * yL j) * z + x * y * zL k -
                (xL i * y + x * yL j - xL i * yL j) * zL k⟧ =
            ⟦xL i * (y * z) + x * (yL j * z + y * zL k - yL j * zL k) -
                xL i * (yL j * z + y * zL k - yL j * zL k)⟧
        simp [quot_mul_assoc]; abel
      · change
          ⟦(xR i * y + x * yR j - xR i * yR j) * z + x * y * zL k -
                (xR i * y + x * yR j - xR i * yR j) * zL k⟧ =
            ⟦xR i * (y * z) + x * (yR j * z + y * zL k - yR j * zL k) -
                xR i * (yR j * z + y * zL k - yR j * zL k)⟧
        simp [quot_mul_assoc]; abel
      · change
          ⟦(xL i * y + x * yR j - xL i * yR j) * z + x * y * zR k -
                (xL i * y + x * yR j - xL i * yR j) * zR k⟧ =
            ⟦xL i * (y * z) + x * (yR j * z + y * zR k - yR j * zR k) -
                xL i * (yR j * z + y * zR k - yR j * zR k)⟧
        simp [quot_mul_assoc]; abel
      · change
          ⟦(xR i * y + x * yL j - xR i * yL j) * z + x * y * zR k -
                (xR i * y + x * yL j - xR i * yL j) * zR k⟧ =
            ⟦xR i * (y * z) + x * (yL j * z + y * zR k - yL j * zR k) -
                xR i * (yL j * z + y * zR k - yL j * zR k)⟧
        simp [quot_mul_assoc]; abel
    · rintro (⟨⟨i, j⟩ | ⟨i, j⟩, k⟩ | ⟨⟨i, j⟩ | ⟨i, j⟩, k⟩)
      · change
          ⟦(xL i * y + x * yL j - xL i * yL j) * z + x * y * zR k -
                (xL i * y + x * yL j - xL i * yL j) * zR k⟧ =
            ⟦xL i * (y * z) + x * (yL j * z + y * zR k - yL j * zR k) -
                xL i * (yL j * z + y * zR k - yL j * zR k)⟧
        simp [quot_mul_assoc]; abel
      · change
          ⟦(xR i * y + x * yR j - xR i * yR j) * z + x * y * zR k -
                (xR i * y + x * yR j - xR i * yR j) * zR k⟧ =
            ⟦xR i * (y * z) + x * (yR j * z + y * zR k - yR j * zR k) -
                xR i * (yR j * z + y * zR k - yR j * zR k)⟧
        simp [quot_mul_assoc]; abel
      · change
          ⟦(xL i * y + x * yR j - xL i * yR j) * z + x * y * zL k -
                (xL i * y + x * yR j - xL i * yR j) * zL k⟧ =
            ⟦xL i * (y * z) + x * (yR j * z + y * zL k - yR j * zL k) -
                xL i * (yR j * z + y * zL k - yR j * zL k)⟧
        simp [quot_mul_assoc]; abel
      · change
          ⟦(xR i * y + x * yL j - xR i * yL j) * z + x * y * zL k -
                (xR i * y + x * yL j - xR i * yL j) * zL k⟧ =
            ⟦xR i * (y * z) + x * (yL j * z + y * zL k - yL j * zL k) -
                xR i * (yL j * z + y * zL k - yL j * zL k)⟧
        simp [quot_mul_assoc]; abel
decreasing_by pgame_wf_tac
#align pgame.quot_mul_assoc SetTheory.PGame.quot_mul_assoc
-/

#print SetTheory.PGame.mul_assoc_equiv /-
/-- `x * y * z` is equivalent to `x * (y * z).`-/
theorem SetTheory.PGame.mul_assoc_equiv (x y z : SetTheory.PGame) : x * y * z ≈ x * (y * z) :=
  Quotient.exact <| SetTheory.PGame.quot_mul_assoc _ _ _
#align pgame.mul_assoc_equiv SetTheory.PGame.mul_assoc_equiv
-/

#print SetTheory.PGame.InvTy /-
/-- Because the two halves of the definition of `inv` produce more elements
on each side, we have to define the two families inductively.
This is the indexing set for the function, and `inv_val` is the function part. -/
inductive SetTheory.PGame.InvTy (l r : Type u) : Bool → Type u
  | zero : inv_ty false
  | left₁ : r → inv_ty false → inv_ty false
  | left₂ : l → inv_ty true → inv_ty false
  | right₁ : l → inv_ty false → inv_ty true
  | right₂ : r → inv_ty true → inv_ty true
#align pgame.inv_ty SetTheory.PGame.InvTy
-/

instance (l r : Type u) [IsEmpty l] [IsEmpty r] : IsEmpty (SetTheory.PGame.InvTy l r true) :=
  ⟨by rintro (_ | _ | _ | a | a) <;> exact isEmptyElim a⟩

instance (l r : Type u) : Inhabited (SetTheory.PGame.InvTy l r false) :=
  ⟨SetTheory.PGame.InvTy.zero⟩

#print SetTheory.PGame.uniqueInvTy /-
instance SetTheory.PGame.uniqueInvTy (l r : Type u) [IsEmpty l] [IsEmpty r] :
    Unique (SetTheory.PGame.InvTy l r false) :=
  { SetTheory.PGame.InvTy.inhabited l r with
    uniq := by rintro (a | a | a); rfl; all_goals exact isEmptyElim a }
#align pgame.unique_inv_ty SetTheory.PGame.uniqueInvTy
-/

#print SetTheory.PGame.invVal /-
/-- Because the two halves of the definition of `inv` produce more elements
of each side, we have to define the two families inductively.
This is the function part, defined by recursion on `inv_ty`. -/
def SetTheory.PGame.invVal {l r} (L : l → SetTheory.PGame) (R : r → SetTheory.PGame)
    (IHl : l → SetTheory.PGame) (IHr : r → SetTheory.PGame) :
    ∀ {b}, SetTheory.PGame.InvTy l r b → SetTheory.PGame
  | _, inv_ty.zero => 0
  | _, inv_ty.left₁ i j => (1 + (R i - SetTheory.PGame.mk l r L R) * inv_val j) * IHr i
  | _, inv_ty.left₂ i j => (1 + (L i - SetTheory.PGame.mk l r L R) * inv_val j) * IHl i
  | _, inv_ty.right₁ i j => (1 + (L i - SetTheory.PGame.mk l r L R) * inv_val j) * IHl i
  | _, inv_ty.right₂ i j => (1 + (R i - SetTheory.PGame.mk l r L R) * inv_val j) * IHr i
#align pgame.inv_val SetTheory.PGame.invVal
-/

#print SetTheory.PGame.invVal_isEmpty /-
@[simp]
theorem SetTheory.PGame.invVal_isEmpty {l r : Type u} {b} (L R IHl IHr)
    (i : SetTheory.PGame.InvTy l r b) [IsEmpty l] [IsEmpty r] :
    SetTheory.PGame.invVal L R IHl IHr i = 0 :=
  by
  cases' i with a _ a _ a _ a
  · rfl
  all_goals exact isEmptyElim a
#align pgame.inv_val_is_empty SetTheory.PGame.invVal_isEmpty
-/

#print SetTheory.PGame.inv' /-
/-- The inverse of a positive surreal number `x = {L | R}` is
given by `x⁻¹ = {0,
  (1 + (R - x) * x⁻¹L) * R, (1 + (L - x) * x⁻¹R) * L |
  (1 + (L - x) * x⁻¹L) * L, (1 + (R - x) * x⁻¹R) * R}`.
Because the two halves `x⁻¹L, x⁻¹R` of `x⁻¹` are used in their own
definition, the sets and elements are inductively generated. -/
def SetTheory.PGame.inv' : SetTheory.PGame → SetTheory.PGame
  | ⟨l, r, L, R⟩ =>
    let l' := { i // 0 < L i }
    let L' : l' → SetTheory.PGame := fun i => L i.1
    let IHl' : l' → SetTheory.PGame := fun i => inv' (L i.1)
    let IHr i := inv' (R i)
    ⟨SetTheory.PGame.InvTy l' r false, SetTheory.PGame.InvTy l' r true,
      SetTheory.PGame.invVal L' R IHl' IHr, SetTheory.PGame.invVal L' R IHl' IHr⟩
#align pgame.inv' SetTheory.PGame.inv'
-/

#print SetTheory.PGame.zero_lf_inv' /-
theorem SetTheory.PGame.zero_lf_inv' : ∀ x : SetTheory.PGame, 0 ⧏ SetTheory.PGame.inv' x
  | ⟨xl, xr, xL, xR⟩ => by convert lf_mk _ _ inv_ty.zero; rfl
#align pgame.zero_lf_inv' SetTheory.PGame.zero_lf_inv'
-/

#print SetTheory.PGame.inv'Zero /-
/-- `inv' 0` has exactly the same moves as `1`. -/
def SetTheory.PGame.inv'Zero : SetTheory.PGame.inv' 0 ≡r 1 :=
  by
  change mk _ _ _ _ ≡r 1
  refine' ⟨_, _, fun i => _, IsEmpty.elim _⟩
  · apply Equiv.equivPUnit (inv_ty _ _ _)
    infer_instance
  · apply Equiv.equivPEmpty (inv_ty _ _ _)
    infer_instance
  · simp
  · dsimp
    infer_instance
#align pgame.inv'_zero SetTheory.PGame.inv'Zero
-/

#print SetTheory.PGame.inv'_zero_equiv /-
theorem SetTheory.PGame.inv'_zero_equiv : SetTheory.PGame.inv' 0 ≈ 1 :=
  SetTheory.PGame.inv'Zero.Equiv
#align pgame.inv'_zero_equiv SetTheory.PGame.inv'_zero_equiv
-/

#print SetTheory.PGame.inv'One /-
/-- `inv' 1` has exactly the same moves as `1`. -/
def SetTheory.PGame.inv'One : SetTheory.PGame.inv' 1 ≡r (1 : SetTheory.PGame.{u}) :=
  by
  change relabelling (mk _ _ _ _) 1
  have : IsEmpty { i : PUnit.{u + 1} // (0 : SetTheory.PGame.{u}) < 0 } := by
    rw [lt_self_iff_false]; infer_instance
  refine' ⟨_, _, fun i => _, IsEmpty.elim _⟩ <;> dsimp
  · apply Equiv.equivPUnit
  · apply Equiv.equivOfIsEmpty
  · simp
  · infer_instance
#align pgame.inv'_one SetTheory.PGame.inv'One
-/

#print SetTheory.PGame.inv'_one_equiv /-
theorem SetTheory.PGame.inv'_one_equiv : SetTheory.PGame.inv' 1 ≈ 1 :=
  SetTheory.PGame.inv'One.Equiv
#align pgame.inv'_one_equiv SetTheory.PGame.inv'_one_equiv
-/

/-- The inverse of a pre-game in terms of the inverse on positive pre-games. -/
noncomputable instance : Inv SetTheory.PGame :=
  ⟨by classical exact fun x => if x ≈ 0 then 0 else if 0 < x then inv' x else -inv' (-x)⟩

noncomputable instance : Div SetTheory.PGame :=
  ⟨fun x y => x * y⁻¹⟩

#print SetTheory.PGame.inv_eq_of_equiv_zero /-
theorem SetTheory.PGame.inv_eq_of_equiv_zero {x : SetTheory.PGame} (h : x ≈ 0) : x⁻¹ = 0 := by
  classical exact if_pos h
#align pgame.inv_eq_of_equiv_zero SetTheory.PGame.inv_eq_of_equiv_zero
-/

#print SetTheory.PGame.inv_zero /-
@[simp]
theorem SetTheory.PGame.inv_zero : (0 : SetTheory.PGame)⁻¹ = 0 :=
  SetTheory.PGame.inv_eq_of_equiv_zero (SetTheory.PGame.equiv_refl _)
#align pgame.inv_zero SetTheory.PGame.inv_zero
-/

#print SetTheory.PGame.inv_eq_of_pos /-
theorem SetTheory.PGame.inv_eq_of_pos {x : SetTheory.PGame} (h : 0 < x) :
    x⁻¹ = SetTheory.PGame.inv' x := by classical exact (if_neg h.lf.not_equiv').trans (if_pos h)
#align pgame.inv_eq_of_pos SetTheory.PGame.inv_eq_of_pos
-/

#print SetTheory.PGame.inv_eq_of_lf_zero /-
theorem SetTheory.PGame.inv_eq_of_lf_zero {x : SetTheory.PGame} (h : x ⧏ 0) :
    x⁻¹ = -SetTheory.PGame.inv' (-x) := by
  classical exact (if_neg h.not_equiv).trans (if_neg h.not_gt)
#align pgame.inv_eq_of_lf_zero SetTheory.PGame.inv_eq_of_lf_zero
-/

#print SetTheory.PGame.invOne /-
/-- `1⁻¹` has exactly the same moves as `1`. -/
def SetTheory.PGame.invOne : 1⁻¹ ≡r 1 := by rw [inv_eq_of_pos SetTheory.PGame.zero_lt_one];
  exact inv'_one
#align pgame.inv_one SetTheory.PGame.invOne
-/

#print SetTheory.PGame.inv_one_equiv /-
theorem SetTheory.PGame.inv_one_equiv : 1⁻¹ ≈ 1 :=
  SetTheory.PGame.invOne.Equiv
#align pgame.inv_one_equiv SetTheory.PGame.inv_one_equiv
-/

end SetTheory.PGame

