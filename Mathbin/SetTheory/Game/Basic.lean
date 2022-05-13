/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Isabel Longbottom, Scott Morrison, Apurva Nakade
-/
import Mathbin.SetTheory.Game.Pgame
import Mathbin.Tactic.Abel

/-!
# Combinatorial games.

In this file we define the quotient of pre-games by the equivalence relation `p ≈ q ↔ p ≤ q ∧ q ≤
p`, and construct an instance `add_comm_group game`, as well as an instance `partial_order game`
(although note carefully the warning that the `<` field in this instance is not the usual relation
on combinatorial games).

## Multiplication on pre-games

We define the operations of multiplication and inverse on pre-games, and prove a few basic theorems
about them. Multiplication is not well-behaved under equivalence of pre-games i.e. `x.equiv y` does
not imply `(x*z).equiv (y*z)`. Hence, multiplication is not a well-defined operation on games.
Nevertheless, the abelian group structure on games allows us to simplify many proofs for pre-games.
-/


open Function

universe u

-- mathport name: «expr ≈ »
local infixl:0 " ≈ " => Pgame.Equiv

instance Pgame.setoid : Setoidₓ Pgame :=
  ⟨fun x y => x ≈ y, fun x => Pgame.equiv_refl _, fun x y => Pgame.equiv_symm, fun x y z => Pgame.equiv_trans⟩

/-- The type of combinatorial games. In ZFC, a combinatorial game is constructed from
  two sets of combinatorial games that have been constructed at an earlier
  stage. To do this in type theory, we say that a combinatorial pre-game is built
  inductively from two families of combinatorial games indexed over any type
  in Type u. The resulting type `pgame.{u}` lives in `Type (u+1)`,
  reflecting that it is a proper class in ZFC.
  A combinatorial game is then constructed by quotienting by the equivalence
  `x ≈ y ↔ x ≤ y ∧ y ≤ x`. -/
abbrev Game :=
  Quotientₓ Pgame.setoid

open Pgame

namespace Game

instance : LE Game :=
  ⟨Quotientₓ.lift₂ (fun x y => x ≤ y) fun x₁ y₁ x₂ y₂ hx hy => propext (le_congr hx hy)⟩

-- Adding `@[refl]` and `@[trans]` attributes here would override the ones on
-- `preorder.le_refl` and `preorder.le_trans`, which breaks all non-`game` uses of `≤`!
theorem le_rfl : ∀ {x : Game}, x ≤ x := by
  rintro ⟨x⟩
  exact Pgame.le_rfl

theorem le_refl (x : Game) : x ≤ x :=
  le_rfl

theorem le_trans : ∀ x y z : Game, x ≤ y → y ≤ z → x ≤ z := by
  rintro ⟨x⟩ ⟨y⟩ ⟨z⟩
  apply Pgame.le_trans

theorem le_antisymm : ∀ x y : Game, x ≤ y → y ≤ x → x = y := by
  rintro ⟨x⟩ ⟨y⟩ h₁ h₂
  apply Quot.sound
  exact ⟨h₁, h₂⟩

/-- This instance is incompatible with that provided by `game.partial_order`, which is why it's made
into a `def` instead. -/
instance : LT Game :=
  ⟨Quotientₓ.lift₂ (fun x y => x < y) fun x₁ y₁ x₂ y₂ hx hy => propext (lt_congr hx hy)⟩

theorem lt_or_eq_of_le : ∀ {x y : Game}, x ≤ y → x < y ∨ x = y := by
  rintro ⟨x⟩ ⟨y⟩
  change _ → _ ∨ ⟦x⟧ = ⟦y⟧
  rw [Quotientₓ.eq]
  exact lt_or_equiv_of_le

instance : IsTrichotomous Game (· < ·) :=
  ⟨by
    rintro ⟨x⟩ ⟨y⟩
    change _ ∨ ⟦x⟧ = ⟦y⟧ ∨ _
    rw [Quotientₓ.eq]
    apply lt_or_equiv_or_gt⟩

@[simp]
theorem not_le : ∀ {x y : Game}, ¬x ≤ y ↔ y < x := by
  rintro ⟨x⟩ ⟨y⟩
  exact not_leₓ

@[simp]
theorem not_lt : ∀ {x y : Game}, ¬x < y ↔ y ≤ x := by
  rintro ⟨x⟩ ⟨y⟩
  exact not_ltₓ

instance : Zero Game :=
  ⟨⟦0⟧⟩

instance : Inhabited Game :=
  ⟨0⟩

instance : One Game :=
  ⟨⟦1⟧⟩

/-- The negation of `{L | R}` is `{-R | -L}`. -/
instance : Neg Game :=
  ⟨Quot.lift (fun x => ⟦-x⟧) fun x y h => Quot.sound (@neg_congr x y h)⟩

/-- The sum of `x = {xL | xR}` and `y = {yL | yR}` is `{xL + y, x + yL | xR + y, x + yR}`. -/
instance : Add Game :=
  ⟨Quotientₓ.lift₂ (fun x y : Pgame => ⟦x + y⟧) fun x₁ y₁ x₂ y₂ hx hy => Quot.sound (Pgame.add_congr hx hy)⟩

instance : AddSemigroupₓ Game.{u} :=
  { Game.hasAdd with
    add_assoc := by
      rintro ⟨x⟩ ⟨y⟩ ⟨z⟩
      exact Quot.sound add_assoc_equiv }

instance : AddMonoidₓ Game :=
  { Game.hasZero, Game.addSemigroup with
    add_zero := by
      rintro ⟨x⟩
      exact Quot.sound (add_zero_equiv x),
    zero_add := by
      rintro ⟨x⟩
      exact Quot.sound (zero_add_equiv x) }

instance : AddGroupₓ Game :=
  { Game.hasNeg, Game.addMonoid with
    add_left_neg := by
      rintro ⟨x⟩
      exact Quot.sound (add_left_neg_equiv x) }

instance : AddCommSemigroupₓ Game :=
  { Game.addSemigroup with
    add_comm := by
      rintro ⟨x⟩ ⟨y⟩
      exact Quot.sound add_comm_equiv }

instance : AddCommGroupₓ Game :=
  { Game.addCommSemigroup, Game.addGroup with }

instance covariant_class_add_le : CovariantClass Game Game (· + ·) (· ≤ ·) :=
  ⟨by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h
    exact @add_le_add_left _ _ _ _ b c h a⟩

instance covariant_class_swap_add_le : CovariantClass Game Game (swap (· + ·)) (· ≤ ·) :=
  ⟨by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h
    exact @add_le_add_right _ _ _ _ b c h a⟩

instance covariant_class_add_lt : CovariantClass Game Game (· + ·) (· < ·) :=
  ⟨by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h
    exact @add_lt_add_left _ _ _ _ b c h a⟩

instance covariant_class_swap_add_lt : CovariantClass Game Game (swap (· + ·)) (· < ·) :=
  ⟨by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h
    exact @add_lt_add_right _ _ _ _ b c h a⟩

/-- The `<` operation provided by this partial order is not the usual `<` on games! -/
-- While it is very tempting to define a `partial_order` on games, and prove
-- that games form an `ordered_add_comm_group`, it is a bit dangerous.
-- The relations `≤` and `<` on games do not satisfy
-- `lt_iff_le_not_le : ∀ a b : α, a < b ↔ (a ≤ b ∧ ¬ b ≤ a)`
-- (Consider `a = 0`, `b = star`.)
-- (`lt_iff_le_not_le` is satisfied by surreal numbers, however.)
-- Thus we can not use `<` when defining a `partial_order`.
-- Because of this issue, we define the `partial_order` and `ordered_add_comm_group` instances,
-- but do not actually mark them as instances, for safety.
def partialOrder : PartialOrderₓ Game :=
  { Game.hasLe with le_refl := le_refl, le_trans := le_trans, le_antisymm := le_antisymm }

/-- The `<` operation provided by this `ordered_add_comm_group` is not the usual `<` on games! -/
def orderedAddCommGroup : OrderedAddCommGroup Game :=
  { Game.addCommGroup, Game.partialOrder with add_le_add_left := @add_le_add_left _ _ _ Game.covariant_class_add_le }

end Game

namespace Pgame

@[simp]
theorem quot_neg (a : Pgame) : ⟦-a⟧ = -⟦a⟧ :=
  rfl

@[simp]
theorem quot_add (a b : Pgame) : ⟦a + b⟧ = ⟦a⟧ + ⟦b⟧ :=
  rfl

@[simp]
theorem quot_sub (a b : Pgame) : ⟦a - b⟧ = ⟦a⟧ - ⟦b⟧ :=
  rfl

theorem quot_eq_of_mk_quot_eq {x y : Pgame} (L : x.LeftMoves ≃ y.LeftMoves) (R : x.RightMoves ≃ y.RightMoves)
    (hl : ∀ i : x.LeftMoves, ⟦x.moveLeft i⟧ = ⟦y.moveLeft (L i)⟧)
    (hr : ∀ j : y.RightMoves, ⟦x.moveRight (R.symm j)⟧ = ⟦y.moveRight j⟧) : ⟦x⟧ = ⟦y⟧ := by
  simp only [Quotientₓ.eq] at hl hr
  apply Quotientₓ.sound
  apply equiv_of_mk_equiv L R hl hr

/-! Multiplicative operations can be defined at the level of pre-games,
but to prove their properties we need to use the abelian group structure of games.
Hence we define them here. -/


/-- The product of `x = {xL | xR}` and `y = {yL | yR}` is
`{xL*y + x*yL - xL*yL, xR*y + x*yR - xR*yR | xL*y + x*yR - xL*yR, x*yL + xR*y - xR*yL }`. -/
instance : Mul Pgame.{u} :=
  ⟨fun x y => by
    induction' x with xl xr xL xR IHxl IHxr generalizing y
    induction' y with yl yr yL yR IHyl IHyr
    have y := mk yl yr yL yR
    refine' ⟨Sum (xl × yl) (xr × yr), Sum (xl × yr) (xr × yl), _, _⟩ <;> rintro (⟨i, j⟩ | ⟨i, j⟩)
    · exact IHxl i y + IHyl j - IHxl i (yL j)
      
    · exact IHxr i y + IHyr j - IHxr i (yR j)
      
    · exact IHxl i y + IHyr j - IHxl i (yR j)
      
    · exact IHxr i y + IHyl j - IHxr i (yL j)
      ⟩

theorem left_moves_mul :
    ∀ x y : Pgame.{u}, (x * y).LeftMoves = Sum (x.LeftMoves × y.LeftMoves) (x.RightMoves × y.RightMoves)
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩ => rfl

theorem right_moves_mul :
    ∀ x y : Pgame.{u}, (x * y).RightMoves = Sum (x.LeftMoves × y.RightMoves) (x.RightMoves × y.LeftMoves)
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩ => rfl

/-- Turns two left or right moves for `x` and `y` into a left move for `x * y` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toLeftMovesMul {x y : Pgame} : Sum (x.LeftMoves × y.LeftMoves) (x.RightMoves × y.RightMoves) ≃ (x * y).LeftMoves :=
  Equivₓ.cast (left_moves_mul x y).symm

/-- Turns a left and a right move for `x` and `y` into a right move for `x * y` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toRightMovesMul {x y : Pgame} :
    Sum (x.LeftMoves × y.RightMoves) (x.RightMoves × y.LeftMoves) ≃ (x * y).RightMoves :=
  Equivₓ.cast (right_moves_mul x y).symm

@[simp]
theorem mk_mul_move_left_inl {xl xr yl yr} {xL xR yL yR} {i j} :
    (mk xl xr xL xR * mk yl yr yL yR).moveLeft (Sum.inl (i, j)) =
      xL i * mk yl yr yL yR + mk xl xr xL xR * yL j - xL i * yL j :=
  rfl

@[simp]
theorem mul_move_left_inl {x y : Pgame} {i j} :
    (x * y).moveLeft (toLeftMovesMul (Sum.inl (i, j))) =
      x.moveLeft i * y + x * y.moveLeft j - x.moveLeft i * y.moveLeft j :=
  by
  cases x
  cases y
  rfl

@[simp]
theorem mk_mul_move_left_inr {xl xr yl yr} {xL xR yL yR} {i j} :
    (mk xl xr xL xR * mk yl yr yL yR).moveLeft (Sum.inr (i, j)) =
      xR i * mk yl yr yL yR + mk xl xr xL xR * yR j - xR i * yR j :=
  rfl

@[simp]
theorem mul_move_left_inr {x y : Pgame} {i j} :
    (x * y).moveLeft (toLeftMovesMul (Sum.inr (i, j))) =
      x.moveRight i * y + x * y.moveRight j - x.moveRight i * y.moveRight j :=
  by
  cases x
  cases y
  rfl

@[simp]
theorem mk_mul_move_right_inl {xl xr yl yr} {xL xR yL yR} {i j} :
    (mk xl xr xL xR * mk yl yr yL yR).moveRight (Sum.inl (i, j)) =
      xL i * mk yl yr yL yR + mk xl xr xL xR * yR j - xL i * yR j :=
  rfl

@[simp]
theorem mul_move_right_inl {x y : Pgame} {i j} :
    (x * y).moveRight (toRightMovesMul (Sum.inl (i, j))) =
      x.moveLeft i * y + x * y.moveRight j - x.moveLeft i * y.moveRight j :=
  by
  cases x
  cases y
  rfl

@[simp]
theorem mk_mul_move_right_inr {xl xr yl yr} {xL xR yL yR} {i j} :
    (mk xl xr xL xR * mk yl yr yL yR).moveRight (Sum.inr (i, j)) =
      xR i * mk yl yr yL yR + mk xl xr xL xR * yL j - xR i * yL j :=
  rfl

@[simp]
theorem mul_move_right_inr {x y : Pgame} {i j} :
    (x * y).moveRight (toRightMovesMul (Sum.inr (i, j))) =
      x.moveRight i * y + x * y.moveLeft j - x.moveRight i * y.moveLeft j :=
  by
  cases x
  cases y
  rfl

theorem quot_mul_comm : ∀ x y : Pgame.{u}, ⟦x * y⟧ = ⟦y * x⟧
  | mk xl xr xL xR, mk yl yr yL yR => by
    refine'
      quot_eq_of_mk_quot_eq (Equivₓ.sumCongr (Equivₓ.prodComm _ _) (Equivₓ.prodComm _ _))
        ((Equivₓ.sumComm _ _).trans (Equivₓ.sumCongr (Equivₓ.prodComm _ _) (Equivₓ.prodComm _ _))) _ _
    all_goals
      rintro (⟨i, j⟩ | ⟨i, j⟩) <;> dsimp' <;> rw [quot_mul_comm, quot_mul_comm (mk xl xr xL xR)]
    · rw [quot_mul_comm (xL i), add_commₓ]
      
    · rw [quot_mul_comm (xR i), add_commₓ]
      
    · rw [quot_mul_comm (xR j), add_commₓ]
      
    · rw [quot_mul_comm (xL j), add_commₓ]
      

/-- `x * y` is equivalent to `y * x`. -/
theorem mul_comm_equiv (x y : Pgame) : x * y ≈ y * x :=
  Quotientₓ.exact <| quot_mul_comm _ _

/-- `x * 0` has exactly the same moves as `0`. -/
def mulZeroRelabelling : ∀ x : Pgame, Relabelling (x * 0) 0
  | mk xl xr xL xR =>
    ⟨by
      fconstructor <;> rintro (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩), by
      fconstructor <;> rintro (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩), by
      rintro (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩), by
      rintro ⟨⟩⟩

/-- `x * 0` is equivalent to `0`. -/
theorem mul_zero_equiv (x : Pgame) : x * 0 ≈ 0 :=
  (mulZeroRelabelling x).Equiv

@[simp]
theorem quot_mul_zero (x : Pgame) : ⟦x * 0⟧ = ⟦0⟧ :=
  @Quotientₓ.sound _ _ (x * 0) _ x.mul_zero_equiv

/-- `0 * x` has exactly the same moves as `0`. -/
def zeroMulRelabelling : ∀ x : Pgame, Relabelling (0 * x) 0
  | mk xl xr xL xR =>
    ⟨by
      fconstructor <;> rintro (⟨⟨⟩, _⟩ | ⟨⟨⟩, _⟩), by
      fconstructor <;> rintro (⟨⟨⟩, _⟩ | ⟨⟨⟩, _⟩), by
      rintro (⟨⟨⟩, _⟩ | ⟨⟨⟩, _⟩), by
      rintro ⟨⟩⟩

/-- `0 * x` is equivalent to `0`. -/
theorem zero_mul_equiv (x : Pgame) : 0 * x ≈ 0 :=
  (zeroMulRelabelling x).Equiv

@[simp]
theorem quot_zero_mul (x : Pgame) : ⟦0 * x⟧ = ⟦0⟧ :=
  @Quotientₓ.sound _ _ (0 * x) _ x.zero_mul_equiv

@[simp]
theorem quot_neg_mul : ∀ x y : Pgame, ⟦-x * y⟧ = -⟦x * y⟧
  | mk xl xr xL xR, mk yl yr yL yR => by
    let x := mk xl xr xL xR
    let y := mk yl yr yL yR
    refine' quot_eq_of_mk_quot_eq _ _ _ _
    · fconstructor <;> rintro (⟨_, _⟩ | ⟨_, _⟩) <;> solve_by_elim [Sum.inl, Sum.inr, Prod.mk]
      
    · fconstructor <;> rintro (⟨_, _⟩ | ⟨_, _⟩) <;> solve_by_elim [Sum.inl, Sum.inr, Prod.mk]
      
    · rintro (⟨i, j⟩ | ⟨i, j⟩)
      · change ⟦-xR i * y + -x * yL j - -xR i * yL j⟧ = ⟦-(xR i * y + x * yL j - xR i * yL j)⟧
        simp only [quot_add, quot_sub, quot_neg_mul]
        simp
        abel
        
      · change ⟦-xL i * y + -x * yR j - -xL i * yR j⟧ = ⟦-(xL i * y + x * yR j - xL i * yR j)⟧
        simp only [quot_add, quot_sub, quot_neg_mul]
        simp
        abel
        
      
    · rintro (⟨i, j⟩ | ⟨i, j⟩)
      · change ⟦-xL i * y + -x * yL j - -xL i * yL j⟧ = ⟦-(xL i * y + x * yL j - xL i * yL j)⟧
        simp only [quot_add, quot_sub, quot_neg_mul]
        simp
        abel
        
      · change ⟦-xR i * y + -x * yR j - -xR i * yR j⟧ = ⟦-(xR i * y + x * yR j - xR i * yR j)⟧
        simp only [quot_add, quot_sub, quot_neg_mul]
        simp
        abel
        
      

@[simp]
theorem quot_mul_neg (x y : Pgame) : ⟦x * -y⟧ = -⟦x * y⟧ := by
  rw [quot_mul_comm, quot_neg_mul, quot_mul_comm]

@[simp]
theorem quot_left_distrib : ∀ x y z : Pgame, ⟦x * (y + z)⟧ = ⟦x * y⟧ + ⟦x * z⟧
  | mk xl xr xL xR, mk yl yr yL yR, mk zl zr zL zR => by
    let x := mk xl xr xL xR
    let y := mk yl yr yL yR
    let z := mk zl zr zL zR
    refine' quot_eq_of_mk_quot_eq _ _ _ _
    · fconstructor
      · rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩) <;> solve_by_elim [Sum.inl, Sum.inr, Prod.mk]
        
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;> solve_by_elim [Sum.inl, Sum.inr, Prod.mk]
        
      · rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩) <;> rfl
        
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;> rfl
        
      
    · fconstructor
      · rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩) <;> solve_by_elim [Sum.inl, Sum.inr, Prod.mk]
        
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;> solve_by_elim [Sum.inl, Sum.inr, Prod.mk]
        
      · rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩) <;> rfl
        
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;> rfl
        
      
    · rintro (⟨i, j | k⟩ | ⟨i, j | k⟩)
      · change ⟦xL i * (y + z) + x * (yL j + z) - xL i * (yL j + z)⟧ = ⟦xL i * y + x * yL j - xL i * yL j + x * z⟧
        simp [quot_left_distrib]
        abel
        
      · change ⟦xL i * (y + z) + x * (y + zL k) - xL i * (y + zL k)⟧ = ⟦x * y + (xL i * z + x * zL k - xL i * zL k)⟧
        simp [quot_left_distrib]
        abel
        
      · change ⟦xR i * (y + z) + x * (yR j + z) - xR i * (yR j + z)⟧ = ⟦xR i * y + x * yR j - xR i * yR j + x * z⟧
        simp [quot_left_distrib]
        abel
        
      · change ⟦xR i * (y + z) + x * (y + zR k) - xR i * (y + zR k)⟧ = ⟦x * y + (xR i * z + x * zR k - xR i * zR k)⟧
        simp [quot_left_distrib]
        abel
        
      
    · rintro (⟨⟨i, j⟩ | ⟨i, j⟩⟩ | ⟨i, k⟩ | ⟨i, k⟩)
      · change ⟦xL i * (y + z) + x * (yR j + z) - xL i * (yR j + z)⟧ = ⟦xL i * y + x * yR j - xL i * yR j + x * z⟧
        simp [quot_left_distrib]
        abel
        
      · change ⟦xR i * (y + z) + x * (yL j + z) - xR i * (yL j + z)⟧ = ⟦xR i * y + x * yL j - xR i * yL j + x * z⟧
        simp [quot_left_distrib]
        abel
        
      · change ⟦xL i * (y + z) + x * (y + zR k) - xL i * (y + zR k)⟧ = ⟦x * y + (xL i * z + x * zR k - xL i * zR k)⟧
        simp [quot_left_distrib]
        abel
        
      · change ⟦xR i * (y + z) + x * (y + zL k) - xR i * (y + zL k)⟧ = ⟦x * y + (xR i * z + x * zL k - xR i * zL k)⟧
        simp [quot_left_distrib]
        abel
        
      

/-- `x * (y + z)` is equivalent to `x * y + x * z.`-/
theorem left_distrib_equiv (x y z : Pgame) : x * (y + z) ≈ x * y + x * z :=
  Quotientₓ.exact <| quot_left_distrib _ _ _

@[simp]
theorem quot_left_distrib_sub (x y z : Pgame) : ⟦x * (y - z)⟧ = ⟦x * y⟧ - ⟦x * z⟧ := by
  change ⟦x * (y + -z)⟧ = ⟦x * y⟧ + -⟦x * z⟧
  rw [quot_left_distrib, quot_mul_neg]

@[simp]
theorem quot_right_distrib (x y z : Pgame) : ⟦(x + y) * z⟧ = ⟦x * z⟧ + ⟦y * z⟧ := by
  simp only [quot_mul_comm, quot_left_distrib]

/-- `(x + y) * z` is equivalent to `x * z + y * z.`-/
theorem right_distrib_equiv (x y z : Pgame) : (x + y) * z ≈ x * z + y * z :=
  Quotientₓ.exact <| quot_right_distrib _ _ _

@[simp]
theorem quot_right_distrib_sub (x y z : Pgame) : ⟦(y - z) * x⟧ = ⟦y * x⟧ - ⟦z * x⟧ := by
  change ⟦(y + -z) * x⟧ = ⟦y * x⟧ + -⟦z * x⟧
  rw [quot_right_distrib, quot_neg_mul]

@[simp]
theorem quot_mul_one : ∀ x : Pgame, ⟦x * 1⟧ = ⟦x⟧
  | mk xl xr xL xR => by
    let x := mk xl xr xL xR
    refine' quot_eq_of_mk_quot_eq _ _ _ _
    · fconstructor
      · rintro (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩)
        assumption
        
      · rintro i
        exact Sum.inl (i, PUnit.unit)
        
      · rintro (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩)
        rfl
        
      · rintro i
        rfl
        
      
    · fconstructor
      · rintro (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩)
        assumption
        
      · rintro i
        exact Sum.inr (i, PUnit.unit)
        
      · rintro (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩)
        rfl
        
      · rintro i
        rfl
        
      
    · rintro (⟨i, ⟨⟩⟩ | ⟨i, ⟨⟩⟩)
      change ⟦xL i * 1 + x * 0 - xL i * 0⟧ = ⟦xL i⟧
      simp [quot_mul_one]
      
    · rintro i
      change ⟦xR i * 1 + x * 0 - xR i * 0⟧ = ⟦xR i⟧
      simp [quot_mul_one]
      

/-- `x * 1` is equivalent to `x`. -/
theorem mul_one_equiv (x : Pgame) : x * 1 ≈ x :=
  Quotientₓ.exact <| quot_mul_one _

@[simp]
theorem quot_one_mul (x : Pgame) : ⟦1 * x⟧ = ⟦x⟧ := by
  rw [quot_mul_comm, quot_mul_one x]

/-- `1 * x` is equivalent to `x`. -/
theorem one_mul_equiv (x : Pgame) : 1 * x ≈ x :=
  Quotientₓ.exact <| quot_one_mul _

theorem quot_mul_assoc : ∀ x y z : Pgame, ⟦x * y * z⟧ = ⟦x * (y * z)⟧
  | mk xl xr xL xR, mk yl yr yL yR, mk zl zr zL zR => by
    let x := mk xl xr xL xR
    let y := mk yl yr yL yR
    let z := mk zl zr zL zR
    refine' quot_eq_of_mk_quot_eq _ _ _ _
    · fconstructor
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩) <;> solve_by_elim [Sum.inl, Sum.inr, Prod.mk]
        
      · rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩) <;> solve_by_elim [Sum.inl, Sum.inr, Prod.mk]
        
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩) <;> rfl
        
      · rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩) <;> rfl
        
      
    · fconstructor
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩) <;> solve_by_elim [Sum.inl, Sum.inr, Prod.mk]
        
      · rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩) <;> solve_by_elim [Sum.inl, Sum.inr, Prod.mk]
        
      · rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩) <;> rfl
        
      · rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩) <;> rfl
        
      
    · rintro (⟨⟨i, j⟩ | ⟨i, j⟩, k⟩ | ⟨⟨i, j⟩ | ⟨i, j⟩, k⟩)
      · change
          ⟦(xL i * y + x * yL j - xL i * yL j) * z + x * y * zL k - (xL i * y + x * yL j - xL i * yL j) * zL k⟧ =
            ⟦xL i * (y * z) + x * (yL j * z + y * zL k - yL j * zL k) - xL i * (yL j * z + y * zL k - yL j * zL k)⟧
        simp [quot_mul_assoc]
        abel
        
      · change
          ⟦(xR i * y + x * yR j - xR i * yR j) * z + x * y * zL k - (xR i * y + x * yR j - xR i * yR j) * zL k⟧ =
            ⟦xR i * (y * z) + x * (yR j * z + y * zL k - yR j * zL k) - xR i * (yR j * z + y * zL k - yR j * zL k)⟧
        simp [quot_mul_assoc]
        abel
        
      · change
          ⟦(xL i * y + x * yR j - xL i * yR j) * z + x * y * zR k - (xL i * y + x * yR j - xL i * yR j) * zR k⟧ =
            ⟦xL i * (y * z) + x * (yR j * z + y * zR k - yR j * zR k) - xL i * (yR j * z + y * zR k - yR j * zR k)⟧
        simp [quot_mul_assoc]
        abel
        
      · change
          ⟦(xR i * y + x * yL j - xR i * yL j) * z + x * y * zR k - (xR i * y + x * yL j - xR i * yL j) * zR k⟧ =
            ⟦xR i * (y * z) + x * (yL j * z + y * zR k - yL j * zR k) - xR i * (yL j * z + y * zR k - yL j * zR k)⟧
        simp [quot_mul_assoc]
        abel
        
      
    · rintro (⟨i, ⟨j, k⟩ | ⟨j, k⟩⟩ | ⟨i, ⟨j, k⟩ | ⟨j, k⟩⟩)
      · change
          ⟦(xL i * y + x * yL j - xL i * yL j) * z + x * y * zR k - (xL i * y + x * yL j - xL i * yL j) * zR k⟧ =
            ⟦xL i * (y * z) + x * (yL j * z + y * zR k - yL j * zR k) - xL i * (yL j * z + y * zR k - yL j * zR k)⟧
        simp [quot_mul_assoc]
        abel
        
      · change
          ⟦(xL i * y + x * yR j - xL i * yR j) * z + x * y * zL k - (xL i * y + x * yR j - xL i * yR j) * zL k⟧ =
            ⟦xL i * (y * z) + x * (yR j * z + y * zL k - yR j * zL k) - xL i * (yR j * z + y * zL k - yR j * zL k)⟧
        simp [quot_mul_assoc]
        abel
        
      · change
          ⟦(xR i * y + x * yL j - xR i * yL j) * z + x * y * zL k - (xR i * y + x * yL j - xR i * yL j) * zL k⟧ =
            ⟦xR i * (y * z) + x * (yL j * z + y * zL k - yL j * zL k) - xR i * (yL j * z + y * zL k - yL j * zL k)⟧
        simp [quot_mul_assoc]
        abel
        
      · change
          ⟦(xR i * y + x * yR j - xR i * yR j) * z + x * y * zR k - (xR i * y + x * yR j - xR i * yR j) * zR k⟧ =
            ⟦xR i * (y * z) + x * (yR j * z + y * zR k - yR j * zR k) - xR i * (yR j * z + y * zR k - yR j * zR k)⟧
        simp [quot_mul_assoc]
        abel
        
      

/-- `x * y * z` is equivalent to `x * (y * z).`-/
theorem mul_assoc_equiv (x y z : Pgame) : x * y * z ≈ x * (y * z) :=
  Quotientₓ.exact <| quot_mul_assoc _ _ _

/-- Because the two halves of the definition of `inv` produce more elements
on each side, we have to define the two families inductively.
This is the indexing set for the function, and `inv_val` is the function part. -/
inductive InvTy (l r : Type u) : Bool → Type u
  | zero : inv_ty false
  | left₁ : r → inv_ty false → inv_ty false
  | left₂ : l → inv_ty true → inv_ty false
  | right₁ : l → inv_ty false → inv_ty true
  | right₂ : r → inv_ty true → inv_ty true

instance (l r : Type u) : Inhabited (InvTy l r false) :=
  ⟨InvTy.zero⟩

/-- Because the two halves of the definition of `inv` produce more elements
of each side, we have to define the two families inductively.
This is the function part, defined by recursion on `inv_ty`. -/
def invVal {l r} (L : l → Pgame) (R : r → Pgame) (IHl : l → Pgame) (IHr : r → Pgame) : ∀ {b}, InvTy l r b → Pgame
  | _, inv_ty.zero => 0
  | _, inv_ty.left₁ i j => (1 + (R i - mk l r L R) * inv_val j) * IHr i
  | _, inv_ty.left₂ i j => (1 + (L i - mk l r L R) * inv_val j) * IHl i
  | _, inv_ty.right₁ i j => (1 + (L i - mk l r L R) * inv_val j) * IHl i
  | _, inv_ty.right₂ i j => (1 + (R i - mk l r L R) * inv_val j) * IHr i

/-- The inverse of a positive surreal number `x = {L | R}` is
given by `x⁻¹ = {0,
  (1 + (R - x) * x⁻¹L) * R, (1 + (L - x) * x⁻¹R) * L |
  (1 + (L - x) * x⁻¹L) * L, (1 + (R - x) * x⁻¹R) * R}`.
Because the two halves `x⁻¹L, x⁻¹R` of `x⁻¹` are used in their own
definition, the sets and elements are inductively generated. -/
def inv' : Pgame → Pgame
  | ⟨l, r, L, R⟩ =>
    let l' := { i // 0 < L i }
    let L' : l' → Pgame := fun i => L i.1
    let IHl' : l' → Pgame := fun i => inv' (L i.1)
    let IHr := fun i => inv' (R i)
    ⟨InvTy l' r false, InvTy l' r true, invVal L' R IHl' IHr, invVal L' R IHl' IHr⟩

/-- The inverse of a surreal number in terms of the inverse on positive surreals. -/
noncomputable instance : Inv Pgame :=
  ⟨by
    classical
    exact fun x => if x = 0 then 0 else if 0 < x then inv' x else inv' (-x)⟩

noncomputable instance : Div Pgame :=
  ⟨fun x y => x * y⁻¹⟩

end Pgame

