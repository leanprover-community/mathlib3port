/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Scott Morrison
-/
import Mathbin.Algebra.Order.Hom.Monoid
import Mathbin.SetTheory.Game.Ordinal

#align_import set_theory.surreal.basic from "leanprover-community/mathlib"@"8900d545017cd21961daa2a1734bb658ef52c618"

/-!
# Surreal numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The basic theory of surreal numbers, built on top of the theory of combinatorial (pre-)games.

A pregame is `numeric` if all the Left options are strictly smaller than all the Right options, and
all those options are themselves numeric. In terms of combinatorial games, the numeric games have
"frozen"; you can only make your position worse by playing, and Left is some definite "number" of
moves ahead (or behind) Right.

A surreal number is an equivalence class of numeric pregames.

In fact, the surreals form a complete ordered field, containing a copy of the reals (and much else
besides!) but we do not yet have a complete development.

## Order properties

Surreal numbers inherit the relations `≤` and `<` from games (`surreal.has_le` and
`surreal.has_lt`), and these relations satisfy the axioms of a partial order.

## Algebraic operations

We show that the surreals form a linear ordered commutative group.

One can also map all the ordinals into the surreals!

### Multiplication of surreal numbers

The proof that multiplication lifts to surreal numbers is surprisingly difficult and is currently
missing in the library. A sample proof can be found in Theorem 3.8 in the second reference below.
The difficulty lies in the length of the proof and the number of theorems that need to proven
simultaneously. This will make for a fun and challenging project.

The branch `surreal_mul` contains some progress on this proof.

### Todo

- Define the field structure on the surreals.

## References

* [Conway, *On numbers and games*][conway2001]
* [Schleicher, Stoll, *An introduction to Conway's games and numbers*][schleicher_stoll]
-/


universe u

open scoped SetTheory.PGame

namespace SetTheory.PGame

#print SetTheory.PGame.Numeric /-
/-- A pre-game is numeric if everything in the L set is less than everything in the R set,
and all the elements of L and R are also numeric. -/
def SetTheory.PGame.Numeric : SetTheory.PGame → Prop
  | ⟨l, r, L, R⟩ => (∀ i j, L i < R j) ∧ (∀ i, numeric (L i)) ∧ ∀ j, numeric (R j)
#align pgame.numeric SetTheory.PGame.Numeric
-/

#print SetTheory.PGame.numeric_def /-
theorem SetTheory.PGame.numeric_def {x : SetTheory.PGame} :
    SetTheory.PGame.Numeric x ↔
      (∀ i j, x.moveLeft i < x.moveRight j) ∧
        (∀ i, SetTheory.PGame.Numeric (x.moveLeft i)) ∧
          ∀ j, SetTheory.PGame.Numeric (x.moveRight j) :=
  by cases x; rfl
#align pgame.numeric_def SetTheory.PGame.numeric_def
-/

namespace Numeric

#print SetTheory.PGame.Numeric.mk /-
theorem SetTheory.PGame.Numeric.mk {x : SetTheory.PGame} (h₁ : ∀ i j, x.moveLeft i < x.moveRight j)
    (h₂ : ∀ i, SetTheory.PGame.Numeric (x.moveLeft i))
    (h₃ : ∀ j, SetTheory.PGame.Numeric (x.moveRight j)) : SetTheory.PGame.Numeric x :=
  SetTheory.PGame.numeric_def.2 ⟨h₁, h₂, h₃⟩
#align pgame.numeric.mk SetTheory.PGame.Numeric.mk
-/

#print SetTheory.PGame.Numeric.left_lt_right /-
theorem SetTheory.PGame.Numeric.left_lt_right {x : SetTheory.PGame} (o : SetTheory.PGame.Numeric x)
    (i : x.LeftMoves) (j : x.RightMoves) : x.moveLeft i < x.moveRight j := by cases x; exact o.1 i j
#align pgame.numeric.left_lt_right SetTheory.PGame.Numeric.left_lt_right
-/

#print SetTheory.PGame.Numeric.moveLeft /-
theorem SetTheory.PGame.Numeric.moveLeft {x : SetTheory.PGame} (o : SetTheory.PGame.Numeric x)
    (i : x.LeftMoves) : SetTheory.PGame.Numeric (x.moveLeft i) := by cases x; exact o.2.1 i
#align pgame.numeric.move_left SetTheory.PGame.Numeric.moveLeft
-/

#print SetTheory.PGame.Numeric.moveRight /-
theorem SetTheory.PGame.Numeric.moveRight {x : SetTheory.PGame} (o : SetTheory.PGame.Numeric x)
    (j : x.RightMoves) : SetTheory.PGame.Numeric (x.moveRight j) := by cases x; exact o.2.2 j
#align pgame.numeric.move_right SetTheory.PGame.Numeric.moveRight
-/

end Numeric

#print SetTheory.PGame.numeric_rec /-
@[elab_as_elim]
theorem SetTheory.PGame.numeric_rec {C : SetTheory.PGame → Prop}
    (H :
      ∀ (l r) (L : l → SetTheory.PGame) (R : r → SetTheory.PGame),
        (∀ i j, L i < R j) →
          (∀ i, SetTheory.PGame.Numeric (L i)) →
            (∀ i, SetTheory.PGame.Numeric (R i)) →
              (∀ i, C (L i)) → (∀ i, C (R i)) → C ⟨l, r, L, R⟩) :
    ∀ x, SetTheory.PGame.Numeric x → C x
  | ⟨l, r, L, R⟩, ⟨h, hl, hr⟩ =>
    H _ _ _ _ h hl hr (fun i => numeric_rec _ (hl i)) fun i => numeric_rec _ (hr i)
#align pgame.numeric_rec SetTheory.PGame.numeric_rec
-/

#print SetTheory.PGame.Relabelling.numeric_imp /-
theorem SetTheory.PGame.Relabelling.numeric_imp {x y : SetTheory.PGame} (r : x ≡r y)
    (ox : SetTheory.PGame.Numeric x) : SetTheory.PGame.Numeric y :=
  by
  induction' x using SetTheory.PGame.moveRecOn with x IHl IHr generalizing y
  apply numeric.mk (fun i j => _) (fun i => _) fun j => _
  · rw [← lt_congr (r.move_left_symm i).Equiv (r.move_right_symm j).Equiv]
    apply ox.left_lt_right
  · exact IHl _ (ox.move_left _) (r.move_left_symm i)
  · exact IHr _ (ox.move_right _) (r.move_right_symm j)
#align pgame.relabelling.numeric_imp SetTheory.PGame.Relabelling.numeric_imp
-/

#print SetTheory.PGame.Relabelling.numeric_congr /-
/-- Relabellings preserve being numeric. -/
theorem SetTheory.PGame.Relabelling.numeric_congr {x y : SetTheory.PGame} (r : x ≡r y) :
    SetTheory.PGame.Numeric x ↔ SetTheory.PGame.Numeric y :=
  ⟨r.numeric_imp, r.symm.numeric_imp⟩
#align pgame.relabelling.numeric_congr SetTheory.PGame.Relabelling.numeric_congr
-/

#print SetTheory.PGame.lf_asymm /-
theorem SetTheory.PGame.lf_asymm {x y : SetTheory.PGame} (ox : SetTheory.PGame.Numeric x)
    (oy : SetTheory.PGame.Numeric y) : x ⧏ y → ¬y ⧏ x :=
  by
  refine' numeric_rec (fun xl xr xL xR hx oxl oxr IHxl IHxr => _) x ox y oy
  refine' numeric_rec fun yl yr yL yR hy oyl oyr IHyl IHyr => _
  rw [mk_lf_mk, mk_lf_mk]; rintro (⟨i, h₁⟩ | ⟨j, h₁⟩) (⟨i, h₂⟩ | ⟨j, h₂⟩)
  · exact IHxl _ _ (oyl _) (h₁.move_left_lf _) (h₂.move_left_lf _)
  · exact (le_trans h₂ h₁).not_gf (lf_of_lt (hy _ _))
  · exact (le_trans h₁ h₂).not_gf (lf_of_lt (hx _ _))
  · exact IHxr _ _ (oyr _) (h₁.lf_move_right _) (h₂.lf_move_right _)
#align pgame.lf_asymm SetTheory.PGame.lf_asymm
-/

#print SetTheory.PGame.le_of_lf /-
theorem SetTheory.PGame.le_of_lf {x y : SetTheory.PGame} (h : x ⧏ y)
    (ox : SetTheory.PGame.Numeric x) (oy : SetTheory.PGame.Numeric y) : x ≤ y :=
  SetTheory.PGame.not_lf.1 (SetTheory.PGame.lf_asymm ox oy h)
#align pgame.le_of_lf SetTheory.PGame.le_of_lf
-/

alias lf.le := le_of_lf
#align pgame.lf.le SetTheory.PGame.LF.le

#print SetTheory.PGame.lt_of_lf /-
theorem SetTheory.PGame.lt_of_lf {x y : SetTheory.PGame} (h : x ⧏ y)
    (ox : SetTheory.PGame.Numeric x) (oy : SetTheory.PGame.Numeric y) : x < y :=
  (SetTheory.PGame.lt_or_fuzzy_of_lf h).resolve_right (SetTheory.PGame.not_fuzzy_of_le (h.le ox oy))
#align pgame.lt_of_lf SetTheory.PGame.lt_of_lf
-/

alias lf.lt := lt_of_lf
#align pgame.lf.lt SetTheory.PGame.LF.lt

#print SetTheory.PGame.lf_iff_lt /-
theorem SetTheory.PGame.lf_iff_lt {x y : SetTheory.PGame} (ox : SetTheory.PGame.Numeric x)
    (oy : SetTheory.PGame.Numeric y) : x ⧏ y ↔ x < y :=
  ⟨fun h => h.lt ox oy, SetTheory.PGame.lf_of_lt⟩
#align pgame.lf_iff_lt SetTheory.PGame.lf_iff_lt
-/

#print SetTheory.PGame.le_iff_forall_lt /-
/-- Definition of `x ≤ y` on numeric pre-games, in terms of `<` -/
theorem SetTheory.PGame.le_iff_forall_lt {x y : SetTheory.PGame} (ox : x.Numeric) (oy : y.Numeric) :
    x ≤ y ↔ (∀ i, x.moveLeft i < y) ∧ ∀ j, x < y.moveRight j := by
  refine' le_iff_forall_lf.trans (and_congr _ _) <;>
      refine' forall_congr' fun i => lf_iff_lt _ _ <;>
    apply_rules [numeric.move_left, numeric.move_right]
#align pgame.le_iff_forall_lt SetTheory.PGame.le_iff_forall_lt
-/

#print SetTheory.PGame.lt_iff_exists_le /-
/-- Definition of `x < y` on numeric pre-games, in terms of `≤` -/
theorem SetTheory.PGame.lt_iff_exists_le {x y : SetTheory.PGame} (ox : x.Numeric) (oy : y.Numeric) :
    x < y ↔ (∃ i, x ≤ y.moveLeft i) ∨ ∃ j, x.moveRight j ≤ y := by
  rw [← lf_iff_lt ox oy, lf_iff_exists_le]
#align pgame.lt_iff_exists_le SetTheory.PGame.lt_iff_exists_le
-/

#print SetTheory.PGame.lt_of_exists_le /-
theorem SetTheory.PGame.lt_of_exists_le {x y : SetTheory.PGame} (ox : x.Numeric) (oy : y.Numeric) :
    ((∃ i, x ≤ y.moveLeft i) ∨ ∃ j, x.moveRight j ≤ y) → x < y :=
  (SetTheory.PGame.lt_iff_exists_le ox oy).2
#align pgame.lt_of_exists_le SetTheory.PGame.lt_of_exists_le
-/

#print SetTheory.PGame.lt_def /-
/-- The definition of `x < y` on numeric pre-games, in terms of `<` two moves later. -/
theorem SetTheory.PGame.lt_def {x y : SetTheory.PGame} (ox : x.Numeric) (oy : y.Numeric) :
    x < y ↔
      (∃ i, (∀ i', x.moveLeft i' < y.moveLeft i) ∧ ∀ j, x < (y.moveLeft i).moveRight j) ∨
        ∃ j, (∀ i, (x.moveRight j).moveLeft i < y) ∧ ∀ j', x.moveRight j < y.moveRight j' :=
  by
  rw [← lf_iff_lt ox oy, lf_def]
  refine' or_congr _ _ <;> refine' exists_congr fun x_1 => _ <;> refine' and_congr _ _ <;>
      refine' forall_congr' fun i => lf_iff_lt _ _ <;>
    apply_rules [numeric.move_left, numeric.move_right]
#align pgame.lt_def SetTheory.PGame.lt_def
-/

#print SetTheory.PGame.not_fuzzy /-
theorem SetTheory.PGame.not_fuzzy {x y : SetTheory.PGame} (ox : SetTheory.PGame.Numeric x)
    (oy : SetTheory.PGame.Numeric y) : ¬SetTheory.PGame.Fuzzy x y := fun h =>
  SetTheory.PGame.not_lf.2 ((SetTheory.PGame.lf_of_fuzzy h).le ox oy) h.2
#align pgame.not_fuzzy SetTheory.PGame.not_fuzzy
-/

#print SetTheory.PGame.lt_or_equiv_or_gt /-
theorem SetTheory.PGame.lt_or_equiv_or_gt {x y : SetTheory.PGame} (ox : SetTheory.PGame.Numeric x)
    (oy : SetTheory.PGame.Numeric y) : x < y ∨ (x ≈ y) ∨ y < x :=
  ((SetTheory.PGame.lf_or_equiv_or_gf x y).imp fun h => h.lt ox oy) <|
    Or.imp_right fun h => h.lt oy ox
#align pgame.lt_or_equiv_or_gt SetTheory.PGame.lt_or_equiv_or_gt
-/

#print SetTheory.PGame.numeric_of_isEmpty /-
theorem SetTheory.PGame.numeric_of_isEmpty (x : SetTheory.PGame) [IsEmpty x.LeftMoves]
    [IsEmpty x.RightMoves] : SetTheory.PGame.Numeric x :=
  SetTheory.PGame.Numeric.mk isEmptyElim isEmptyElim isEmptyElim
#align pgame.numeric_of_is_empty SetTheory.PGame.numeric_of_isEmpty
-/

#print SetTheory.PGame.numeric_of_isEmpty_leftMoves /-
theorem SetTheory.PGame.numeric_of_isEmpty_leftMoves (x : SetTheory.PGame) [IsEmpty x.LeftMoves] :
    (∀ j, SetTheory.PGame.Numeric (x.moveRight j)) → SetTheory.PGame.Numeric x :=
  SetTheory.PGame.Numeric.mk isEmptyElim isEmptyElim
#align pgame.numeric_of_is_empty_left_moves SetTheory.PGame.numeric_of_isEmpty_leftMoves
-/

#print SetTheory.PGame.numeric_of_isEmpty_rightMoves /-
theorem SetTheory.PGame.numeric_of_isEmpty_rightMoves (x : SetTheory.PGame) [IsEmpty x.RightMoves]
    (H : ∀ i, SetTheory.PGame.Numeric (x.moveLeft i)) : SetTheory.PGame.Numeric x :=
  SetTheory.PGame.Numeric.mk (fun _ => isEmptyElim) H isEmptyElim
#align pgame.numeric_of_is_empty_right_moves SetTheory.PGame.numeric_of_isEmpty_rightMoves
-/

#print SetTheory.PGame.numeric_zero /-
theorem SetTheory.PGame.numeric_zero : SetTheory.PGame.Numeric 0 :=
  SetTheory.PGame.numeric_of_isEmpty 0
#align pgame.numeric_zero SetTheory.PGame.numeric_zero
-/

#print SetTheory.PGame.numeric_one /-
theorem SetTheory.PGame.numeric_one : SetTheory.PGame.Numeric 1 :=
  SetTheory.PGame.numeric_of_isEmpty_rightMoves 1 fun _ => SetTheory.PGame.numeric_zero
#align pgame.numeric_one SetTheory.PGame.numeric_one
-/

#print SetTheory.PGame.Numeric.neg /-
theorem SetTheory.PGame.Numeric.neg :
    ∀ {x : SetTheory.PGame} (o : SetTheory.PGame.Numeric x), SetTheory.PGame.Numeric (-x)
  | ⟨l, r, L, R⟩, o =>
    ⟨fun j i => SetTheory.PGame.neg_lt_neg_iff.2 (o.1 i j), fun j => (o.2.2 j).neg, fun i =>
      (o.2.1 i).neg⟩
#align pgame.numeric.neg SetTheory.PGame.Numeric.neg
-/

namespace Numeric

#print SetTheory.PGame.Numeric.moveLeft_lt /-
theorem SetTheory.PGame.Numeric.moveLeft_lt {x : SetTheory.PGame} (o : SetTheory.PGame.Numeric x)
    (i) : x.moveLeft i < x :=
  (SetTheory.PGame.moveLeft_lf i).lt (o.moveLeft i) o
#align pgame.numeric.move_left_lt SetTheory.PGame.Numeric.moveLeft_lt
-/

#print SetTheory.PGame.Numeric.moveLeft_le /-
theorem SetTheory.PGame.Numeric.moveLeft_le {x : SetTheory.PGame} (o : SetTheory.PGame.Numeric x)
    (i) : x.moveLeft i ≤ x :=
  (o.moveLeft_lt i).le
#align pgame.numeric.move_left_le SetTheory.PGame.Numeric.moveLeft_le
-/

#print SetTheory.PGame.Numeric.lt_moveRight /-
theorem SetTheory.PGame.Numeric.lt_moveRight {x : SetTheory.PGame} (o : SetTheory.PGame.Numeric x)
    (j) : x < x.moveRight j :=
  (SetTheory.PGame.lf_moveRight j).lt o (o.moveRight j)
#align pgame.numeric.lt_move_right SetTheory.PGame.Numeric.lt_moveRight
-/

#print SetTheory.PGame.Numeric.le_moveRight /-
theorem SetTheory.PGame.Numeric.le_moveRight {x : SetTheory.PGame} (o : SetTheory.PGame.Numeric x)
    (j) : x ≤ x.moveRight j :=
  (o.lt_moveRight j).le
#align pgame.numeric.le_move_right SetTheory.PGame.Numeric.le_moveRight
-/

#print SetTheory.PGame.Numeric.add /-
theorem SetTheory.PGame.Numeric.add :
    ∀ {x y : SetTheory.PGame} (ox : SetTheory.PGame.Numeric x) (oy : SetTheory.PGame.Numeric y),
      SetTheory.PGame.Numeric (x + y)
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩, ox, oy =>
    ⟨by
      rintro (ix | iy) (jx | jy)
      · exact add_lt_add_right (ox.1 ix jx) _
      ·
        exact
          (add_lf_add_of_lf_of_le (lf_mk _ _ ix) (oy.le_move_right jy)).lt
            ((ox.move_left ix).add oy) (ox.add (oy.move_right jy))
      ·
        exact
          (add_lf_add_of_lf_of_le (mk_lf _ _ jx) (oy.move_left_le iy)).lt (ox.add (oy.move_left iy))
            ((ox.move_right jx).add oy)
      · exact add_lt_add_left (oy.1 iy jy) ⟨xl, xr, xL, xR⟩,
      by
      constructor
      · rintro (ix | iy)
        · exact (ox.move_left ix).add oy
        · exact ox.add (oy.move_left iy)
      · rintro (jx | jy)
        · apply (ox.move_right jx).add oy
        · apply ox.add (oy.move_right jy)⟩
decreasing_by pgame_wf_tac
#align pgame.numeric.add SetTheory.PGame.Numeric.add
-/

#print SetTheory.PGame.Numeric.sub /-
theorem SetTheory.PGame.Numeric.sub {x y : SetTheory.PGame} (ox : SetTheory.PGame.Numeric x)
    (oy : SetTheory.PGame.Numeric y) : SetTheory.PGame.Numeric (x - y) :=
  ox.add oy.neg
#align pgame.numeric.sub SetTheory.PGame.Numeric.sub
-/

end Numeric

#print SetTheory.PGame.numeric_nat /-
/-- Pre-games defined by natural numbers are numeric. -/
theorem SetTheory.PGame.numeric_nat : ∀ n : ℕ, SetTheory.PGame.Numeric n
  | 0 => SetTheory.PGame.numeric_zero
  | n + 1 => (numeric_nat n).add SetTheory.PGame.numeric_one
#align pgame.numeric_nat SetTheory.PGame.numeric_nat
-/

#print SetTheory.PGame.numeric_toPGame /-
/-- Ordinal games are numeric. -/
theorem SetTheory.PGame.numeric_toPGame (o : Ordinal) : o.toPGame.Numeric :=
  by
  induction' o using Ordinal.induction with o IH
  apply numeric_of_is_empty_right_moves
  simpa using fun i => IH _ (Ordinal.toLeftMovesToPGame_symm_lt i)
#align pgame.numeric_to_pgame SetTheory.PGame.numeric_toPGame
-/

end SetTheory.PGame

open SetTheory.PGame

#print Surreal /-
/-- The type of surreal numbers. These are the numeric pre-games quotiented
by the equivalence relation `x ≈ y ↔ x ≤ y ∧ y ≤ x`. In the quotient,
the order becomes a total order. -/
def Surreal :=
  Quotient (Subtype.setoid SetTheory.PGame.Numeric)
#align surreal Surreal
-/

namespace Surreal

#print Surreal.mk /-
/-- Construct a surreal number from a numeric pre-game. -/
def mk (x : SetTheory.PGame) (h : x.Numeric) : Surreal :=
  ⟦⟨x, h⟩⟧
#align surreal.mk Surreal.mk
-/

instance : Zero Surreal :=
  ⟨mk 0 SetTheory.PGame.numeric_zero⟩

instance : One Surreal :=
  ⟨mk 1 SetTheory.PGame.numeric_one⟩

instance : Inhabited Surreal :=
  ⟨0⟩

#print Surreal.lift /-
/-- Lift an equivalence-respecting function on pre-games to surreals. -/
def lift {α} (f : ∀ x, SetTheory.PGame.Numeric x → α)
    (H :
      ∀ {x y} (hx : SetTheory.PGame.Numeric x) (hy : SetTheory.PGame.Numeric y),
        x.Equiv y → f x hx = f y hy) :
    Surreal → α :=
  Quotient.lift (fun x : { x // SetTheory.PGame.Numeric x } => f x.1 x.2) fun x y => H x.2 y.2
#align surreal.lift Surreal.lift
-/

#print Surreal.lift₂ /-
/-- Lift a binary equivalence-respecting function on pre-games to surreals. -/
def lift₂ {α} (f : ∀ x y, SetTheory.PGame.Numeric x → SetTheory.PGame.Numeric y → α)
    (H :
      ∀ {x₁ y₁ x₂ y₂} (ox₁ : SetTheory.PGame.Numeric x₁) (oy₁ : SetTheory.PGame.Numeric y₁)
        (ox₂ : SetTheory.PGame.Numeric x₂) (oy₂ : SetTheory.PGame.Numeric y₂),
        x₁.Equiv x₂ → y₁.Equiv y₂ → f x₁ y₁ ox₁ oy₁ = f x₂ y₂ ox₂ oy₂) :
    Surreal → Surreal → α :=
  lift
    (fun x ox =>
      lift (fun y oy => f x y ox oy) fun y₁ y₂ oy₁ oy₂ => H _ _ _ _ SetTheory.PGame.equiv_rfl)
    fun x₁ x₂ ox₁ ox₂ h => funext <| Quotient.ind fun ⟨y, oy⟩ => H _ _ _ _ h equiv_rfl
#align surreal.lift₂ Surreal.lift₂
-/

instance : LE Surreal :=
  ⟨lift₂ (fun x y _ _ => x ≤ y) fun x₁ y₁ x₂ y₂ _ _ _ _ hx hy =>
      propext (SetTheory.PGame.le_congr hx hy)⟩

instance : LT Surreal :=
  ⟨lift₂ (fun x y _ _ => x < y) fun x₁ y₁ x₂ y₂ _ _ _ _ hx hy =>
      propext (SetTheory.PGame.lt_congr hx hy)⟩

/-- Addition on surreals is inherited from pre-game addition:
the sum of `x = {xL | xR}` and `y = {yL | yR}` is `{xL + y, x + yL | xR + y, x + yR}`. -/
instance : Add Surreal :=
  ⟨Surreal.lift₂ (fun (x y : SetTheory.PGame) ox oy => ⟦⟨x + y, ox.add oy⟩⟧)
      fun x₁ y₁ x₂ y₂ _ _ _ _ hx hy => Quotient.sound (SetTheory.PGame.add_congr hx hy)⟩

/-- Negation for surreal numbers is inherited from pre-game negation:
the negation of `{L | R}` is `{-R | -L}`. -/
instance : Neg Surreal :=
  ⟨Surreal.lift (fun x ox => ⟦⟨-x, ox.neg⟩⟧) fun _ _ _ _ a =>
      Quotient.sound (SetTheory.PGame.neg_equiv_neg_iff.2 a)⟩

instance : OrderedAddCommGroup Surreal where
  add := (· + ·)
  add_assoc := by rintro ⟨_⟩ ⟨_⟩ ⟨_⟩; exact Quotient.sound add_assoc_equiv
  zero := 0
  zero_add := by rintro ⟨_⟩; exact Quotient.sound (zero_add_equiv a)
  add_zero := by rintro ⟨_⟩; exact Quotient.sound (add_zero_equiv a)
  neg := Neg.neg
  add_left_neg := by rintro ⟨_⟩; exact Quotient.sound (add_left_neg_equiv a)
  add_comm := by rintro ⟨_⟩ ⟨_⟩; exact Quotient.sound add_comm_equiv
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl := by rintro ⟨_⟩; apply @le_rfl SetTheory.PGame
  le_trans := by rintro ⟨_⟩ ⟨_⟩ ⟨_⟩; apply @le_trans SetTheory.PGame
  lt_iff_le_not_le := by rintro ⟨_, ox⟩ ⟨_, oy⟩; apply @lt_iff_le_not_le SetTheory.PGame
  le_antisymm := by rintro ⟨_⟩ ⟨_⟩ h₁ h₂; exact Quotient.sound ⟨h₁, h₂⟩
  add_le_add_left := by rintro ⟨_⟩ ⟨_⟩ hx ⟨_⟩; exact @add_le_add_left SetTheory.PGame _ _ _ _ _ hx _

noncomputable instance : LinearOrderedAddCommGroup Surreal :=
  {
    Surreal.orderedAddCommGroup with
    le_total := by
      rintro ⟨⟨x, ox⟩⟩ ⟨⟨y, oy⟩⟩ <;> classical skip <;>
        exact or_iff_not_imp_left.2 fun h => (SetTheory.PGame.not_le.1 h).le oy ox
    decidableLe := Classical.decRel _ }

instance : AddMonoidWithOne Surreal :=
  AddMonoidWithOne.unary

#print Surreal.toGame /-
/-- Casts a `surreal` number into a `game`. -/
def toGame : Surreal →+o SetTheory.Game
    where
  toFun := lift (fun x _ => ⟦x⟧) fun x y ox oy => Quot.sound
  map_zero' := rfl
  map_add' := by rintro ⟨_, _⟩ ⟨_, _⟩; rfl
  monotone' := by rintro ⟨_, _⟩ ⟨_, _⟩; exact id
#align surreal.to_game Surreal.toGame
-/

#print Surreal.zero_toGame /-
theorem zero_toGame : toGame 0 = 0 :=
  rfl
#align surreal.zero_to_game Surreal.zero_toGame
-/

#print Surreal.one_toGame /-
@[simp]
theorem one_toGame : toGame 1 = 1 :=
  rfl
#align surreal.one_to_game Surreal.one_toGame
-/

#print Surreal.nat_toGame /-
@[simp]
theorem nat_toGame : ∀ n : ℕ, toGame n = n :=
  map_natCast' _ one_toGame
#align surreal.nat_to_game Surreal.nat_toGame
-/

theorem upperBound_numeric {ι : Type u} {f : ι → SetTheory.PGame.{u}} (H : ∀ i, (f i).Numeric) :
    (SetTheory.PGame.upperBound f).Numeric :=
  SetTheory.PGame.numeric_of_isEmpty_rightMoves _ fun i => (H _).moveLeft _
#align surreal.upper_bound_numeric Surreal.upperBound_numeric

theorem lowerBound_numeric {ι : Type u} {f : ι → SetTheory.PGame.{u}} (H : ∀ i, (f i).Numeric) :
    (SetTheory.PGame.lowerBound f).Numeric :=
  SetTheory.PGame.numeric_of_isEmpty_leftMoves _ fun i => (H _).moveRight _
#align surreal.lower_bound_numeric Surreal.lowerBound_numeric

/-- A small set `s` of surreals is bounded above. -/
theorem bddAbove_of_small (s : Set Surreal.{u}) [Small.{u} s] : BddAbove s :=
  by
  let g := Subtype.val ∘ Quotient.out ∘ Subtype.val ∘ (equivShrink s).symm
  refine' ⟨mk (upper_bound g) (upper_bound_numeric fun i => Subtype.prop _), fun i hi => _⟩
  rw [← Quotient.out_eq i]
  show i.out.1 ≤ _
  simpa [g] using le_upper_bound g (equivShrink s ⟨i, hi⟩)
#align surreal.bdd_above_of_small Surreal.bddAbove_of_small

/-- A small set `s` of surreals is bounded below. -/
theorem bddBelow_of_small (s : Set Surreal.{u}) [Small.{u} s] : BddBelow s :=
  by
  let g := Subtype.val ∘ Quotient.out ∘ Subtype.val ∘ (equivShrink s).symm
  refine' ⟨mk (lower_bound g) (lower_bound_numeric fun i => Subtype.prop _), fun i hi => _⟩
  rw [← Quotient.out_eq i]
  show _ ≤ i.out.1
  simpa [g] using lower_bound_le g (equivShrink s ⟨i, hi⟩)
#align surreal.bdd_below_of_small Surreal.bddBelow_of_small

end Surreal

open Surreal

namespace Ordinal

#print Ordinal.toSurreal /-
/-- Converts an ordinal into the corresponding surreal. -/
noncomputable def toSurreal : Ordinal ↪o Surreal
    where
  toFun o := mk _ (SetTheory.PGame.numeric_toPGame o)
  inj' a b h := toPGame_equiv_iff.1 (Quotient.exact h)
  map_rel_iff' := @toPGame_le_iff
#align ordinal.to_surreal Ordinal.toSurreal
-/

end Ordinal

