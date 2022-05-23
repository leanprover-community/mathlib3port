/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Scott Morrison
-/
import Mathbin.SetTheory.Game.Pgame

/-!
# Surreal numbers

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

## References

* [Conway, *On numbers and games*][conway2001]
* [Schleicher, Stoll, *An introduction to Conway's games and numbers*][schleicher_stoll]
-/


universe u

-- mathport name: «expr ≈ »
local infixl:0 " ≈ " => Pgame.Equiv

-- mathport name: «expr ⧏ »
local infixl:50 " ⧏ " => Pgame.Lf

namespace Pgame

/-- A pre-game is numeric if everything in the L set is less than everything in the R set,
and all the elements of L and R are also numeric. -/
def Numeric : Pgame → Prop
  | ⟨l, r, L, R⟩ => (∀ i j, L i < R j) ∧ (∀ i, numeric (L i)) ∧ ∀ i, numeric (R i)

theorem numeric_def (x : Pgame) :
    Numeric x ↔ (∀ i j, x.moveLeft i < x.moveRight j) ∧ (∀ i, Numeric (x.moveLeft i)) ∧ ∀ i, Numeric (x.moveRight i) :=
  by
  cases x
  rfl

theorem Numeric.left_lt_right {x : Pgame} (o : Numeric x) (i : x.LeftMoves) (j : x.RightMoves) :
    x.moveLeft i < x.moveRight j := by
  cases' x with xl xr xL xR
  exact o.1 i j

theorem Numeric.move_left {x : Pgame} (o : Numeric x) (i : x.LeftMoves) : Numeric (x.moveLeft i) := by
  cases' x with xl xr xL xR
  exact o.2.1 i

theorem Numeric.move_right {x : Pgame} (o : Numeric x) (j : x.RightMoves) : Numeric (x.moveRight j) := by
  cases' x with xl xr xL xR
  exact o.2.2 j

@[elab_as_eliminator]
theorem numeric_rec {C : Pgame → Prop}
    (H :
      ∀ l r L : l → Pgame R : r → Pgame,
        (∀ i j, L i < R j) →
          (∀ i, Numeric (L i)) → (∀ i, Numeric (R i)) → (∀ i, C (L i)) → (∀ i, C (R i)) → C ⟨l, r, L, R⟩) :
    ∀ x, Numeric x → C x
  | ⟨l, r, L, R⟩, ⟨h, hl, hr⟩ => H _ _ _ _ h hl hr (fun i => numeric_rec _ (hl i)) fun i => numeric_rec _ (hr i)

theorem lf_asymm {x y : Pgame} (ox : Numeric x) (oy : Numeric y) : x ⧏ y → ¬y ⧏ x := by
  refine' numeric_rec (fun xl xr xL xR hx oxl oxr IHxl IHxr => _) x ox y oy
  refine' numeric_rec fun yl yr yL yR hy oyl oyr IHyl IHyr => _
  rw [mk_lf_mk, mk_lf_mk]
  rintro (⟨i, h₁⟩ | ⟨j, h₁⟩) (⟨i, h₂⟩ | ⟨j, h₂⟩)
  · exact IHxl _ _ (oyl _) (move_left_lf_of_le _ h₁) (move_left_lf_of_le _ h₂)
    
  · exact not_lf.2 (le_transₓ h₂ h₁) (lf_of_lt (hy _ _))
    
  · exact not_lf.2 (le_transₓ h₁ h₂) (lf_of_lt (hx _ _))
    
  · exact IHxr _ _ (oyr _) (lf_move_right_of_le _ h₁) (lf_move_right_of_le _ h₂)
    

theorem le_of_lf {x y : Pgame} (ox : Numeric x) (oy : Numeric y) (h : x ⧏ y) : x ≤ y :=
  not_lf.1 (lf_asymm ox oy h)

theorem lt_of_lf {x y : Pgame} (ox : Numeric x) (oy : Numeric y) (h : x ⧏ y) : x < y :=
  (lt_or_fuzzy_of_lf h).resolve_right (not_fuzzy_of_le (le_of_lf ox oy h))

theorem lf_iff_lt {x y : Pgame} (ox : Numeric x) (oy : Numeric y) : x ⧏ y ↔ x < y :=
  ⟨lt_of_lf ox oy, lf_of_lt⟩

theorem not_fuzzy {x y : Pgame} (ox : Numeric x) (oy : Numeric y) : ¬Fuzzy x y := fun h =>
  not_lf.2 (le_of_lf ox oy (lf_of_fuzzy h)) h.2

theorem numeric_zero : Numeric 0 :=
  ⟨by
    rintro ⟨⟩ ⟨⟩,
    ⟨by
      rintro ⟨⟩, by
      rintro ⟨⟩⟩⟩

theorem numeric_one : Numeric 1 :=
  ⟨by
    rintro ⟨⟩ ⟨⟩,
    ⟨fun x => numeric_zero, by
      rintro ⟨⟩⟩⟩

theorem Numeric.neg : ∀ {x : Pgame} o : Numeric x, Numeric (-x)
  | ⟨l, r, L, R⟩, o => ⟨fun j i => neg_lt_iff.2 (o.1 i j), fun j => (o.2.2 j).neg, fun i => (o.2.1 i).neg⟩

theorem Numeric.move_left_lt {x : Pgame} (o : Numeric x) i : x.moveLeft i < x :=
  lt_of_lf (o.moveLeft i) o (Pgame.move_left_lf i)

theorem Numeric.move_left_le {x : Pgame} (o : Numeric x) i : x.moveLeft i ≤ x :=
  (o.move_left_lt i).le

theorem Numeric.lt_move_right {x : Pgame} (o : Numeric x) j : x < x.moveRight j :=
  lt_of_lf o (o.moveRight j) (Pgame.lf_move_right j)

theorem Numeric.le_move_right {x : Pgame} (o : Numeric x) j : x ≤ x.moveRight j :=
  (o.lt_move_right j).le

-- TODO: this can be generalized to `add_lf_add_of_lf_of_lt`, which doesn't depend on any `numeric`
-- hypotheses.
theorem add_lf_add {w x y z : Pgame.{u}} (oy : Numeric y) (oz : Numeric z) (hwx : w ⧏ x) (hyz : y ⧏ z) :
    w + y ⧏ x + z := by
  rw [lf_iff_forall_le] at *
  rcases hwx with (⟨ix, hix⟩ | ⟨jw, hjw⟩) <;> rcases hyz with (⟨iz, hiz⟩ | ⟨jy, hjy⟩)
  · refine' Or.inl ⟨to_left_moves_add (Sum.inl ix), _⟩
    rw [add_move_left_inl]
    calc w + y ≤ move_left x ix + y := add_le_add_right hix _ _ ≤ move_left x ix + move_left z iz :=
        add_le_add_left hiz _ _ ≤ move_left x ix + z := add_le_add_left (oz.move_left_le iz) _
    
  · refine' Or.inl ⟨to_left_moves_add (Sum.inl ix), _⟩
    rw [add_move_left_inl]
    calc w + y ≤ move_left x ix + y := add_le_add_right hix _ _ ≤ move_left x ix + move_right y jy :=
        add_le_add_left (oy.le_move_right jy) _ _ ≤ move_left x ix + z := add_le_add_left hjy _
    
  · refine' Or.inr ⟨to_right_moves_add (Sum.inl jw), _⟩
    rw [add_move_right_inl]
    calc move_right w jw + y ≤ x + y := add_le_add_right hjw _ _ ≤ x + move_left z iz :=
        add_le_add_left hiz _ _ ≤ x + z := add_le_add_left (oz.move_left_le iz) _
    
  · refine' Or.inr ⟨to_right_moves_add (Sum.inl jw), _⟩
    rw [add_move_right_inl]
    calc move_right w jw + y ≤ x + y := add_le_add_right hjw _ _ ≤ x + move_right y jy :=
        add_le_add_left (oy.le_move_right jy) _ _ ≤ x + z := add_le_add_left hjy _
    

theorem Numeric.add : ∀ {x y : Pgame} ox : Numeric x oy : Numeric y, Numeric (x + y)
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩, ox, oy =>
    ⟨by
      rintro (ix | iy) (jx | jy)
      · exact add_lt_add_right (ox.1 ix jx) _
        
      · apply
          lt_of_lf ((ox.move_left ix).add oy) (ox.add (oy.move_right jy))
            (add_lf_add oy (oy.move_right jy) (Pgame.move_left_lf ix) (Pgame.lf_move_right jy))
        
      · apply
          lt_of_lf (ox.add (oy.move_left iy)) ((ox.move_right jx).add oy)
            (add_lf_add (oy.move_left iy) oy (Pgame.lf_move_right jx) (Pgame.move_left_lf iy))
        
      · exact add_lt_add_left (oy.1 iy jy) ⟨xl, xr, xL, xR⟩
        ,
      by
      constructor
      · rintro (ix | iy)
        · exact (ox.move_left ix).add oy
          
        · exact ox.add (oy.move_left iy)
          
        
      · rintro (jx | jy)
        · apply (ox.move_right jx).add oy
          
        · apply ox.add (oy.move_right jy)
          
        ⟩

theorem Numeric.sub {x y : Pgame} (ox : Numeric x) (oy : Numeric y) : Numeric (x - y) :=
  ox.add oy.neg

/-- Pre-games defined by natural numbers are numeric. -/
theorem numeric_nat : ∀ n : ℕ, Numeric n
  | 0 => numeric_zero
  | n + 1 => (numeric_nat n).add numeric_one

/-- The pre-game `half` is numeric. -/
theorem numeric_half : Numeric half := by
  constructor
  · rintro ⟨⟩ ⟨⟩
    exact zero_lt_one
    
  constructor <;> rintro ⟨⟩
  · exact numeric_zero
    
  · exact numeric_one
    

end Pgame

/-- The equivalence on numeric pre-games. -/
def Surreal.Equiv (x y : { x // Pgame.Numeric x }) : Prop :=
  x.1.Equiv y.1

open Pgame

instance Surreal.setoid : Setoidₓ { x // Pgame.Numeric x } :=
  ⟨fun x y => x.1 ≈ y.1, fun x => equiv_refl x.1, fun x y => Pgame.equiv_symm, fun x y z => Pgame.equiv_trans⟩

/-- The type of surreal numbers. These are the numeric pre-games quotiented
by the equivalence relation `x ≈ y ↔ x ≤ y ∧ y ≤ x`. In the quotient,
the order becomes a total order. -/
def Surreal :=
  Quotientₓ Surreal.setoid

namespace Surreal

/-- Construct a surreal number from a numeric pre-game. -/
def mk (x : Pgame) (h : x.Numeric) : Surreal :=
  Quotientₓ.mk ⟨x, h⟩

instance : Zero Surreal where
  zero := ⟦⟨0, numeric_zero⟩⟧

instance : One Surreal where
  one := ⟦⟨1, numeric_one⟩⟧

instance : Inhabited Surreal :=
  ⟨0⟩

/-- Lift an equivalence-respecting function on pre-games to surreals. -/
def lift {α} (f : ∀ x, Numeric x → α) (H : ∀ {x y} hx : Numeric x hy : Numeric y, x.Equiv y → f x hx = f y hy) :
    Surreal → α :=
  Quotientₓ.lift (fun x : { x // Numeric x } => f x.1 x.2) fun x y => H x.2 y.2

/-- Lift a binary equivalence-respecting function on pre-games to surreals. -/
def lift₂ {α} (f : ∀ x y, Numeric x → Numeric y → α)
    (H :
      ∀ {x₁ y₁ x₂ y₂} ox₁ : Numeric x₁ oy₁ : Numeric y₁ ox₂ : Numeric x₂ oy₂ : Numeric y₂,
        x₁.Equiv x₂ → y₁.Equiv y₂ → f x₁ y₁ ox₁ oy₁ = f x₂ y₂ ox₂ oy₂) :
    Surreal → Surreal → α :=
  lift (fun x ox => lift (fun y oy => f x y ox oy) fun y₁ y₂ oy₁ oy₂ h => H _ _ _ _ equiv_rfl h) fun x₁ x₂ ox₁ ox₂ h =>
    funext <| Quotientₓ.ind fun ⟨y, oy⟩ => H _ _ _ _ h equiv_rfl

instance : LE Surreal :=
  ⟨lift₂ (fun x y _ _ => x ≤ y) fun x₁ y₁ x₂ y₂ _ _ _ _ hx hy => propext (le_congr hx hy)⟩

instance : LT Surreal :=
  ⟨lift₂ (fun x y _ _ => x < y) fun x₁ y₁ x₂ y₂ _ _ _ _ hx hy => propext (lt_congr hx hy)⟩

/-- Addition on surreals is inherited from pre-game addition:
the sum of `x = {xL | xR}` and `y = {yL | yR}` is `{xL + y, x + yL | xR + y, x + yR}`. -/
instance : Add Surreal :=
  ⟨Surreal.lift₂ (fun oy => ⟦⟨x + y, ox.add oy⟩⟧) fun x₁ y₁ x₂ y₂ _ _ _ _ hx hy =>
      Quotientₓ.sound (Pgame.add_congr hx hy)⟩

/-- Negation for surreal numbers is inherited from pre-game negation:
the negation of `{L | R}` is `{-R | -L}`. -/
instance : Neg Surreal :=
  ⟨Surreal.lift (fun x ox => ⟦⟨-x, ox.neg⟩⟧) fun _ _ _ _ a => Quotientₓ.sound (Pgame.neg_congr a)⟩

instance : OrderedAddCommGroup Surreal where
  add := (· + ·)
  add_assoc := by
    rintro ⟨_⟩ ⟨_⟩ ⟨_⟩
    exact Quotientₓ.sound add_assoc_equiv
  zero := 0
  zero_add := by
    rintro ⟨_⟩
    exact Quotientₓ.sound (Pgame.zero_add_equiv a)
  add_zero := by
    rintro ⟨_⟩
    exact Quotientₓ.sound (Pgame.add_zero_equiv a)
  neg := Neg.neg
  add_left_neg := by
    rintro ⟨_⟩
    exact Quotientₓ.sound (Pgame.add_left_neg_equiv a)
  add_comm := by
    rintro ⟨_⟩ ⟨_⟩
    exact Quotientₓ.sound Pgame.add_comm_equiv
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl := by
    rintro ⟨_⟩
    apply @le_rfl Pgame
  le_trans := by
    rintro ⟨_⟩ ⟨_⟩ ⟨_⟩
    apply @le_transₓ Pgame
  lt_iff_le_not_le := by
    rintro ⟨_, ox⟩ ⟨_, oy⟩
    exact lt_iff_le_not_leₓ
  le_antisymm := by
    rintro ⟨_⟩ ⟨_⟩ h₁ h₂
    exact Quotientₓ.sound ⟨h₁, h₂⟩
  add_le_add_left := by
    rintro ⟨_⟩ ⟨_⟩ hx ⟨_⟩
    exact @add_le_add_left Pgame _ _ _ _ _ hx _

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: classical ... #[[]]
noncomputable instance : LinearOrderedAddCommGroup Surreal :=
  { Surreal.orderedAddCommGroup with
    le_total := by
      rintro ⟨⟨x, ox⟩⟩ ⟨⟨y, oy⟩⟩ <;>
        classical <;> exact or_iff_not_imp_left.2 fun h => le_of_lf oy ox (Pgame.not_le.1 h),
    decidableLe := Classical.decRel _ }

-- We conclude with some ideas for further work on surreals; these would make fun projects.
-- TODO define the inclusion of groups `surreal → game`
-- TODO define the field structure on the surreals
end Surreal

