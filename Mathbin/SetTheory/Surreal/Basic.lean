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
Surreal numbers inherit the relations `≤` and `<` from games, and these relations satisfy the axioms
of a partial order (recall that `x < y ↔ x ≤ y ∧ ¬ y ≤ x` did not hold for games).

## Algebraic operations
We show that the surreals form a linear ordered commutative group.

One can also map all the ordinals into the surreals!

### Multiplication of surreal numbers
The definition of multiplication for surreal numbers is surprisingly difficult and is currently
missing in the library. A sample proof can be found in Theorem 3.8 in the second reference below.
The difficulty lies in the length of the proof and the number of theorems that need to proven
simultaneously. This will make for a fun and challenging project.

## References
* [Conway, *On numbers and games*][conway2001]
* [Schleicher, Stoll, *An introduction to Conway's games and numbers*][schleicher_stoll]
-/


universe u

-- mathport name: «expr ≈ »
local infixl:0 " ≈ " => Pgame.Equiv

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

theorem lt_asymm {x y : Pgame} (ox : Numeric x) (oy : Numeric y) : x < y → ¬y < x := by
  refine' numeric_rec (fun xl xr xL xR hx oxl oxr IHxl IHxr => _) x ox y oy
  refine' numeric_rec fun yl yr yL yR hy oyl oyr IHyl IHyr => _
  rw [mk_lt_mk, mk_lt_mk]
  rintro (⟨i, h₁⟩ | ⟨j, h₁⟩) (⟨i, h₂⟩ | ⟨j, h₂⟩)
  · exact IHxl _ _ (oyl _) (lt_of_le_mk h₁) (lt_of_le_mk h₂)
    
  · exact not_ltₓ.2 (le_transₓ h₂ h₁) (hy _ _)
    
  · exact not_ltₓ.2 (le_transₓ h₁ h₂) (hx _ _)
    
  · exact IHxr _ _ (oyr _) (lt_of_mk_le h₁) (lt_of_mk_le h₂)
    

theorem le_of_lt {x y : Pgame} (ox : Numeric x) (oy : Numeric y) (h : x < y) : x ≤ y :=
  not_lt.1 (lt_asymm ox oy h)

/-- On numeric pre-games, `<` and `≤` satisfy the axioms of a partial order (even though they
don't on all pre-games). -/
theorem lt_iff_le_not_le {x y : Pgame} (ox : Numeric x) (oy : Numeric y) : x < y ↔ x ≤ y ∧ ¬y ≤ x :=
  ⟨fun h => ⟨le_of_lt ox oy h, not_le.2 h⟩, fun h => not_le.1 h.2⟩

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
  | ⟨l, r, L, R⟩, o => ⟨fun j i => lt_iff_neg_gt.1 (o.1 i j), fun j => (o.2.2 j).neg, fun i => (o.2.1 i).neg⟩

/-- For the `<` version, see `pgame.move_left_lt`. -/
theorem Numeric.move_left_le {x : Pgame} (o : Numeric x) (i : x.LeftMoves) : x.moveLeft i ≤ x :=
  le_of_lt (o.moveLeft i) o (Pgame.move_left_lt i)

/-- For the `<` version, see `pgame.lt_move_right`. -/
theorem Numeric.le_move_right {x : Pgame} (o : Numeric x) (j : x.RightMoves) : x ≤ x.moveRight j :=
  le_of_lt o (o.moveRight j) (Pgame.lt_move_right j)

theorem add_lt_add {w x y z : Pgame.{u}} (oy : Numeric y) (oz : Numeric z) (hwx : w < x) (hyz : y < z) :
    w + y < x + z := by
  rw [lt_def_le] at *
  rcases hwx with (⟨ix, hix⟩ | ⟨jw, hjw⟩) <;> rcases hyz with (⟨iz, hiz⟩ | ⟨jy, hjy⟩)
  · left
    use (left_moves_add x z).symm (Sum.inl ix)
    simp only [add_move_left_inl]
    calc w + y ≤ move_left x ix + y := add_le_add_right hix _ _ ≤ move_left x ix + move_left z iz :=
        add_le_add_left hiz _ _ ≤ move_left x ix + z := add_le_add_left (oz.move_left_le iz) _
    
  · left
    use (left_moves_add x z).symm (Sum.inl ix)
    simp only [add_move_left_inl]
    calc w + y ≤ move_left x ix + y := add_le_add_right hix _ _ ≤ move_left x ix + move_right y jy :=
        add_le_add_left (oy.le_move_right jy) _ _ ≤ move_left x ix + z := add_le_add_left hjy _
    
  · right
    use (right_moves_add w y).symm (Sum.inl jw)
    simp only [add_move_right_inl]
    calc move_right w jw + y ≤ x + y := add_le_add_right hjw _ _ ≤ x + move_left z iz :=
        add_le_add_left hiz _ _ ≤ x + z := add_le_add_left (oz.move_left_le iz) _
    
  · right
    use (right_moves_add w y).symm (Sum.inl jw)
    simp only [add_move_right_inl]
    calc move_right w jw + y ≤ x + y := add_le_add_right hjw _ _ ≤ x + move_right y jy :=
        add_le_add_left (oy.le_move_right jy) _ _ ≤ x + z := add_le_add_left hjy _
    

theorem Numeric.add : ∀ {x y : Pgame} ox : Numeric x oy : Numeric y, Numeric (x + y)
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩, ox, oy =>
    ⟨by
      rintro (ix | iy) (jx | jy)
      · show xL ix + ⟨yl, yr, yL, yR⟩ < xR jx + ⟨yl, yr, yL, yR⟩
        exact add_lt_add_right (ox.1 ix jx) _
        
      · show xL ix + ⟨yl, yr, yL, yR⟩ < ⟨xl, xr, xL, xR⟩ + yR jy
        exact add_lt_add oy (oy.move_right jy) (Pgame.lt_mk ix) (Pgame.mk_lt jy)
        
      · -- show ⟨xl, xr, xL, xR⟩ + yL iy < xR jx + ⟨yl, yr, yL, yR⟩, -- fails?
        exact add_lt_add (oy.move_left iy) oy (Pgame.mk_lt jx) (Pgame.lt_mk iy)
        
      · -- show ⟨xl, xr, xL, xR⟩ + yL iy < ⟨xl, xr, xL, xR⟩ + yR jy, -- fails?
        exact @add_lt_add_left Pgame _ _ _ _ _ (oy.1 iy jy) ⟨xl, xr, xL, xR⟩
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

/-- The pre-game omega is numeric. -/
theorem numeric_omega : Numeric omega :=
  ⟨by
    rintro ⟨⟩ ⟨⟩, fun i => numeric_nat i.down, by
    rintro ⟨⟩⟩

/-- The pre-game `half` is numeric. -/
theorem numeric_half : Numeric half := by
  constructor
  · rintro ⟨⟩ ⟨⟩
    exact zero_lt_one
    
  constructor <;> rintro ⟨⟩
  · exact numeric_zero
    
  · exact numeric_one
    

theorem half_add_half_equiv_one : half + half ≈ 1 := by
  constructor <;> rw [le_def] <;> constructor
  · rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
    · right
      use Sum.inr PUnit.unit
      calc
        ((half + half).moveLeft (Sum.inl PUnit.unit)).moveRight (Sum.inr PUnit.unit) =
            (half.move_left PUnit.unit + half).moveRight (Sum.inr PUnit.unit) :=
          by
          fconstructor _ = (0 + half).moveRight (Sum.inr PUnit.unit) := by
          fconstructor _ ≈ 1 := zero_add_equiv 1_ ≤ 1 := Pgame.le_refl 1
      
    · right
      use Sum.inl PUnit.unit
      calc
        ((half + half).moveLeft (Sum.inr PUnit.unit)).moveRight (Sum.inl PUnit.unit) =
            (half + half.move_left PUnit.unit).moveRight (Sum.inl PUnit.unit) :=
          by
          fconstructor _ = (half + 0).moveRight (Sum.inl PUnit.unit) := by
          fconstructor _ ≈ 1 := add_zero_equiv 1_ ≤ 1 := Pgame.le_refl 1
      
    
  · rintro ⟨⟩
    
  · rintro ⟨⟩
    left
    use Sum.inl PUnit.unit
    calc 0 ≤ half := le_of_ltₓ numeric_zero numeric_half Pgame.zero_lt_half _ ≈ 0 + half :=
        (zero_add_equiv half).symm _ = (half + half).moveLeft (Sum.inl PUnit.unit) := by
        fconstructor
    
  · rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩) <;> left
    · exact ⟨Sum.inr PUnit.unit, le_of_le_of_equiv (Pgame.le_refl _) (add_zero_equiv _).symm⟩
      
    · exact ⟨Sum.inl PUnit.unit, le_of_le_of_equiv (Pgame.le_refl _) (zero_add_equiv _).symm⟩
      
    

end Pgame

/-- The equivalence on numeric pre-games. -/
def Surreal.Equiv (x y : { x // Pgame.Numeric x }) : Prop :=
  x.1.Equiv y.1

instance Surreal.setoid : Setoidₓ { x // Pgame.Numeric x } :=
  ⟨fun x y => x.1.Equiv y.1, fun x => Pgame.equiv_refl _, fun x y => Pgame.equiv_symm, fun x y z => Pgame.equiv_trans⟩

/-- The type of surreal numbers. These are the numeric pre-games quotiented
by the equivalence relation `x ≈ y ↔ x ≤ y ∧ y ≤ x`. In the quotient,
the order becomes a total order. -/
def Surreal :=
  Quotientₓ Surreal.setoid

namespace Surreal

open Pgame

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
  lift (fun x ox => lift (fun y oy => f x y ox oy) fun y₁ y₂ oy₁ oy₂ h => H _ _ _ _ (equiv_refl _) h)
    fun x₁ x₂ ox₁ ox₂ h => funext <| Quotientₓ.ind fun ⟨y, oy⟩ => H _ _ _ _ h (equiv_refl _)

/-- The relation `x ≤ y` on surreals. -/
def Le : Surreal → Surreal → Prop :=
  lift₂ (fun x y _ _ => x ≤ y) fun x₁ y₁ x₂ y₂ _ _ _ _ hx hy => propext (le_congr hx hy)

/-- The relation `x < y` on surreals. -/
def Lt : Surreal → Surreal → Prop :=
  lift₂ (fun x y _ _ => x < y) fun x₁ y₁ x₂ y₂ _ _ _ _ hx hy => propext (lt_congr hx hy)

theorem not_le : ∀ {x y : Surreal}, ¬Le x y ↔ Lt y x := by
  rintro ⟨⟨x, ox⟩⟩ ⟨⟨y, oy⟩⟩ <;> exact not_leₓ

/-- Addition on surreals is inherited from pre-game addition:
the sum of `x = {xL | xR}` and `y = {yL | yR}` is `{xL + y, x + yL | xR + y, x + yR}`. -/
def add : Surreal → Surreal → Surreal :=
  Surreal.lift₂ (fun oy => ⟦⟨x + y, ox.add oy⟩⟧) fun x₁ y₁ x₂ y₂ _ _ _ _ hx hy =>
    Quotientₓ.sound (Pgame.add_congr hx hy)

/-- Negation for surreal numbers is inherited from pre-game negation:
the negation of `{L | R}` is `{-R | -L}`. -/
def neg : Surreal → Surreal :=
  Surreal.lift (fun x ox => ⟦⟨-x, ox.neg⟩⟧) fun _ _ _ _ a => Quotientₓ.sound (Pgame.neg_congr a)

instance : LE Surreal :=
  ⟨Le⟩

instance : LT Surreal :=
  ⟨Lt⟩

instance : Add Surreal :=
  ⟨add⟩

instance : Neg Surreal :=
  ⟨neg⟩

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
    rfl
  le_trans := by
    rintro ⟨_⟩ ⟨_⟩ ⟨_⟩
    exact Pgame.le_trans
  lt_iff_le_not_le := by
    rintro ⟨_, ox⟩ ⟨_, oy⟩
    exact Pgame.lt_iff_le_not_le ox oy
  le_antisymm := by
    rintro ⟨_⟩ ⟨_⟩ h₁ h₂
    exact Quotientₓ.sound ⟨h₁, h₂⟩
  add_le_add_left := by
    rintro ⟨_⟩ ⟨_⟩ hx ⟨_⟩
    exact @add_le_add_left Pgame _ _ _ _ _ hx _

noncomputable instance : LinearOrderedAddCommGroup Surreal :=
  { Surreal.orderedAddCommGroup with
    le_total := by
      rintro ⟨⟨x, ox⟩⟩ ⟨⟨y, oy⟩⟩ <;>
        classical <;> exact or_iff_not_imp_left.2 fun h => le_of_ltₓ oy ox (Pgame.not_le.1 h),
    decidableLe := Classical.decRel _ }

-- We conclude with some ideas for further work on surreals; these would make fun projects.
-- TODO define the inclusion of groups `surreal → game`
-- TODO define the field structure on the surreals
end Surreal

