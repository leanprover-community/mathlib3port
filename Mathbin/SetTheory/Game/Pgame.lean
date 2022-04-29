/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Isabel Longbottom, Scott Morrison
-/
import Mathbin.Data.Fin.Basic
import Mathbin.Data.Nat.Cast
import Mathbin.Logic.Embedding

/-!
# Combinatorial (pre-)games.

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

Pregames have both a `≤` and a `<` relation, which are related in quite a subtle way. In particular,
it is worth noting that in Lean's (perhaps unfortunate?) definition of a `preorder`, we have
`lt_iff_le_not_le : ∀ a b : α, a < b ↔ (a ≤ b ∧ ¬ b ≤ a)`, but this is _not_ satisfied by the usual
`≤` and `<` relations on pregames. (It is satisfied once we restrict to the surreal numbers.) In
particular, `<` is not transitive; there is an example below showing `0 < star ∧ star < 0`.

We do have
```
theorem not_le {x y : pgame} : ¬ x ≤ y ↔ y < x := ...
theorem not_lt {x y : pgame} : ¬ x < y ↔ y ≤ x := ...
```

The statement `0 ≤ x` means that Left has a good response to any move by Right; in particular, the
theorem `zero_le` below states
```
0 ≤ x ↔ ∀ j : x.right_moves, ∃ i : (x.move_right j).left_moves, 0 ≤ (x.move_right j).move_left i
```
On the other hand the statement `0 < x` means that Left has a good move right now; in particular the
theorem `zero_lt` below states
```
0 < x ↔ ∃ i : left_moves x, ∀ j : right_moves (x.move_left i), 0 < (x.move_left i).move_right j
```

The theorems `le_def`, `lt_def`, give a recursive characterisation of each relation, in terms of
themselves two moves later. The theorems `le_def_lt` and `lt_def_lt` give recursive
characterisations of each relation in terms of the other relation one move later.

We define an equivalence relation `equiv p q ↔ p ≤ q ∧ q ≤ p`. Later, games will be defined as the
quotient by this relation.

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


open Function

universe u

/-- The type of pre-games, before we have quotiented
  by extensionality. In ZFC, a combinatorial game is constructed from
  two sets of combinatorial games that have been constructed at an earlier
  stage. To do this in type theory, we say that a pre-game is built
  inductively from two families of pre-games indexed over any type
  in Type u. The resulting type `pgame.{u}` lives in `Type (u+1)`,
  reflecting that it is a proper class in ZFC. -/
inductive Pgame : Type (u + 1)
  | mk : ∀ α β : Type u, (α → Pgame) → (β → Pgame) → Pgame

namespace Pgame

/-- Construct a pre-game from list of pre-games describing the available moves for Left and Right.
-/
-- TODO provide some API describing the interaction with
-- `left_moves`, `right_moves`, `move_left` and `move_right` below.
-- TODO define this at the level of games, as well, and perhaps also for finsets of games.
def ofLists (L R : List Pgame.{0}) : Pgame.{0} :=
  Pgame.mk (Finₓ L.length) (Finₓ R.length) (fun i => L.nthLe i i.is_lt) fun j => R.nthLe j.val j.is_lt

/-- The indexing type for allowable moves by Left. -/
def LeftMoves : Pgame → Type u
  | mk l _ _ _ => l

/-- The indexing type for allowable moves by Right. -/
def RightMoves : Pgame → Type u
  | mk _ r _ _ => r

/-- The new game after Left makes an allowed move. -/
def moveLeft : ∀ g : Pgame, LeftMoves g → Pgame
  | mk l _ L _ => L

/-- The new game after Right makes an allowed move. -/
def moveRight : ∀ g : Pgame, RightMoves g → Pgame
  | mk _ r _ R => R

@[simp]
theorem left_moves_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : Pgame).LeftMoves = xl :=
  rfl

@[simp]
theorem move_left_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : Pgame).moveLeft = xL :=
  rfl

@[simp]
theorem right_moves_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : Pgame).RightMoves = xr :=
  rfl

@[simp]
theorem move_right_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : Pgame).moveRight = xR :=
  rfl

/-- A variant of `pgame.rec_on` expressed in terms of `pgame.move_left` and `pgame.move_right`.

Both this and `pgame.rec_on` describe Conway induction on games. -/
@[elab_as_eliminator]
def moveRecOn {C : Pgame → Sort _} (x : Pgame)
    (IH : ∀ y : Pgame, (∀ i, C (y.moveLeft i)) → (∀ j, C (y.moveRight j)) → C y) : C x :=
  x.recOn fun yl yr yL yR => IH (mk yl yr yL yR)

/-- `is_option x y` means that `x` is either a left or right option for `y`. -/
@[mk_iff]
inductive IsOption : Pgame → Pgame → Prop
  | move_left {x : Pgame} (i : x.LeftMoves) : is_option (x.moveLeft i) x
  | move_right {x : Pgame} (i : x.RightMoves) : is_option (x.moveRight i) x

theorem IsOption.mk_left {xl xr : Type u} (xL : xl → Pgame) (xR : xr → Pgame) (i : xl) :
    (xL i).IsOption (mk xl xr xL xR) :=
  @IsOption.move_left (mk _ _ _ _) i

theorem IsOption.mk_right {xl xr : Type u} (xL : xl → Pgame) (xR : xr → Pgame) (i : xr) :
    (xR i).IsOption (mk xl xr xL xR) :=
  @IsOption.move_right (mk _ _ _ _) i

theorem wf_is_option : WellFounded IsOption :=
  ⟨fun x =>
    (moveRecOn x) fun x IHl IHr =>
      (Acc.intro x) fun y h => by
        induction' h with _ i _ j
        · exact IHl i
          
        · exact IHr j
          ⟩

/-- `subsequent p q` says that `p` can be obtained by playing
  some nonempty sequence of moves from `q`. -/
inductive Subsequent : Pgame → Pgame → Prop
  | left : ∀ x : Pgame i : x.LeftMoves, subsequent (x.moveLeft i) x
  | right : ∀ x : Pgame j : x.RightMoves, subsequent (x.moveRight j) x
  | trans : ∀ x y z : Pgame, subsequent x y → subsequent y z → subsequent x z

theorem wf_subsequent : WellFounded Subsequent :=
  ⟨fun x => by
    induction' x with l r L R IHl IHr
    refine' ⟨_, fun y h => _⟩
    generalize e : mk l r L R = x  at h
    induction' h with _ i _ j a b _ h1 h2 IH1 IH2 <;> subst e
    · apply IHl
      
    · apply IHr
      
    · exact Acc.invₓ (IH2 rfl) h1
      ⟩

instance : HasWellFounded Pgame where
  R := Subsequent
  wf := wf_subsequent

/-- A move by Left produces a subsequent game. (For use in pgame_wf_tac.) -/
theorem Subsequent.left_move {xl xr} {xL : xl → Pgame} {xR : xr → Pgame} {i : xl} :
    Subsequent (xL i) (mk xl xr xL xR) :=
  Subsequent.left (mk xl xr xL xR) i

/-- A move by Right produces a subsequent game. (For use in pgame_wf_tac.) -/
theorem Subsequent.right_move {xl xr} {xL : xl → Pgame} {xR : xr → Pgame} {j : xr} :
    Subsequent (xR j) (mk xl xr xL xR) :=
  Subsequent.right (mk xl xr xL xR) j

-- ././Mathport/Syntax/Translate/Basic.lean:915:4: warning: unsupported (TODO): `[tacs]
/-- A local tactic for proving well-foundedness of recursive definitions involving pregames. -/
unsafe def pgame_wf_tac :=
  sorry

/-- The pre-game `zero` is defined by `0 = { | }`. -/
instance : Zero Pgame :=
  ⟨⟨Pempty, Pempty, Pempty.elimₓ, Pempty.elimₓ⟩⟩

@[simp]
theorem zero_left_moves : (0 : Pgame).LeftMoves = Pempty :=
  rfl

@[simp]
theorem zero_right_moves : (0 : Pgame).RightMoves = Pempty :=
  rfl

instance is_empty_zero_left_moves : IsEmpty (0 : Pgame).LeftMoves :=
  Pempty.is_empty

instance is_empty_zero_right_moves : IsEmpty (0 : Pgame).RightMoves :=
  Pempty.is_empty

instance : Inhabited Pgame :=
  ⟨0⟩

/-- The pre-game `one` is defined by `1 = { 0 | }`. -/
instance : One Pgame :=
  ⟨⟨PUnit, Pempty, fun _ => 0, Pempty.elimₓ⟩⟩

@[simp]
theorem one_left_moves : (1 : Pgame).LeftMoves = PUnit :=
  rfl

@[simp]
theorem one_move_left : (1 : Pgame).moveLeft PUnit.unit = 0 :=
  rfl

@[simp]
theorem one_right_moves : (1 : Pgame).RightMoves = Pempty :=
  rfl

instance is_empty_one_right_moves : IsEmpty (1 : Pgame).RightMoves :=
  Pempty.is_empty

/-- Define simultaneously by mutual induction the `<=` and `<`
  relation on pre-games. The ZFC definition says that `x = {xL | xR}`
  is less or equal to `y = {yL | yR}` if `∀ x₁ ∈ xL, x₁ < y`
  and `∀ y₂ ∈ yR, x < y₂`, where `x < y` is the same as `¬ y <= x`.
  This is a tricky induction because it only decreases one side at
  a time, and it also swaps the arguments in the definition of `<`.
  The solution is to define `x < y` and `x <= y` simultaneously. -/
def leLt : ∀ x y : Pgame, Prop × Prop
  | mk xl xr xL xR,
    mk yl yr yL yR =>-- the orderings of the clauses here are carefully chosen so that
    --   and.left/or.inl refer to moves by Left, and
    --   and.right/or.inr refer to moves by Right.
    ((∀ i : xl, (le_lt (xL i) ⟨yl, yr, yL, yR⟩).2) ∧ ∀ j : yr, (le_lt ⟨xl, xr, xL, xR⟩ (yR j)).2,
      (∃ i : yl, (le_lt ⟨xl, xr, xL, xR⟩ (yL i)).1) ∨ ∃ j : xr, (le_lt (xR j) ⟨yl, yr, yL, yR⟩).1)

instance : LE Pgame :=
  ⟨fun x y => (leLt x y).1⟩

instance : LT Pgame :=
  ⟨fun x y => (leLt x y).2⟩

/-- Definition of `x ≤ y` on pre-games built using the constructor. -/
@[simp]
theorem mk_le_mk {xl xr xL xR yl yr yL yR} :
    (⟨xl, xr, xL, xR⟩ : Pgame) ≤ ⟨yl, yr, yL, yR⟩ ↔
      (∀ i, xL i < ⟨yl, yr, yL, yR⟩) ∧ ∀ j, (⟨xl, xr, xL, xR⟩ : Pgame) < yR j :=
  show (leLt _ _).1 ↔ _ by
    rw [le_lt]
    rfl

/-- Definition of `x ≤ y` on pre-games, in terms of `<` -/
theorem le_def_lt {x y : Pgame} :
    x ≤ y ↔ (∀ i : x.LeftMoves, x.moveLeft i < y) ∧ ∀ j : y.RightMoves, x < y.moveRight j := by
  cases x
  cases y
  rw [mk_le_mk]
  rfl

/-- Definition of `x < y` on pre-games built using the constructor. -/
@[simp]
theorem mk_lt_mk {xl xr xL xR yl yr yL yR} :
    (⟨xl, xr, xL, xR⟩ : Pgame) < ⟨yl, yr, yL, yR⟩ ↔
      (∃ i, (⟨xl, xr, xL, xR⟩ : Pgame) ≤ yL i) ∨ ∃ j, xR j ≤ ⟨yl, yr, yL, yR⟩ :=
  show (leLt _ _).2 ↔ _ by
    rw [le_lt]
    rfl

/-- Definition of `x < y` on pre-games, in terms of `≤` -/
theorem lt_def_le {x y : Pgame} :
    x < y ↔ (∃ i : y.LeftMoves, x ≤ y.moveLeft i) ∨ ∃ j : x.RightMoves, x.moveRight j ≤ y := by
  cases x
  cases y
  rw [mk_lt_mk]
  rfl

/-- The definition of `x ≤ y` on pre-games, in terms of `≤` two moves later. -/
theorem le_def {x y : Pgame} :
    x ≤ y ↔
      (∀ i : x.LeftMoves,
          (∃ i' : y.LeftMoves, x.moveLeft i ≤ y.moveLeft i') ∨
            ∃ j : (x.moveLeft i).RightMoves, (x.moveLeft i).moveRight j ≤ y) ∧
        ∀ j : y.RightMoves,
          (∃ i : (y.moveRight j).LeftMoves, x ≤ (y.moveRight j).moveLeft i) ∨
            ∃ j' : x.RightMoves, x.moveRight j' ≤ y.moveRight j :=
  by
  rw [le_def_lt]
  conv => lhs simp only [lt_def_le]

/-- The definition of `x < y` on pre-games, in terms of `<` two moves later. -/
theorem lt_def {x y : Pgame} :
    x < y ↔
      (∃ i : y.LeftMoves,
          (∀ i' : x.LeftMoves, x.moveLeft i' < y.moveLeft i) ∧
            ∀ j : (y.moveLeft i).RightMoves, x < (y.moveLeft i).moveRight j) ∨
        ∃ j : x.RightMoves,
          (∀ i : (x.moveRight j).LeftMoves, (x.moveRight j).moveLeft i < y) ∧
            ∀ j' : y.RightMoves, x.moveRight j < y.moveRight j' :=
  by
  rw [lt_def_le]
  conv => lhs simp only [le_def_lt]

/-- The definition of `x ≤ 0` on pre-games, in terms of `≤ 0` two moves later. -/
theorem le_zero {x : Pgame} :
    x ≤ 0 ↔ ∀ i : x.LeftMoves, ∃ j : (x.moveLeft i).RightMoves, (x.moveLeft i).moveRight j ≤ 0 := by
  rw [le_def]
  dsimp
  simp [forall_pempty, exists_pempty]

/-- The definition of `0 ≤ x` on pre-games, in terms of `0 ≤` two moves later. -/
theorem zero_le {x : Pgame} :
    0 ≤ x ↔ ∀ j : x.RightMoves, ∃ i : (x.moveRight j).LeftMoves, 0 ≤ (x.moveRight j).moveLeft i := by
  rw [le_def]
  dsimp
  simp [forall_pempty, exists_pempty]

/-- The definition of `x < 0` on pre-games, in terms of `< 0` two moves later. -/
theorem lt_zero {x : Pgame} :
    x < 0 ↔ ∃ j : x.RightMoves, ∀ i : (x.moveRight j).LeftMoves, (x.moveRight j).moveLeft i < 0 := by
  rw [lt_def]
  dsimp
  simp [forall_pempty, exists_pempty]

/-- The definition of `0 < x` on pre-games, in terms of `< x` two moves later. -/
theorem zero_lt {x : Pgame} :
    0 < x ↔ ∃ i : x.LeftMoves, ∀ j : (x.moveLeft i).RightMoves, 0 < (x.moveLeft i).moveRight j := by
  rw [lt_def]
  dsimp
  simp [forall_pempty, exists_pempty]

/-- Given a right-player-wins game, provide a response to any move by left. -/
noncomputable def rightResponse {x : Pgame} (h : x ≤ 0) (i : x.LeftMoves) : (x.moveLeft i).RightMoves :=
  Classical.some <| (le_zero.1 h) i

/-- Show that the response for right provided by `right_response`
    preserves the right-player-wins condition. -/
theorem right_response_spec {x : Pgame} (h : x ≤ 0) (i : x.LeftMoves) :
    (x.moveLeft i).moveRight (rightResponse h i) ≤ 0 :=
  Classical.some_spec <| (le_zero.1 h) i

/-- Given a left-player-wins game, provide a response to any move by right. -/
noncomputable def leftResponse {x : Pgame} (h : 0 ≤ x) (j : x.RightMoves) : (x.moveRight j).LeftMoves :=
  Classical.some <| (zero_le.1 h) j

/-- Show that the response for left provided by `left_response`
    preserves the left-player-wins condition. -/
theorem left_response_spec {x : Pgame} (h : 0 ≤ x) (j : x.RightMoves) :
    0 ≤ (x.moveRight j).moveLeft (leftResponse h j) :=
  Classical.some_spec <| (zero_le.1 h) j

theorem lt_of_le_mk {xl xr xL xR y i} : (⟨xl, xr, xL, xR⟩ : Pgame) ≤ y → xL i < y := by
  cases y
  rw [mk_le_mk]
  tauto

theorem lt_of_mk_le {x : Pgame} {yl yr yL yR i} : x ≤ ⟨yl, yr, yL, yR⟩ → x < yR i := by
  cases x
  rw [mk_le_mk]
  tauto

theorem mk_lt_of_le {xl xr xL xR y i} : (xR : xr → Pgame) i ≤ y → (⟨xl, xr, xL, xR⟩ : Pgame) < y := by
  cases y
  rw [mk_lt_mk]
  tauto

theorem lt_mk_of_le {x : Pgame} {yl yr : Type _} {yL : yl → Pgame} {yR i} : x ≤ yL i → x < ⟨yl, yr, yL, yR⟩ := by
  cases x
  rw [mk_lt_mk]
  exact fun h => Or.inl ⟨_, h⟩

theorem move_left_lt_of_le {x y : Pgame} {i} : x ≤ y → x.moveLeft i < y := by
  cases x
  exact lt_of_le_mk

theorem lt_move_right_of_le {x y : Pgame} {i} : x ≤ y → x < y.moveRight i := by
  cases y
  exact lt_of_mk_le

theorem lt_of_move_right_le {x y : Pgame} {i} : x.moveRight i ≤ y → x < y := by
  cases x
  rw [move_right_mk]
  exact mk_lt_of_le

theorem lt_of_le_move_left {x y : Pgame} {i} : x ≤ y.moveLeft i → x < y := by
  cases y
  rw [move_left_mk]
  exact lt_mk_of_le

private theorem not_le_lt {x y : Pgame} : (¬x ≤ y ↔ y < x) ∧ (¬x < y ↔ y ≤ x) := by
  induction' x with xl xr xL xR IHxl IHxr generalizing y
  induction' y with yl yr yL yR IHyl IHyr
  classical
  simp only [mk_le_mk, mk_lt_mk, not_and_distrib, not_or_distrib, not_forall, not_exists, and_comm, or_comm, IHxl, IHxr,
    IHyl, IHyr, iff_selfₓ, and_selfₓ]

@[simp]
theorem not_le {x y : Pgame} : ¬x ≤ y ↔ y < x :=
  not_le_lt.1

@[simp]
theorem not_lt {x y : Pgame} : ¬x < y ↔ y ≤ x :=
  not_le_lt.2

@[refl]
protected theorem le_refl : ∀ x : Pgame, x ≤ x
  | ⟨l, r, L, R⟩ => by
    rw [mk_le_mk] <;> exact ⟨fun i => lt_mk_of_le (le_reflₓ _), fun i => mk_lt_of_le (le_reflₓ _)⟩

protected theorem le_rfl {x : Pgame} : x ≤ x :=
  Pgame.le_refl x

protected theorem lt_irrefl (x : Pgame) : ¬x < x :=
  not_lt.2 (Pgame.le_refl _)

protected theorem ne_of_lt : ∀ {x y : Pgame}, x < y → x ≠ y
  | x, _, h, rfl => Pgame.lt_irrefl x h

/-- In general, `xL i ≤ x` isn't true. It is true however for `numeric` games, see
`numeric.move_left_le`. -/
theorem lt_mk {xl xr : Type u} {xL : xl → Pgame} {xR : xr → Pgame} i : xL i < mk xl xr xL xR :=
  lt_mk_of_le Pgame.le_rfl

/-- In general, `x ≤ xR i` isn't true. It is true however for `numeric` games, see
`numeric.move_right_le`. -/
theorem mk_lt {xl xr : Type u} {xL : xl → Pgame} {xR : xr → Pgame} i : mk xl xr xL xR < xR i :=
  mk_lt_of_le Pgame.le_rfl

/-- In general, `x.move_left i ≤ x` isn't true. It is true however for `numeric` games, see
`numeric.move_left_le`. -/
theorem move_left_lt {x : Pgame} i : x.moveLeft i < x :=
  move_left_lt_of_le Pgame.le_rfl

/-- In general, `x ≤ x.move_right i` isn't true. It is true however for `numeric` games, see
`numeric.move_right_le`. -/
theorem lt_move_right {x : Pgame} i : x < x.moveRight i :=
  lt_move_right_of_le Pgame.le_rfl

theorem le_trans_aux {xl xr} {xL : xl → Pgame} {xR : xr → Pgame} {yl yr} {yL : yl → Pgame} {yR : yr → Pgame} {zl zr}
    {zL : zl → Pgame} {zR : zr → Pgame}
    (h₁ : ∀ i, mk yl yr yL yR ≤ mk zl zr zL zR → mk zl zr zL zR ≤ xL i → mk yl yr yL yR ≤ xL i)
    (h₂ : ∀ i, zR i ≤ mk xl xr xL xR → mk xl xr xL xR ≤ mk yl yr yL yR → zR i ≤ mk yl yr yL yR) :
    mk xl xr xL xR ≤ mk yl yr yL yR → mk yl yr yL yR ≤ mk zl zr zL zR → mk xl xr xL xR ≤ mk zl zr zL zR := by
  simp only [mk_le_mk] at * <;>
    exact fun ⟨xLy, xyR⟩ ⟨yLz, yzR⟩ =>
      ⟨fun i => not_leₓ.1 fun h => not_ltₓ.2 (h₁ _ ⟨yLz, yzR⟩ h) (xLy _), fun i =>
        not_leₓ.1 fun h => not_ltₓ.2 (h₂ _ h ⟨xLy, xyR⟩) (yzR _)⟩

@[trans]
theorem le_trans {x y z : Pgame} : x ≤ y → y ≤ z → x ≤ z := by
  suffices ∀ {x y z : Pgame}, (x ≤ y → y ≤ z → x ≤ z) ∧ (y ≤ z → z ≤ x → y ≤ x) ∧ (z ≤ x → x ≤ y → z ≤ y) from this.1
  clear x y z
  intros
  induction' x with xl xr xL xR IHxl IHxr generalizing y z
  induction' y with yl yr yL yR IHyl IHyr generalizing z
  induction' z with zl zr zL zR IHzl IHzr
  exact
    ⟨le_trans_aux (fun i => (IHxl _).2.1) fun i => (IHzr _).2.2,
      le_trans_aux (fun i => (IHyl _).2.2) fun i => (IHxr _).1,
      le_trans_aux (fun i => (IHzl _).1) fun i => (IHyr _).2.1⟩

@[trans]
theorem lt_of_le_of_lt {x y z : Pgame} (hxy : x ≤ y) (hyz : y < z) : x < z := by
  rw [← not_leₓ] at hyz⊢
  exact mt (fun H => le_transₓ H hxy) hyz

@[trans]
theorem lt_of_lt_of_le {x y z : Pgame} (hxy : x < y) (hyz : y ≤ z) : x < z := by
  rw [← not_leₓ] at hxy⊢
  exact mt (fun H => le_transₓ hyz H) hxy

/-- Define the equivalence relation on pre-games. Two pre-games
  `x`, `y` are equivalent if `x ≤ y` and `y ≤ x`. -/
def Equiv (x y : Pgame) : Prop :=
  x ≤ y ∧ y ≤ x

-- mathport name: «expr ≈ »
local infixl:0 " ≈ " => Pgame.Equiv

@[refl, simp]
theorem equiv_refl x : x ≈ x :=
  ⟨Pgame.le_refl _, Pgame.le_refl _⟩

@[symm]
theorem equiv_symm {x y} : (x ≈ y) → (y ≈ x)
  | ⟨xy, yx⟩ => ⟨yx, xy⟩

@[trans]
theorem equiv_trans {x y z} : (x ≈ y) → (y ≈ z) → (x ≈ z)
  | ⟨xy, yx⟩, ⟨yz, zy⟩ => ⟨le_trans xy yz, le_trans zy yx⟩

@[trans]
theorem lt_of_lt_of_equiv {x y z} (h₁ : x < y) (h₂ : y ≈ z) : x < z :=
  lt_of_lt_of_le h₁ h₂.1

@[trans]
theorem le_of_le_of_equiv {x y z} (h₁ : x ≤ y) (h₂ : y ≈ z) : x ≤ z :=
  le_trans h₁ h₂.1

@[trans]
theorem lt_of_equiv_of_lt {x y z} (h₁ : x ≈ y) (h₂ : y < z) : x < z :=
  lt_of_le_of_lt h₁.1 h₂

@[trans]
theorem le_of_equiv_of_le {x y z} (h₁ : x ≈ y) (h₂ : y ≤ z) : x ≤ z :=
  le_trans h₁.1 h₂

theorem le_congr {x₁ y₁ x₂ y₂} : (x₁ ≈ x₂) → (y₁ ≈ y₂) → (x₁ ≤ y₁ ↔ x₂ ≤ y₂)
  | ⟨x12, x21⟩, ⟨y12, y21⟩ => ⟨fun h => le_trans x21 (le_trans h y12), fun h => le_trans x12 (le_trans h y21)⟩

theorem lt_congr {x₁ y₁ x₂ y₂} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ < y₁ ↔ x₂ < y₂ :=
  not_le.symm.trans <| (not_congr (le_congr hy hx)).trans not_le

theorem equiv_congr_left {y₁ y₂} : (y₁ ≈ y₂) ↔ ∀ x₁, (x₁ ≈ y₁) ↔ (x₁ ≈ y₂) :=
  ⟨fun h x₁ => ⟨fun h' => equiv_trans h' h, fun h' => equiv_trans h' (equiv_symm h)⟩, fun h => (h y₁).1 <| equiv_refl _⟩

theorem equiv_congr_right {x₁ x₂} : (x₁ ≈ x₂) ↔ ∀ y₁, (x₁ ≈ y₁) ↔ (x₂ ≈ y₁) :=
  ⟨fun h y₁ => ⟨fun h' => equiv_trans (equiv_symm h) h', fun h' => equiv_trans h h'⟩, fun h => (h x₂).2 <| equiv_refl _⟩

theorem equiv_of_mk_equiv {x y : Pgame} (L : x.LeftMoves ≃ y.LeftMoves) (R : x.RightMoves ≃ y.RightMoves)
    (hl : ∀ i : x.LeftMoves, x.moveLeft i ≈ y.moveLeft (L i))
    (hr : ∀ j : y.RightMoves, x.moveRight (R.symm j) ≈ y.moveRight j) : x ≈ y := by
  fconstructor <;> rw [le_def]
  · exact ⟨fun i => Or.inl ⟨L i, (hl i).1⟩, fun j => Or.inr ⟨R.symm j, (hr j).1⟩⟩
    
  · fconstructor
    · intro i
      left
      specialize hl (L.symm i)
      simp only [move_left_mk, Equivₓ.apply_symm_apply] at hl
      use ⟨L.symm i, hl.2⟩
      
    · intro j
      right
      specialize hr (R j)
      simp only [move_right_mk, Equivₓ.symm_apply_apply] at hr
      use ⟨R j, hr.2⟩
      
    

/-- `restricted x y` says that Left always has no more moves in `x` than in `y`,
     and Right always has no more moves in `y` than in `x` -/
inductive Restricted : Pgame.{u} → Pgame.{u} → Type (u + 1)
  | mk :
    ∀ {x y : Pgame} L : x.LeftMoves → y.LeftMoves R : y.RightMoves → x.RightMoves,
      (∀ i : x.LeftMoves, restricted (x.moveLeft i) (y.moveLeft (L i))) →
        (∀ j : y.RightMoves, restricted (x.moveRight (R j)) (y.moveRight j)) → restricted x y

/-- The identity restriction. -/
@[refl]
def Restricted.refl : ∀ x : Pgame, Restricted x x
  | mk xl xr xL xR => Restricted.mk id id (fun i => restricted.refl _) fun j => restricted.refl _

instance (x : Pgame) : Inhabited (Restricted x x) :=
  ⟨Restricted.refl _⟩

-- TODO trans for restricted
theorem Restricted.le : ∀ {x y : Pgame} r : Restricted x y, x ≤ y
  | mk xl xr xL xR, mk yl yr yL yR, restricted.mk L_embedding R_embedding L_restriction R_restriction => by
    rw [le_def]
    exact ⟨fun i => Or.inl ⟨L_embedding i, (L_restriction i).le⟩, fun i => Or.inr ⟨R_embedding i, (R_restriction i).le⟩⟩

/-- `relabelling x y` says that `x` and `y` are really the same game, just dressed up differently.
Specifically, there is a bijection between the moves for Left in `x` and in `y`, and similarly
for Right, and under these bijections we inductively have `relabelling`s for the consequent games.
-/
inductive Relabelling : Pgame.{u} → Pgame.{u} → Type (u + 1)
  | mk :
    ∀ {x y : Pgame} L : x.LeftMoves ≃ y.LeftMoves R : x.RightMoves ≃ y.RightMoves,
      (∀ i : x.LeftMoves, relabelling (x.moveLeft i) (y.moveLeft (L i))) →
        (∀ j : y.RightMoves, relabelling (x.moveRight (R.symm j)) (y.moveRight j)) → relabelling x y

/-- If `x` is a relabelling of `y`, then Left and Right have the same moves in either game,
    so `x` is a restriction of `y`. -/
def Relabelling.restricted : ∀ {x y : Pgame} r : Relabelling x y, Restricted x y
  | mk xl xr xL xR, mk yl yr yL yR, relabelling.mk L_equiv R_equiv L_relabelling R_relabelling =>
    Restricted.mk L_equiv.toEmbedding R_equiv.symm.toEmbedding (fun i => (L_relabelling i).Restricted) fun j =>
      (R_relabelling j).Restricted

/-- The identity relabelling. -/
-- It's not the case that `restricted x y → restricted y x → relabelling x y`,
-- but if we insisted that the maps in a restriction were injective, then one
-- could use Schröder-Bernstein for do this.
@[refl]
def Relabelling.refl : ∀ x : Pgame, Relabelling x x
  | mk xl xr xL xR =>
    Relabelling.mk (Equivₓ.refl _) (Equivₓ.refl _) (fun i => relabelling.refl _) fun j => relabelling.refl _

instance (x : Pgame) : Inhabited (Relabelling x x) :=
  ⟨Relabelling.refl _⟩

/-- Reverse a relabelling. -/
@[symm]
def Relabelling.symm : ∀ {x y : Pgame}, Relabelling x y → Relabelling y x
  | mk xl xr xL xR, mk yl yr yL yR, relabelling.mk L_equiv R_equiv L_relabelling R_relabelling => by
    refine' relabelling.mk L_equiv.symm R_equiv.symm _ _
    · intro i
      simpa using (L_relabelling (L_equiv.symm i)).symm
      
    · intro j
      simpa using (R_relabelling (R_equiv j)).symm
      

/-- Transitivity of relabelling -/
@[trans]
def Relabelling.trans : ∀ {x y z : Pgame}, Relabelling x y → Relabelling y z → Relabelling x z
  | mk xl xr xL xR, mk yl yr yL yR, mk zl zr zL zR, relabelling.mk L_equiv₁ R_equiv₁ L_relabelling₁ R_relabelling₁,
    relabelling.mk L_equiv₂ R_equiv₂ L_relabelling₂ R_relabelling₂ => by
    refine' relabelling.mk (L_equiv₁.trans L_equiv₂) (R_equiv₁.trans R_equiv₂) _ _
    · intro i
      simpa using (L_relabelling₁ _).trans (L_relabelling₂ _)
      
    · intro j
      simpa using (R_relabelling₁ _).trans (R_relabelling₂ _)
      

/-- Any game without left or right moves is a relabelling of 0. -/
def Relabelling.isEmpty (x : Pgame) [IsEmpty x.LeftMoves] [IsEmpty x.RightMoves] : Relabelling x 0 :=
  ⟨Equivₓ.equivPempty _, Equivₓ.equivPempty _, isEmptyElim, isEmptyElim⟩

theorem Relabelling.le {x y : Pgame} (r : Relabelling x y) : x ≤ y :=
  r.Restricted.le

/-- A relabelling lets us prove equivalence of games. -/
theorem Relabelling.equiv {x y : Pgame} (r : Relabelling x y) : x ≈ y :=
  ⟨r.le, r.symm.le⟩

instance {x y : Pgame} : Coe (Relabelling x y) (x ≈ y) :=
  ⟨Relabelling.equiv⟩

/-- Replace the types indexing the next moves for Left and Right by equivalent types. -/
def relabel {x : Pgame} {xl' xr'} (el : x.LeftMoves ≃ xl') (er : x.RightMoves ≃ xr') :=
  Pgame.mk xl' xr' (fun i => x.moveLeft (el.symm i)) fun j => x.moveRight (er.symm j)

@[simp]
theorem relabel_move_left' {x : Pgame} {xl' xr'} (el : x.LeftMoves ≃ xl') (er : x.RightMoves ≃ xr') (i : xl') :
    moveLeft (relabel el er) i = x.moveLeft (el.symm i) :=
  rfl

@[simp]
theorem relabel_move_left {x : Pgame} {xl' xr'} (el : x.LeftMoves ≃ xl') (er : x.RightMoves ≃ xr') (i : x.LeftMoves) :
    moveLeft (relabel el er) (el i) = x.moveLeft i := by
  simp

@[simp]
theorem relabel_move_right' {x : Pgame} {xl' xr'} (el : x.LeftMoves ≃ xl') (er : x.RightMoves ≃ xr') (j : xr') :
    moveRight (relabel el er) j = x.moveRight (er.symm j) :=
  rfl

@[simp]
theorem relabel_move_right {x : Pgame} {xl' xr'} (el : x.LeftMoves ≃ xl') (er : x.RightMoves ≃ xr') (j : x.RightMoves) :
    moveRight (relabel el er) (er j) = x.moveRight j := by
  simp

/-- The game obtained by relabelling the next moves is a relabelling of the original game. -/
def relabelRelabelling {x : Pgame} {xl' xr'} (el : x.LeftMoves ≃ xl') (er : x.RightMoves ≃ xr') :
    Relabelling x (relabel el er) :=
  Relabelling.mk el er
    (fun i => by
      simp )
    fun j => by
    simp

/-- The negation of `{L | R}` is `{-R | -L}`. -/
def neg : Pgame → Pgame
  | ⟨l, r, L, R⟩ => ⟨r, l, fun i => neg (R i), fun i => neg (L i)⟩

instance : Neg Pgame :=
  ⟨neg⟩

@[simp]
theorem neg_def {xl xr xL xR} : -mk xl xr xL xR = mk xr xl (fun j => -xR j) fun i => -xL i :=
  rfl

instance : HasInvolutiveNeg Pgame :=
  { Pgame.hasNeg with
    neg_neg := fun x => by
      induction' x with xl xr xL xR ihL ihR
      simp_rw [neg_def, ihL, ihR]
      exact ⟨rfl, rfl, HEq.rfl, HEq.rfl⟩ }

@[simp]
protected theorem neg_zero : -(0 : Pgame) = 0 := by
  dsimp [Zero.zero, Neg.neg, neg]
  congr <;> funext i <;> cases i

/-- An explicit equivalence between the moves for Left in `-x` and the moves for Right in `x`. -/
-- This equivalence is useful to avoid having to use `cases` unnecessarily.
def leftMovesNeg (x : Pgame) : (-x).LeftMoves ≃ x.RightMoves := by
  cases x
  rfl

/-- An explicit equivalence between the moves for Right in `-x` and the moves for Left in `x`. -/
def rightMovesNeg (x : Pgame) : (-x).RightMoves ≃ x.LeftMoves := by
  cases x
  rfl

@[simp]
theorem move_right_left_moves_neg {x : Pgame} (i : LeftMoves (-x)) :
    moveRight x ((leftMovesNeg x) i) = -moveLeft (-x) i := by
  induction x
  exact (neg_negₓ _).symm

@[simp]
theorem move_left_left_moves_neg_symm {x : Pgame} (i : RightMoves x) :
    moveLeft (-x) ((leftMovesNeg x).symm i) = -moveRight x i := by
  cases x
  rfl

@[simp]
theorem move_left_right_moves_neg {x : Pgame} (i : RightMoves (-x)) :
    moveLeft x ((rightMovesNeg x) i) = -moveRight (-x) i := by
  induction x
  exact (neg_negₓ _).symm

@[simp]
theorem move_right_right_moves_neg_symm {x : Pgame} (i : LeftMoves x) :
    moveRight (-x) ((rightMovesNeg x).symm i) = -moveLeft x i := by
  cases x
  rfl

/-- If `x` has the same moves as `y`, then `-x` has the sames moves as `-y`. -/
def Relabelling.negCongr : ∀ {x y : Pgame}, x.Relabelling y → (-x).Relabelling (-y)
  | mk xl xr xL xR, mk yl yr yL yR, ⟨L_equiv, R_equiv, L_relabelling, R_relabelling⟩ =>
    ⟨R_equiv, L_equiv, fun i =>
      relabelling.neg_congr
        (by
          simpa using R_relabelling (R_equiv i)),
      fun i =>
      relabelling.neg_congr
        (by
          simpa using L_relabelling (L_equiv.symm i))⟩

theorem le_iff_neg_ge : ∀ {x y : Pgame}, x ≤ y ↔ -y ≤ -x
  | mk xl xr xL xR, mk yl yr yL yR => by
    rw [le_def]
    rw [le_def]
    dsimp [neg]
    constructor
    · intro h
      constructor
      · intro i
        have t := h.right i
        cases t
        · right
          cases t
          use (@right_moves_neg (yR i)).symm t_w
          convert le_iff_neg_ge.1 t_h
          simp
          
        · left
          cases t
          use t_w
          exact le_iff_neg_ge.1 t_h
          
        
      · intro j
        have t := h.left j
        cases t
        · right
          cases t
          use t_w
          exact le_iff_neg_ge.1 t_h
          
        · left
          cases t
          use (@left_moves_neg (xL j)).symm t_w
          convert le_iff_neg_ge.1 t_h
          simp
          
        
      
    · intro h
      constructor
      · intro i
        have t := h.right i
        cases t
        · right
          cases t
          use (@left_moves_neg (xL i)) t_w
          convert le_iff_neg_ge.2 _
          convert t_h
          simp
          
        · left
          cases t
          use t_w
          exact le_iff_neg_ge.2 t_h
          
        
      · intro j
        have t := h.left j
        cases t
        · right
          cases t
          use t_w
          exact le_iff_neg_ge.2 t_h
          
        · left
          cases t
          use (@right_moves_neg (yR j)) t_w
          convert le_iff_neg_ge.2 _
          convert t_h
          simp
          
        
      

theorem neg_congr {x y : Pgame} (h : x ≈ y) : -x ≈ -y :=
  ⟨le_iff_neg_ge.1 h.2, le_iff_neg_ge.1 h.1⟩

theorem lt_iff_neg_gt : ∀ {x y : Pgame}, x < y ↔ -y < -x := by
  classical
  intros
  rw [← not_leₓ, ← not_leₓ, not_iff_not]
  apply le_iff_neg_ge

theorem zero_le_iff_neg_le_zero {x : Pgame} : 0 ≤ x ↔ -x ≤ 0 := by
  convert le_iff_neg_ge
  rw [Pgame.neg_zero]

theorem le_zero_iff_zero_le_neg {x : Pgame} : x ≤ 0 ↔ 0 ≤ -x := by
  convert le_iff_neg_ge
  rw [Pgame.neg_zero]

/-- The sum of `x = {xL | xR}` and `y = {yL | yR}` is `{xL + y, x + yL | xR + y, x + yR}`. -/
def add (x y : Pgame) : Pgame := by
  induction' x with xl xr xL xR IHxl IHxr generalizing y
  induction' y with yl yr yL yR IHyl IHyr
  have y := mk yl yr yL yR
  refine' ⟨Sum xl yl, Sum xr yr, Sum.rec _ _, Sum.rec _ _⟩
  · exact fun i => IHxl i y
    
  · exact fun i => IHyl i
    
  · exact fun i => IHxr i y
    
  · exact fun i => IHyr i
    

instance : Add Pgame :=
  ⟨add⟩

/-- `x + 0` has exactly the same moves as `x`. -/
def addZeroRelabelling : ∀ x : Pgame.{u}, Relabelling (x + 0) x
  | mk xl xr xL xR => by
    refine' ⟨Equivₓ.sumEmpty xl Pempty, Equivₓ.sumEmpty xr Pempty, _, _⟩
    · rintro (⟨i⟩ | ⟨⟨⟩⟩)
      apply add_zero_relabelling
      
    · rintro j
      apply add_zero_relabelling
      

/-- `x + 0` is equivalent to `x`. -/
theorem add_zero_equiv (x : Pgame.{u}) : x + 0 ≈ x :=
  (addZeroRelabelling x).Equiv

/-- `0 + x` has exactly the same moves as `x`. -/
def zeroAddRelabelling : ∀ x : Pgame.{u}, Relabelling (0 + x) x
  | mk xl xr xL xR => by
    refine' ⟨Equivₓ.emptySum Pempty xl, Equivₓ.emptySum Pempty xr, _, _⟩
    · rintro (⟨⟨⟩⟩ | ⟨i⟩)
      apply zero_add_relabelling
      
    · rintro j
      apply zero_add_relabelling
      

/-- `0 + x` is equivalent to `x`. -/
theorem zero_add_equiv (x : Pgame.{u}) : 0 + x ≈ x :=
  (zeroAddRelabelling x).Equiv

/-- An explicit equivalence between the moves for Left in `x + y` and the type-theory sum
    of the moves for Left in `x` and in `y`. -/
def leftMovesAdd (x y : Pgame) : (x + y).LeftMoves ≃ Sum x.LeftMoves y.LeftMoves := by
  cases x
  cases y
  rfl

/-- An explicit equivalence between the moves for Right in `x + y` and the type-theory sum
    of the moves for Right in `x` and in `y`. -/
def rightMovesAdd (x y : Pgame) : (x + y).RightMoves ≃ Sum x.RightMoves y.RightMoves := by
  cases x
  cases y
  rfl

@[simp]
theorem mk_add_move_left_inl {xl xr yl yr} {xL xR yL yR} {i} :
    (mk xl xr xL xR + mk yl yr yL yR).moveLeft (Sum.inl i) = (mk xl xr xL xR).moveLeft i + mk yl yr yL yR :=
  rfl

@[simp]
theorem add_move_left_inl {x y : Pgame} {i} :
    (x + y).moveLeft ((@leftMovesAdd x y).symm (Sum.inl i)) = x.moveLeft i + y := by
  cases x
  cases y
  rfl

@[simp]
theorem mk_add_move_right_inl {xl xr yl yr} {xL xR yL yR} {i} :
    (mk xl xr xL xR + mk yl yr yL yR).moveRight (Sum.inl i) = (mk xl xr xL xR).moveRight i + mk yl yr yL yR :=
  rfl

@[simp]
theorem add_move_right_inl {x y : Pgame} {i} :
    (x + y).moveRight ((@rightMovesAdd x y).symm (Sum.inl i)) = x.moveRight i + y := by
  cases x
  cases y
  rfl

@[simp]
theorem mk_add_move_left_inr {xl xr yl yr} {xL xR yL yR} {i} :
    (mk xl xr xL xR + mk yl yr yL yR).moveLeft (Sum.inr i) = mk xl xr xL xR + (mk yl yr yL yR).moveLeft i :=
  rfl

@[simp]
theorem add_move_left_inr {x y : Pgame} {i : y.LeftMoves} :
    (x + y).moveLeft ((@leftMovesAdd x y).symm (Sum.inr i)) = x + y.moveLeft i := by
  cases x
  cases y
  rfl

@[simp]
theorem mk_add_move_right_inr {xl xr yl yr} {xL xR yL yR} {i} :
    (mk xl xr xL xR + mk yl yr yL yR).moveRight (Sum.inr i) = mk xl xr xL xR + (mk yl yr yL yR).moveRight i :=
  rfl

@[simp]
theorem add_move_right_inr {x y : Pgame} {i} :
    (x + y).moveRight ((@rightMovesAdd x y).symm (Sum.inr i)) = x + y.moveRight i := by
  cases x
  cases y
  rfl

instance is_empty_nat_right_moves : ∀ n : ℕ, IsEmpty (RightMoves n)
  | 0 => Pempty.is_empty
  | n + 1 => by
    have := is_empty_nat_right_moves n
    rw [Nat.cast_succₓ]
    exact (right_moves_add _ _).isEmpty

/-- If `w` has the same moves as `x` and `y` has the same moves as `z`,
then `w + y` has the same moves as `x + z`. -/
def Relabelling.addCongr : ∀ {w x y z : Pgame.{u}}, w.Relabelling x → y.Relabelling z → (w + y).Relabelling (x + z)
  | mk wl wr wL wR, mk xl xr xL xR, mk yl yr yL yR, mk zl zr zL zR,
    ⟨L_equiv₁, R_equiv₁, L_relabelling₁, R_relabelling₁⟩, ⟨L_equiv₂, R_equiv₂, L_relabelling₂, R_relabelling₂⟩ => by
    refine' ⟨Equivₓ.sumCongr L_equiv₁ L_equiv₂, Equivₓ.sumCongr R_equiv₁ R_equiv₂, _, _⟩
    · rintro (i | j)
      · exact relabelling.add_congr (L_relabelling₁ i) ⟨L_equiv₂, R_equiv₂, L_relabelling₂, R_relabelling₂⟩
        
      · exact relabelling.add_congr ⟨L_equiv₁, R_equiv₁, L_relabelling₁, R_relabelling₁⟩ (L_relabelling₂ j)
        
      
    · rintro (i | j)
      · exact relabelling.add_congr (R_relabelling₁ i) ⟨L_equiv₂, R_equiv₂, L_relabelling₂, R_relabelling₂⟩
        
      · exact relabelling.add_congr ⟨L_equiv₁, R_equiv₁, L_relabelling₁, R_relabelling₁⟩ (R_relabelling₂ j)
        
      

instance : Sub Pgame :=
  ⟨fun x y => x + -y⟩

@[simp]
theorem sub_zero (x : Pgame) : x - 0 = x + 0 :=
  show x + -0 = x + 0 by
    rw [Pgame.neg_zero]

/-- If `w` has the same moves as `x` and `y` has the same moves as `z`,
then `w - y` has the same moves as `x - z`. -/
def Relabelling.subCongr {w x y z : Pgame} (h₁ : w.Relabelling x) (h₂ : y.Relabelling z) :
    (w - y).Relabelling (x - z) :=
  h₁.addCongr h₂.negCongr

/-- `-(x+y)` has exactly the same moves as `-x + -y`. -/
def negAddRelabelling : ∀ x y : Pgame, Relabelling (-(x + y)) (-x + -y)
  | mk xl xr xL xR, mk yl yr yL yR =>
    ⟨Equivₓ.refl _, Equivₓ.refl _, fun j =>
      Sum.casesOn j (fun j => neg_add_relabelling (xR j) (mk yl yr yL yR)) fun j =>
        neg_add_relabelling (mk xl xr xL xR) (yR j),
      fun i =>
      Sum.casesOn i (fun i => neg_add_relabelling (xL i) (mk yl yr yL yR)) fun i =>
        neg_add_relabelling (mk xl xr xL xR) (yL i)⟩

theorem neg_add_le {x y : Pgame} : -(x + y) ≤ -x + -y :=
  (negAddRelabelling x y).le

/-- `x+y` has exactly the same moves as `y+x`. -/
def addCommRelabelling : ∀ x y : Pgame.{u}, Relabelling (x + y) (y + x)
  | mk xl xr xL xR, mk yl yr yL yR => by
    refine' ⟨Equivₓ.sumComm _ _, Equivₓ.sumComm _ _, _, _⟩ <;>
      rintro (_ | _) <;>
        · simp [left_moves_add, right_moves_add]
          apply add_comm_relabelling
          

theorem add_comm_le {x y : Pgame} : x + y ≤ y + x :=
  (addCommRelabelling x y).le

theorem add_comm_equiv {x y : Pgame} : x + y ≈ y + x :=
  (addCommRelabelling x y).Equiv

/-- `(x + y) + z` has exactly the same moves as `x + (y + z)`. -/
def addAssocRelabelling : ∀ x y z : Pgame.{u}, Relabelling (x + y + z) (x + (y + z))
  | mk xl xr xL xR, mk yl yr yL yR, mk zl zr zL zR => by
    refine' ⟨Equivₓ.sumAssoc _ _ _, Equivₓ.sumAssoc _ _ _, _, _⟩
    · rintro (⟨i | i⟩ | i)
      · apply add_assoc_relabelling
        
      · change relabelling (mk xl xr xL xR + yL i + mk zl zr zL zR) (mk xl xr xL xR + (yL i + mk zl zr zL zR))
        apply add_assoc_relabelling
        
      · change relabelling (mk xl xr xL xR + mk yl yr yL yR + zL i) (mk xl xr xL xR + (mk yl yr yL yR + zL i))
        apply add_assoc_relabelling
        
      
    · rintro (j | ⟨j | j⟩)
      · apply add_assoc_relabelling
        
      · change relabelling (mk xl xr xL xR + yR j + mk zl zr zL zR) (mk xl xr xL xR + (yR j + mk zl zr zL zR))
        apply add_assoc_relabelling
        
      · change relabelling (mk xl xr xL xR + mk yl yr yL yR + zR j) (mk xl xr xL xR + (mk yl yr yL yR + zR j))
        apply add_assoc_relabelling
        
      

theorem add_assoc_equiv {x y z : Pgame} : x + y + z ≈ x + (y + z) :=
  (addAssocRelabelling x y z).Equiv

private theorem add_le_add_right : ∀ {x y z : Pgame} h : x ≤ y, x + z ≤ y + z
  | mk xl xr xL xR, mk yl yr yL yR, mk zl zr zL zR => by
    intro h
    rw [le_def]
    constructor
    · -- if Left plays first
      intro i
      change Sum xl zl at i
      cases i
      · -- either they play in x
        rw [le_def] at h
        cases h
        have t := h_left i
        rcases t with (⟨i', ih⟩ | ⟨j, jh⟩)
        · left
          refine' ⟨(left_moves_add _ _).invFun (Sum.inl i'), _⟩
          exact add_le_add_right ih
          
        · right
          refine' ⟨(right_moves_add _ _).invFun (Sum.inl j), _⟩
          convert add_le_add_right jh
          apply add_move_right_inl
          
        
      · -- or play in z
        left
        refine' ⟨(left_moves_add _ _).invFun (Sum.inr i), _⟩
        exact add_le_add_right h
        
      
    · -- if Right plays first
      intro j
      change Sum yr zr at j
      cases j
      · -- either they play in y
        rw [le_def] at h
        cases h
        have t := h_right j
        rcases t with (⟨i, ih⟩ | ⟨j', jh⟩)
        · left
          refine' ⟨(left_moves_add _ _).invFun (Sum.inl i), _⟩
          convert add_le_add_right ih
          apply add_move_left_inl
          
        · right
          refine' ⟨(right_moves_add _ _).invFun (Sum.inl j'), _⟩
          exact add_le_add_right jh
          
        
      · -- or play in z
        right
        refine' ⟨(right_moves_add _ _).invFun (Sum.inr j), _⟩
        exact add_le_add_right h
        
      

instance covariant_class_swap_add_le : CovariantClass Pgame Pgame (swap (· + ·)) (· ≤ ·) :=
  ⟨fun x y z => add_le_add_right⟩

instance covariant_class_add_le : CovariantClass Pgame Pgame (· + ·) (· ≤ ·) :=
  ⟨fun x y z h =>
    calc
      x + y ≤ y + x := add_comm_le
      _ ≤ z + x := add_le_add_right h _
      _ ≤ x + z := add_comm_le
      ⟩

theorem add_congr {w x y z : Pgame} (h₁ : w ≈ x) (h₂ : y ≈ z) : w + y ≈ x + z :=
  ⟨calc
      w + y ≤ w + z := add_le_add_left h₂.1 _
      _ ≤ x + z := add_le_add_right h₁.1 _
      ,
    calc
      x + z ≤ x + y := add_le_add_left h₂.2 _
      _ ≤ w + y := add_le_add_right h₁.2 _
      ⟩

theorem sub_congr {w x y z : Pgame} (h₁ : w ≈ x) (h₂ : y ≈ z) : w - y ≈ x - z :=
  add_congr h₁ (neg_congr h₂)

theorem add_left_neg_le_zero : ∀ x : Pgame, -x + x ≤ 0
  | ⟨xl, xr, xL, xR⟩ => by
    rw [le_def]
    constructor
    · intro i
      change Sum xr xl at i
      cases i
      · -- If Left played in -x, Right responds with the same move in x.
        right
        refine' ⟨(right_moves_add _ _).invFun (Sum.inr i), _⟩
        convert @add_left_neg_le_zero (xR i)
        exact add_move_right_inr
        
      · -- If Left in x, Right responds with the same move in -x.
        right
        dsimp
        refine' ⟨(right_moves_add _ _).invFun (Sum.inl i), _⟩
        convert @add_left_neg_le_zero (xL i)
        exact add_move_right_inl
        
      
    · rintro ⟨⟩
      

theorem zero_le_add_left_neg (x : Pgame) : 0 ≤ -x + x := by
  rw [le_iff_neg_ge, Pgame.neg_zero]
  exact le_transₓ neg_add_le (add_left_neg_le_zero _)

theorem add_left_neg_equiv (x : Pgame) : -x + x ≈ 0 :=
  ⟨add_left_neg_le_zero x, zero_le_add_left_neg x⟩

theorem add_right_neg_le_zero (x : Pgame) : x + -x ≤ 0 :=
  le_trans add_comm_le (add_left_neg_le_zero x)

theorem zero_le_add_right_neg (x : Pgame) : 0 ≤ x + -x :=
  le_trans (zero_le_add_left_neg x) add_comm_le

theorem add_right_neg_equiv (x : Pgame) : x + -x ≈ 0 :=
  ⟨add_right_neg_le_zero x, zero_le_add_right_neg x⟩

instance covariant_class_swap_add_lt : CovariantClass Pgame Pgame (swap (· + ·)) (· < ·) :=
  ⟨fun x y z h =>
    suffices z + x ≤ y + x → z ≤ y by
      rw [← not_leₓ] at h⊢
      exact mt this h
    fun w =>
    calc
      z ≤ z + 0 := (addZeroRelabelling _).symm.le
      _ ≤ z + (x + -x) := add_le_add_left (zero_le_add_right_neg x) _
      _ ≤ z + x + -x := (addAssocRelabelling _ _ _).symm.le
      _ ≤ y + x + -x := add_le_add_right w _
      _ ≤ y + (x + -x) := (addAssocRelabelling _ _ _).le
      _ ≤ y + 0 := add_le_add_left (add_right_neg_le_zero x) _
      _ ≤ y := (addZeroRelabelling _).le
      ⟩

instance covariant_class_add_lt : CovariantClass Pgame Pgame (· + ·) (· < ·) :=
  ⟨fun x y z h =>
    calc
      x + y ≤ y + x := add_comm_le
      _ < z + x := add_lt_add_right h _
      _ ≤ x + z := add_comm_le
      ⟩

theorem le_iff_sub_nonneg {x y : Pgame} : x ≤ y ↔ 0 ≤ y - x :=
  ⟨fun h => le_trans (zero_le_add_right_neg x) (add_le_add_right h _), fun h =>
    calc
      x ≤ 0 + x := (zeroAddRelabelling x).symm.le
      _ ≤ y - x + x := add_le_add_right h _
      _ ≤ y + (-x + x) := (addAssocRelabelling _ _ _).le
      _ ≤ y + 0 := add_le_add_left (add_left_neg_le_zero x) _
      _ ≤ y := (addZeroRelabelling y).le
      ⟩

theorem lt_iff_sub_pos {x y : Pgame} : x < y ↔ 0 < y - x :=
  ⟨fun h => lt_of_le_of_lt (zero_le_add_right_neg x) (add_lt_add_right h _), fun h =>
    calc
      x ≤ 0 + x := (zeroAddRelabelling x).symm.le
      _ < y - x + x := add_lt_add_right h _
      _ ≤ y + (-x + x) := (addAssocRelabelling _ _ _).le
      _ ≤ y + 0 := add_le_add_left (add_left_neg_le_zero x) _
      _ ≤ y := (addZeroRelabelling y).le
      ⟩

/-- The pre-game `star`, which is fuzzy/confused with zero. -/
def star : Pgame :=
  Pgame.ofLists [0] [0]

instance inhabitedStarLeftMoves : Inhabited star.LeftMoves :=
  show Inhabited (Finₓ 1) by
    infer_instance

instance inhabitedStarRightMoves : Inhabited star.RightMoves :=
  show Inhabited (Finₓ 1) by
    infer_instance

theorem star_lt_zero : star < 0 := by
  rw [lt_def] <;>
    exact
      Or.inr
        ⟨⟨0, zero_lt_one⟩, by
          constructor <;> rintro ⟨⟩⟩

theorem zero_lt_star : 0 < star := by
  rw [lt_def] <;>
    exact
      Or.inl
        ⟨⟨0, zero_lt_one⟩, by
          constructor <;> rintro ⟨⟩⟩

/-- The pre-game `ω`. (In fact all ordinals have game and surreal representatives.) -/
def omega : Pgame :=
  ⟨ULift ℕ, Pempty, fun n => ↑n.1, Pempty.elimₓ⟩

theorem zero_lt_one : (0 : Pgame) < 1 := by
  rw [lt_def]
  left
  use
    ⟨PUnit.unit, by
      constructor <;> rintro ⟨⟩⟩

/-- The pre-game `half` is defined as `{0 | 1}`. -/
def half : Pgame :=
  ⟨PUnit, PUnit, 0, 1⟩

@[simp]
theorem half_move_left : half.moveLeft PUnit.unit = 0 :=
  rfl

@[simp]
theorem half_move_right : half.moveRight PUnit.unit = 1 :=
  rfl

protected theorem zero_lt_half : 0 < half := by
  rw [lt_def]
  left
  use PUnit.unit
  constructor <;> rintro ⟨⟩

theorem half_lt_one : half < 1 := by
  rw [lt_def]
  right
  use PUnit.unit
  constructor <;> rintro ⟨⟩
  exact zero_lt_one

end Pgame

