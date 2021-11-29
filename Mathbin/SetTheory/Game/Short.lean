import Mathbin.SetTheory.Game 
import Mathbin.Data.Fintype.Basic

/-!
# Short games

A combinatorial game is `short` [Conway, ch.9][conway2001] if it has only finitely many positions.
In particular, this means there is a finite set of moves at every point.

We prove that the order relations `≤` and `<`, and the equivalence relation `≈`, are decidable on
short games, although unfortunately in practice `dec_trivial` doesn't seem to be able to
prove anything using these instances.
-/


universe u

namespace Pgame

/-- A short game is a game with a finite set of moves at every turn. -/
inductive short : Pgame.{u} → Type (u + 1)
  | mk :
  ∀ {α β : Type u} {L : α → Pgame.{u}} {R : β → Pgame.{u}} sL : ∀ i : α, short (L i) sR : ∀ j : β, short (R j)
    [Fintype α] [Fintype β], short ⟨α, β, L, R⟩

instance subsingleton_short : ∀ x : Pgame, Subsingleton (short x)
| mk xl xr xL xR =>
  ⟨fun a b =>
      by 
        cases a 
        cases b 
        congr
        ·
          funext 
          apply @Subsingleton.elimₓ _ (subsingleton_short (xL x))
        ·
          funext 
          apply @Subsingleton.elimₓ _ (subsingleton_short (xR x))⟩

/-- A synonym for `short.mk` that specifies the pgame in an implicit argument. -/
def short.mk' {x : Pgame} [Fintype x.left_moves] [Fintype x.right_moves]
  (sL : ∀ i : x.left_moves, short (x.move_left i)) (sR : ∀ j : x.right_moves, short (x.move_right j)) : short x :=
  by 
    (
        cases x 
        dsimp  at *) <;>
      exact short.mk sL sR

attribute [class] short

/--
Extracting the `fintype` instance for the indexing type for Left's moves in a short game.
This is an unindexed typeclass, so it can't be made a global instance.
-/
def fintype_left {α β : Type u} {L : α → Pgame.{u}} {R : β → Pgame.{u}} [S : short ⟨α, β, L, R⟩] : Fintype α :=
  by 
    cases' S with _ _ _ _ _ _ F _ 
    exact F

attribute [local instance] fintype_left

instance fintype_left_moves (x : Pgame) [S : short x] : Fintype x.left_moves :=
  by 
    cases' x 
    dsimp 
    infer_instance

/--
Extracting the `fintype` instance for the indexing type for Right's moves in a short game.
This is an unindexed typeclass, so it can't be made a global instance.
-/
def fintype_right {α β : Type u} {L : α → Pgame.{u}} {R : β → Pgame.{u}} [S : short ⟨α, β, L, R⟩] : Fintype β :=
  by 
    cases' S with _ _ _ _ _ _ _ F 
    exact F

attribute [local instance] fintype_right

instance fintype_right_moves (x : Pgame) [S : short x] : Fintype x.right_moves :=
  by 
    cases' x 
    dsimp 
    infer_instance

instance move_left_short (x : Pgame) [S : short x] (i : x.left_moves) : short (x.move_left i) :=
  by 
    cases' S with _ _ _ _ L _ _ _ 
    apply L

/--
Extracting the `short` instance for a move by Left.
This would be a dangerous instance potentially introducing new metavariables
in typeclass search, so we only make it an instance locally.
-/
def move_left_short' {xl xr} xL xR [S : short (mk xl xr xL xR)] (i : xl) : short (xL i) :=
  by 
    cases' S with _ _ _ _ L _ _ _ 
    apply L

attribute [local instance] move_left_short'

instance move_right_short (x : Pgame) [S : short x] (j : x.right_moves) : short (x.move_right j) :=
  by 
    cases' S with _ _ _ _ _ R _ _ 
    apply R

/--
Extracting the `short` instance for a move by Right.
This would be a dangerous instance potentially introducing new metavariables
in typeclass search, so we only make it an instance locally.
-/
def move_right_short' {xl xr} xL xR [S : short (mk xl xr xL xR)] (j : xr) : short (xR j) :=
  by 
    cases' S with _ _ _ _ _ R _ _ 
    apply R

attribute [local instance] move_right_short'

instance short.of_pempty {xL} {xR} : short (mk Pempty Pempty xL xR) :=
  short.mk (fun i => Pempty.elimₓ i) fun j => Pempty.elimₓ j

instance short_0 : short 0 :=
  short.mk
    (fun i =>
      by 
        cases i)
    fun j =>
      by 
        cases j

instance short_1 : short 1 :=
  short.mk
    (fun i =>
      by 
        cases i 
        infer_instance)
    fun j =>
      by 
        cases j

/-- Evidence that every `pgame` in a list is `short`. -/
inductive list_short : List Pgame.{u} → Type (u + 1)
  | nil : list_short []
  | cons : ∀ hd : Pgame.{u} [short hd] tl : List Pgame.{u} [list_short tl], list_short (hd :: tl)

attribute [class] list_short

attribute [instance] list_short.nil list_short.cons

instance list_short_nth_le :
  ∀ L : List Pgame.{u} [list_short L] i : Finₓ (List.length L), short (List.nthLe L i i.is_lt)
| [], _, n =>
  by 
    exfalso 
    rcases n with ⟨_, ⟨⟩⟩
| hd :: tl, @list_short.cons _ S _ _, ⟨0, _⟩ => S
| hd :: tl, @list_short.cons _ _ _ S, ⟨n+1, h⟩ => @list_short_nth_le tl S ⟨n, (add_lt_add_iff_right 1).mp h⟩

instance short_of_lists : ∀ L R : List Pgame [list_short L] [list_short R], short (Pgame.ofLists L R)
| L, R, _, _ =>
  by 
    skip 
    apply short.mk
    ·
      intros 
      infer_instance
    ·
      intros 
      apply Pgame.listShortNthLe

-- error in SetTheory.Game.Short: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `x` is a short game, and `y` is a relabelling of `x`, then `y` is also short. -/
def short_of_relabelling : ∀ {x y : pgame.{u}} (R : relabelling x y) (S : short x), short y
| x, y, ⟨L, R, rL, rR⟩, S := begin
  resetI,
  haveI [] [] [":=", expr fintype.of_equiv _ L],
  haveI [] [] [":=", expr fintype.of_equiv _ R],
  exact [expr short.mk' (λ i, by { rw ["<-", expr L.right_inv i] [],
      apply [expr short_of_relabelling (rL (L.symm i)) infer_instance] }) (λ
    j, short_of_relabelling (rR j) infer_instance)]
end

/-- If `x` has no left move or right moves, it is (very!) short. -/
def short_of_equiv_empty {x : Pgame.{u}} (el : x.left_moves ≃ Pempty) (er : x.right_moves ≃ Pempty) : short x :=
  short_of_relabelling (relabel_relabelling el er).symm short.of_pempty

instance short_neg : ∀ x : Pgame.{u} [short x], short (-x)
| mk xl xr xL xR, _ =>
  by 
    skip 
    apply short.mk
    ·
      rintro i 
      apply short_neg _ 
      infer_instance
    ·
      rintro j 
      apply short_neg _ 
      infer_instance

instance short_add : ∀ x y : Pgame.{u} [short x] [short y], short (x+y)
| mk xl xr xL xR, mk yl yr yL yR, _, _ =>
  by 
    skip 
    apply short.mk
    ·
      rintro ⟨i⟩
      ·
        apply short_add
      ·
        change short (mk xl xr xL xR+yL i)
        apply short_add
    ·
      rintro ⟨j⟩
      ·
        apply short_add
      ·
        change short (mk xl xr xL xR+yR j)
        apply short_add

instance short_nat : ∀ n : ℕ, short n
| 0 => Pgame.short0
| n+1 => @Pgame.shortAdd _ _ (short_nat n) Pgame.short1

instance short_bit0 (x : Pgame.{u}) [short x] : short (bit0 x) :=
  by 
    dsimp [bit0]
    infer_instance

instance short_bit1 (x : Pgame.{u}) [short x] : short (bit1 x) :=
  by 
    dsimp [bit1]
    infer_instance

/--
Auxiliary construction of decidability instances.
We build `decidable (x ≤ y)` and `decidable (x < y)` in a simultaneous induction.
Instances for the two projections separately are provided below.
-/
def le_lt_decidable : ∀ x y : Pgame.{u} [short x] [short y], Decidable (x ≤ y) × Decidable (x < y)
| mk xl xr xL xR, mk yl yr yL yR, shortx, shorty =>
  by 
    skip 
    split 
    ·
      refine' @decidableOfIff' _ _ mk_le_mk (id _)
      apply @And.decidable _ _ _ _
      ·
        apply
          @Fintype.decidableForallFintype xl _ _
            (by 
              infer_instance)
        intro i 
        apply (@le_lt_decidable _ _ _ _).2 <;> infer_instance
      ·
        apply
          @Fintype.decidableForallFintype yr _ _
            (by 
              infer_instance)
        intro i 
        apply (@le_lt_decidable _ _ _ _).2 <;> infer_instance
    ·
      refine' @decidableOfIff' _ _ mk_lt_mk (id _)
      apply @Or.decidable _ _ _ _
      ·
        apply
          @Fintype.decidableExistsFintype yl _ _
            (by 
              infer_instance)
        intro i 
        apply (@le_lt_decidable _ _ _ _).1 <;> infer_instance
      ·
        apply
          @Fintype.decidableExistsFintype xr _ _
            (by 
              infer_instance)
        intro i 
        apply (@le_lt_decidable _ _ _ _).1 <;> infer_instance

instance le_decidable (x y : Pgame.{u}) [short x] [short y] : Decidable (x ≤ y) :=
  (le_lt_decidable x y).1

instance lt_decidable (x y : Pgame.{u}) [short x] [short y] : Decidable (x < y) :=
  (le_lt_decidable x y).2

instance equiv_decidable (x y : Pgame.{u}) [short x] [short y] : Decidable (x ≈ y) :=
  And.decidable

example : short 0 :=
  by 
    infer_instance

example : short 1 :=
  by 
    infer_instance

example : short 2 :=
  by 
    infer_instance

example : short (-2) :=
  by 
    infer_instance

example : short (of_lists [0] [1]) :=
  by 
    infer_instance

example : short (of_lists [-2, -1] [1]) :=
  by 
    infer_instance

example : short (0+0) :=
  by 
    infer_instance

example : Decidable ((1 : Pgame) ≤ 1) :=
  by 
    infer_instance

end Pgame

