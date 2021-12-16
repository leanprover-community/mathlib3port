import Mathbin.SetTheory.Game.Short

/-!
# Games described via "the state of the board".

We provide a simple mechanism for constructing combinatorial (pre-)games, by describing
"the state of the board", and providing an upper bound on the number of turns remaining.


## Implementation notes

We're very careful to produce a computable definition, so small games can be evaluated
using `dec_trivial`. To achieve this, I've had to rely solely on induction on natural numbers:
relying on general well-foundedness seems to be poisonous to computation?

See `set_theory/game/domineering` for an example using this construction.
-/


universe u

namespace Pgame

/--
`pgame_state S` describes how to interpret `s : S` as a state of a combinatorial game.
Use `pgame.of s` or `game.of s` to construct the game.

`pgame_state.L : S → finset S` and `pgame_state.R : S → finset S` describe the states reachable
by a move by Left or Right. `pgame_state.turn_bound : S → ℕ` gives an upper bound on the number of
possible turns remaining from this state.
-/
class State (S : Type u) where 
  turnBound : S → ℕ 
  l : S → Finset S 
  r : S → Finset S 
  left_bound : ∀ {s t : S} m : t ∈ L s, turn_bound t < turn_bound s 
  right_bound : ∀ {s t : S} m : t ∈ R s, turn_bound t < turn_bound s

open State

variable {S : Type u} [State S]

theorem turn_bound_ne_zero_of_left_move {s t : S} (m : t ∈ L s) : turn_bound s ≠ 0 :=
  by 
    intro h 
    have t := state.left_bound m 
    rw [h] at t 
    exact Nat.not_succ_le_zeroₓ _ t

theorem turn_bound_ne_zero_of_right_move {s t : S} (m : t ∈ R s) : turn_bound s ≠ 0 :=
  by 
    intro h 
    have t := state.right_bound m 
    rw [h] at t 
    exact Nat.not_succ_le_zeroₓ _ t

theorem turn_bound_of_left {s t : S} (m : t ∈ L s) (n : ℕ) (h : turn_bound s ≤ n+1) : turn_bound t ≤ n :=
  Nat.le_of_lt_succₓ (Nat.lt_of_lt_of_leₓ (left_bound m) h)

theorem turn_bound_of_right {s t : S} (m : t ∈ R s) (n : ℕ) (h : turn_bound s ≤ n+1) : turn_bound t ≤ n :=
  Nat.le_of_lt_succₓ (Nat.lt_of_lt_of_leₓ (right_bound m) h)

/--
Construct a `pgame` from a state and a (not necessarily optimal) bound on the number of
turns remaining.
-/
def of_aux : ∀ n : ℕ s : S h : turn_bound s ≤ n, Pgame
| 0, s, h =>
  Pgame.mk { t // t ∈ L s } { t // t ∈ R s }
    (fun t =>
      by 
        exfalso 
        exact turn_bound_ne_zero_of_left_move t.2 (nonpos_iff_eq_zero.mp h))
    fun t =>
      by 
        exfalso 
        exact turn_bound_ne_zero_of_right_move t.2 (nonpos_iff_eq_zero.mp h)
| n+1, s, h =>
  Pgame.mk { t // t ∈ L s } { t // t ∈ R s } (fun t => of_aux n t (turn_bound_of_left t.2 n h))
    fun t => of_aux n t (turn_bound_of_right t.2 n h)

/-- Two different (valid) turn bounds give equivalent games. -/
def of_aux_relabelling :
  ∀ s : S n m : ℕ hn : turn_bound s ≤ n hm : turn_bound s ≤ m, relabelling (of_aux n s hn) (of_aux m s hm)
| s, 0, 0, hn, hm =>
  by 
    dsimp [Pgame.ofAux]
    fconstructor 
    rfl 
    rfl
    ·
      intro i 
      dsimp  at i 
      exfalso 
      exact turn_bound_ne_zero_of_left_move i.2 (nonpos_iff_eq_zero.mp hn)
    ·
      intro j 
      dsimp  at j 
      exfalso 
      exact turn_bound_ne_zero_of_right_move j.2 (nonpos_iff_eq_zero.mp hm)
| s, 0, m+1, hn, hm =>
  by 
    dsimp [Pgame.ofAux]
    fconstructor 
    rfl 
    rfl
    ·
      intro i 
      dsimp  at i 
      exfalso 
      exact turn_bound_ne_zero_of_left_move i.2 (nonpos_iff_eq_zero.mp hn)
    ·
      intro j 
      dsimp  at j 
      exfalso 
      exact turn_bound_ne_zero_of_right_move j.2 (nonpos_iff_eq_zero.mp hn)
| s, n+1, 0, hn, hm =>
  by 
    dsimp [Pgame.ofAux]
    fconstructor 
    rfl 
    rfl
    ·
      intro i 
      dsimp  at i 
      exfalso 
      exact turn_bound_ne_zero_of_left_move i.2 (nonpos_iff_eq_zero.mp hm)
    ·
      intro j 
      dsimp  at j 
      exfalso 
      exact turn_bound_ne_zero_of_right_move j.2 (nonpos_iff_eq_zero.mp hm)
| s, n+1, m+1, hn, hm =>
  by 
    dsimp [Pgame.ofAux]
    fconstructor 
    rfl 
    rfl
    ·
      intro i 
      apply of_aux_relabelling
    ·
      intro j 
      apply of_aux_relabelling

/-- Construct a combinatorial `pgame` from a state. -/
def of (s : S) : Pgame :=
  of_aux (turn_bound s) s (refl _)

/--
The equivalence between `left_moves` for a `pgame` constructed using `of_aux _ s _`, and `L s`.
-/
def left_moves_of_aux (n : ℕ) {s : S} (h : turn_bound s ≤ n) : left_moves (of_aux n s h) ≃ { t // t ∈ L s } :=
  by 
    induction n <;> rfl

/--
The equivalence between `left_moves` for a `pgame` constructed using `of s`, and `L s`.
-/
def left_moves_of (s : S) : left_moves (of s) ≃ { t // t ∈ L s } :=
  left_moves_of_aux _ _

/--
The equivalence between `right_moves` for a `pgame` constructed using `of_aux _ s _`, and `R s`.
-/
def right_moves_of_aux (n : ℕ) {s : S} (h : turn_bound s ≤ n) : right_moves (of_aux n s h) ≃ { t // t ∈ R s } :=
  by 
    induction n <;> rfl

/-- The equivalence between `right_moves` for a `pgame` constructed using `of s`, and `R s`. -/
def right_moves_of (s : S) : right_moves (of s) ≃ { t // t ∈ R s } :=
  right_moves_of_aux _ _

/--
The relabelling showing `move_left` applied to a game constructed using `of_aux`
has itself been constructed using `of_aux`.
-/
def relabelling_move_left_aux (n : ℕ) {s : S} (h : turn_bound s ≤ n) (t : left_moves (of_aux n s h)) :
  relabelling (move_left (of_aux n s h) t)
    (of_aux (n - 1) ((left_moves_of_aux n h) t : S)
      (turn_bound_of_left ((left_moves_of_aux n h) t).2 (n - 1) (Nat.le_transₓ h le_tsub_add))) :=
  by 
    induction n
    ·
      have t' := (left_moves_of_aux 0 h) t 
      exfalso 
      exact turn_bound_ne_zero_of_left_move t'.2 (nonpos_iff_eq_zero.mp h)
    ·
      rfl

/--
The relabelling showing `move_left` applied to a game constructed using `of`
has itself been constructed using `of`.
-/
def relabelling_move_left (s : S) (t : left_moves (of s)) :
  relabelling (move_left (of s) t) (of ((left_moves_of s).toFun t : S)) :=
  by 
    trans 
    apply relabelling_move_left_aux 
    apply of_aux_relabelling

/--
The relabelling showing `move_right` applied to a game constructed using `of_aux`
has itself been constructed using `of_aux`.
-/
def relabelling_move_right_aux (n : ℕ) {s : S} (h : turn_bound s ≤ n) (t : right_moves (of_aux n s h)) :
  relabelling (move_right (of_aux n s h) t)
    (of_aux (n - 1) ((right_moves_of_aux n h) t : S)
      (turn_bound_of_right ((right_moves_of_aux n h) t).2 (n - 1) (Nat.le_transₓ h le_tsub_add))) :=
  by 
    induction n
    ·
      have t' := (right_moves_of_aux 0 h) t 
      exfalso 
      exact turn_bound_ne_zero_of_right_move t'.2 (nonpos_iff_eq_zero.mp h)
    ·
      rfl

/--
The relabelling showing `move_right` applied to a game constructed using `of`
has itself been constructed using `of`.
-/
def relabelling_move_right (s : S) (t : right_moves (of s)) :
  relabelling (move_right (of s) t) (of ((right_moves_of s).toFun t : S)) :=
  by 
    trans 
    apply relabelling_move_right_aux 
    apply of_aux_relabelling

instance fintype_left_moves_of_aux (n : ℕ) (s : S) (h : turn_bound s ≤ n) : Fintype (left_moves (of_aux n s h)) :=
  by 
    apply Fintype.ofEquiv _ (left_moves_of_aux _ _).symm 
    infer_instance

instance fintype_right_moves_of_aux (n : ℕ) (s : S) (h : turn_bound s ≤ n) : Fintype (right_moves (of_aux n s h)) :=
  by 
    apply Fintype.ofEquiv _ (right_moves_of_aux _ _).symm 
    infer_instance

instance short_of_aux : ∀ n : ℕ {s : S} h : turn_bound s ≤ n, short (of_aux n s h)
| 0, s, h =>
  short.mk'
    (fun i =>
      by 
        have i := (left_moves_of_aux _ _).toFun i 
        exfalso 
        exact turn_bound_ne_zero_of_left_move i.2 (nonpos_iff_eq_zero.mp h))
    fun j =>
      by 
        have j := (right_moves_of_aux _ _).toFun j 
        exfalso 
        exact turn_bound_ne_zero_of_right_move j.2 (nonpos_iff_eq_zero.mp h)
| n+1, s, h =>
  short.mk' (fun i => short_of_relabelling (relabelling_move_left_aux (n+1) h i).symm (short_of_aux n _))
    fun j => short_of_relabelling (relabelling_move_right_aux (n+1) h j).symm (short_of_aux n _)

instance short_of (s : S) : short (of s) :=
  by 
    dsimp [Pgame.of]
    infer_instance

end Pgame

namespace Game

/-- Construct a combinatorial `game` from a state. -/
def of {S : Type u} [Pgame.State S] (s : S) : Game :=
  ⟦Pgame.of s⟧

end Game

