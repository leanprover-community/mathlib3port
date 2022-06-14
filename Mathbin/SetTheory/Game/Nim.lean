/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Markus Himmel
-/
import Mathbin.Data.Nat.Bitwise
import Mathbin.SetTheory.Game.Birthday
import Mathbin.SetTheory.Game.Impartial

/-!
# Nim and the Sprague-Grundy theorem

This file contains the definition for nim for any ordinal `O`. In the game of `nim O₁` both players
may move to `nim O₂` for any `O₂ < O₁`.
We also define a Grundy value for an impartial game `G` and prove the Sprague-Grundy theorem, that
`G` is equivalent to `nim (grundy_value G)`.
Finally, we compute the sum of finite Grundy numbers: if `G` and `H` have Grundy values `n` and `m`,
where `n` and `m` are natural numbers, then `G + H` has the Grundy value `n xor m`.

## Implementation details

The pen-and-paper definition of nim defines the possible moves of `nim O` to be `{O' | O' < O}`.
However, this definition does not work for us because it would make the type of nim
`ordinal.{u} → pgame.{u + 1}`, which would make it impossible for us to state the Sprague-Grundy
theorem, since that requires the type of `nim` to be `ordinal.{u} → pgame.{u}`. For this reason, we
instead use `O.out.α` for the possible moves, which makes proofs significantly more messy and
tedious, but avoids the universe bump.

The lemma `nim_def` is somewhat prone to produce "motive is not type correct" errors. If you run
into this problem, you may find the lemmas `exists_ordinal_move_left_eq` and `exists_move_left_eq`
useful.

-/


universe u

/-- `ordinal.out'` has the sole purpose of making `nim` computable. It performs the same job as
  `quotient.out` but is specific to ordinals. -/
def Ordinal.out' (o : Ordinal) : WellOrder :=
  ⟨o.out.α, (· < ·), o.out.wo⟩

/-- The definition of single-heap nim, which can be viewed as a pile of stones where each player can
  take a positive number of stones from it on their turn. -/
def nim : Ordinal → Pgame
  | O₁ =>
    let f := fun O₂ =>
      have hwf : Ordinal.typein O₁.out'.R O₂ < O₁ := Ordinal.typein_lt_self O₂
      nim (Ordinal.typein O₁.out'.R O₂)
    ⟨O₁.out'.α, O₁.out'.α, f, f⟩

namespace Pgame

-- mathport name: «expr ≈ »
local infixl:0 " ≈ " => Equiv

namespace nim

open Ordinal

theorem nim_def (O : Ordinal) :
    nim O =
      Pgame.mk O.out.α O.out.α (fun O₂ => nim (Ordinal.typein (· < ·) O₂)) fun O₂ => nim (Ordinal.typein (· < ·) O₂) :=
  by
  rw [nim]
  rfl

instance : IsEmpty (nim 0).LeftMoves := by
  rw [nim_def]
  exact Ordinal.is_empty_out_zero

instance : IsEmpty (nim 0).RightMoves := by
  rw [nim_def]
  exact Ordinal.is_empty_out_zero

noncomputable instance : Unique (nim 1).LeftMoves := by
  rw [nim_def]
  exact Ordinal.uniqueOutOne

noncomputable instance : Unique (nim 1).RightMoves := by
  rw [nim_def]
  exact Ordinal.uniqueOutOne

/-- `nim 0` has exactly the same moves as `0`. -/
def nimZeroRelabelling : Relabelling (nim 0) 0 :=
  Relabelling.isEmpty _

@[simp]
theorem nim_zero_equiv : nim 0 ≈ 0 :=
  Equiv.is_empty _

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:42:50: missing argument
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:60:31: expecting tactic arg
/-- `nim 1` has exactly the same moves as `star`. -/
noncomputable def nimOneRelabelling : Relabelling (nim 1) star := by
  rw [nim_def]
  refine' ⟨_, _, fun i => _, fun j => _⟩
  any_goals {
  }
  all_goals
    simp
    exact nim_zero_relabelling

@[simp]
theorem nim_one_equiv : nim 1 ≈ star :=
  nimOneRelabelling.Equiv

@[simp]
theorem nim_birthday (O : Ordinal) : (nim O).birthday = O := by
  induction' O using Ordinal.induction with O IH
  rw [nim_def, birthday_def]
  dsimp'
  rw [max_eq_rightₓ le_rfl]
  convert lsub_typein O
  exact funext fun i => IH _ (typein_lt_self i)

theorem left_moves_nim (O : Ordinal) : (nim O).LeftMoves = O.out.α := by
  rw [nim_def]
  rfl

theorem right_moves_nim (O : Ordinal) : (nim O).RightMoves = O.out.α := by
  rw [nim_def]
  rfl

theorem move_left_nim_heq (O : Ordinal) : HEq (nim O).moveLeft fun i : O.out.α => nim (typein (· < ·) i) := by
  rw [nim_def]
  rfl

theorem move_right_nim_heq (O : Ordinal) : HEq (nim O).moveRight fun i : O.out.α => nim (typein (· < ·) i) := by
  rw [nim_def]
  rfl

/-- Turns an ordinal less than `O` into a left move for `nim O` and viceversa. -/
noncomputable def toLeftMovesNim {O : Ordinal} : Set.Iio O ≃ (nim O).LeftMoves :=
  (enumIsoOut O).toEquiv.trans (Equivₓ.cast (left_moves_nim O).symm)

/-- Turns an ordinal less than `O` into a right move for `nim O` and viceversa. -/
noncomputable def toRightMovesNim {O : Ordinal} : Set.Iio O ≃ (nim O).RightMoves :=
  (enumIsoOut O).toEquiv.trans (Equivₓ.cast (right_moves_nim O).symm)

@[simp]
theorem to_left_moves_nim_symm_lt {O : Ordinal} (i : (nim O).LeftMoves) : ↑(toLeftMovesNim.symm i) < O :=
  (toLeftMovesNim.symm i).Prop

@[simp]
theorem to_right_moves_nim_symm_lt {O : Ordinal} (i : (nim O).RightMoves) : ↑(toRightMovesNim.symm i) < O :=
  (toRightMovesNim.symm i).Prop

@[simp]
theorem move_left_nim' {O : Ordinal.{u}} i : (nim O).moveLeft i = nim (toLeftMovesNim.symm i).val :=
  (congr_heq (move_left_nim_heq O).symm (cast_heq _ i)).symm

theorem move_left_nim {O : Ordinal} i : (nim O).moveLeft (toLeftMovesNim i) = nim i := by
  simp

@[simp]
theorem move_right_nim' {O : Ordinal} i : (nim O).moveRight i = nim (toRightMovesNim.symm i).val :=
  (congr_heq (move_right_nim_heq O).symm (cast_heq _ i)).symm

theorem move_right_nim {O : Ordinal} i : (nim O).moveRight (toRightMovesNim i) = nim i := by
  simp

@[simp]
theorem neg_nim (O : Ordinal) : -nim O = nim O := by
  induction' O using Ordinal.induction with O IH
  rw [nim_def]
  dsimp' <;> congr <;> funext i <;> exact IH _ (Ordinal.typein_lt_self i)

instance nim_impartial (O : Ordinal) : Impartial (nim O) := by
  induction' O using Ordinal.induction with O IH
  rw [impartial_def, neg_nim]
  refine' ⟨equiv_rfl, fun i => _, fun i => _⟩ <;> simpa using IH _ (typein_lt_self _)

theorem exists_ordinal_move_left_eq {O : Ordinal} i : ∃ O' < O, (nim O).moveLeft i = nim O' :=
  ⟨_, typein_lt_self _, move_left_nim' i⟩

theorem exists_move_left_eq {O O' : Ordinal} (h : O' < O) : ∃ i, (nim O).moveLeft i = nim O' :=
  ⟨toLeftMovesNim ⟨O', h⟩, by
    simp ⟩

@[simp]
theorem zero_first_loses : (nim (0 : Ordinal)).FirstLoses :=
  Equiv.is_empty _

theorem non_zero_first_wins {O : Ordinal} (hO : O ≠ 0) : (nim O).FirstWins := by
  rw [impartial.first_wins_symm, nim_def, lf_iff_forall_le]
  rw [← Ordinal.pos_iff_ne_zero] at hO
  exact
    Or.inr
      ⟨(Ordinal.principalSegOut hO).top, by
        simp ⟩

@[simp]
theorem sum_first_loses_iff_eq (O₁ O₂ : Ordinal) : (nim O₁ + nim O₂).FirstLoses ↔ O₁ = O₂ := by
  constructor
  · contrapose
    intro h
    rw [impartial.not_first_loses]
    wlog h' : O₁ ≤ O₂ using O₁ O₂, O₂ O₁
    · exact le_totalₓ O₁ O₂
      
    · have h : O₁ < O₂ := lt_of_le_of_neₓ h' h
      rw [impartial.first_wins_symm', lf_iff_forall_le, nim_def O₂]
      refine' Or.inl ⟨to_left_moves_add (Sum.inr _), _⟩
      · exact (Ordinal.principalSegOut h).top
        
      · simpa using (impartial.add_self (nim O₁)).2
        
      
    · exact first_wins_of_equiv add_comm_equiv (this (Ne.symm h))
      
    
  · rintro rfl
    exact impartial.add_self (nim O₁)
    

@[simp]
theorem sum_first_wins_iff_neq (O₁ O₂ : Ordinal) : (nim O₁ + nim O₂).FirstWins ↔ O₁ ≠ O₂ := by
  rw [iff_not_comm, impartial.not_first_wins, sum_first_loses_iff_eq]

@[simp]
theorem equiv_iff_eq (O₁ O₂ : Ordinal) : (nim O₁ ≈ nim O₂) ↔ O₁ = O₂ :=
  ⟨fun h =>
    (sum_first_loses_iff_eq _ _).1 <| by
      rw [first_loses_of_equiv_iff (add_congr_left h), sum_first_loses_iff_eq],
    by
    rintro rfl
    rfl⟩

end nim

/-- The Grundy value of an impartial game, the ordinal which corresponds to the game of nim that the
 game is equivalent to -/
noncomputable def grundyValue : ∀ G : Pgame.{u}, Ordinal.{u}
  | G => Ordinal.mex.{u, u} fun i => grundy_value (G.moveLeft i)

theorem grundy_value_def (G : Pgame) : grundyValue G = Ordinal.mex.{u, u} fun i => grundyValue (G.moveLeft i) := by
  rw [grundy_value]

/-- The Sprague-Grundy theorem which states that every impartial game is equivalent to a game of
 nim, namely the game of nim corresponding to the games Grundy value -/
theorem equiv_nim_grundy_value : ∀ G : Pgame.{u} [G.Impartial], G ≈ nim (grundyValue G)
  | G => by
    intro hG
    rw [impartial.equiv_iff_sum_first_loses, ← impartial.no_good_left_moves_iff_first_loses]
    intro i
    apply left_moves_add_cases i
    · intro i₁
      rw [add_move_left_inl]
      apply first_wins_of_equiv (add_congr_left (equiv_nim_grundy_value (G.move_left i₁)).symm)
      rw [nim.sum_first_wins_iff_neq]
      intro heq
      rw [eq_comm, grundy_value_def G] at heq
      have h := Ordinal.ne_mex _
      rw [HEq] at h
      exact (h i₁).irrefl
      
    · intro i₂
      rw [add_move_left_inr, ← impartial.good_left_move_iff_first_wins]
      revert i₂
      rw [nim.nim_def]
      intro i₂
      have h' :
        ∃ i : G.left_moves, grundy_value (G.move_left i) = Ordinal.typein (Quotientₓ.out (grundy_value G)).R i₂ := by
        revert i₂
        rw [grundy_value_def]
        intro i₂
        have hnotin : _ ∉ _ := fun hin => (le_not_le_of_ltₓ (Ordinal.typein_lt_self i₂)).2 (cInf_le' hin)
        simpa using hnotin
      cases' h' with i hi
      use to_left_moves_add (Sum.inl i)
      rw [add_move_left_inl, move_left_mk]
      apply first_loses_of_equiv (add_congr_left (equiv_nim_grundy_value (G.move_left i)).symm)
      simpa only [hi] using impartial.add_self (nim (grundy_value (G.move_left i)))
      

@[simp]
theorem grundy_value_eq_iff_equiv_nim (G : Pgame) [G.Impartial] (O : Ordinal) : grundyValue G = O ↔ (G ≈ nim O) :=
  ⟨by
    rintro rfl
    exact equiv_nim_grundy_value G, by
    intro h
    rw [← nim.equiv_iff_eq]
    exact (equiv_nim_grundy_value G).symm.trans h⟩

theorem Nim.grundy_value (O : Ordinal.{u}) : grundyValue (nim O) = O := by
  simp

@[simp]
theorem grundy_value_eq_iff_equiv (G H : Pgame) [G.Impartial] [H.Impartial] : grundyValue G = grundyValue H ↔ (G ≈ H) :=
  (grundy_value_eq_iff_equiv_nim _ _).trans (equiv_congr_left.1 (equiv_nim_grundy_value H) _).symm

@[simp]
theorem grundy_value_zero : grundyValue 0 = 0 := by
  simp [nim.nim_zero_equiv.symm]

@[simp]
theorem grundy_value_iff_equiv_zero (G : Pgame) [G.Impartial] : grundyValue G = 0 ↔ (G ≈ 0) := by
  rw [← grundy_value_eq_iff_equiv, grundy_value_zero]

theorem grundy_value_star : grundyValue star = 1 := by
  simp [nim.nim_one_equiv.symm]

@[simp]
theorem grundy_value_nim_add_nim (n m : ℕ) : grundyValue (nim.{u} n + nim.{u} m) = Nat.lxor n m := by
  induction' n using Nat.strong_induction_onₓ with n hn generalizing m
  induction' m using Nat.strong_induction_onₓ with m hm
  rw [grundy_value_def]
  -- We want to show that `n xor m` is the smallest unreachable Grundy value. We will do this in two
  -- steps:
  -- h₀: `n xor m` is not a reachable grundy number.
  -- h₁: every Grundy number strictly smaller than `n xor m` is reachable.
  have h₀ : ∀ i, grundy_value ((nim n + nim m).moveLeft i) ≠ (Nat.lxor n m : Ordinal) := by
    -- To show that `n xor m` is unreachable, we show that every move produces a Grundy number
    -- different from `n xor m`.
    intro i
    -- The move operates either on the left pile or on the right pile.
    apply left_moves_add_cases i
    all_goals
      -- One of the piles is reduced to `k` stones, with `k < n` or `k < m`.
      intro a
      obtain ⟨ok, hk, hk'⟩ := nim.exists_ordinal_move_left_eq a
      obtain ⟨k, rfl⟩ := Ordinal.lt_omega.1 (lt_transₓ hk (Ordinal.nat_lt_omega _))
      replace hk := Ordinal.nat_cast_lt.1 hk
      -- Thus, the problem is reduced to computing the Grundy value of `nim n + nim k` or
      -- `nim k + nim m`, both of which can be dealt with using an inductive hypothesis.
      simp only [hk', add_move_left_inl, add_move_left_inr, id]
      first |
        rw [hn _ hk]|
        rw [hm _ hk]
      -- But of course xor is injective, so if we change one of the arguments, we will not get the
      -- same value again.
      intro h
      rw [Ordinal.nat_cast_inj] at h
      try
        rw [Nat.lxor_comm n k, Nat.lxor_comm n m] at h
      exact hk.ne (Nat.lxor_left_inj h)
  have h₁ : ∀ u : Ordinal, u < Nat.lxor n m → u ∈ Set.Range fun i => grundy_value ((nim n + nim m).moveLeft i) := by
    -- Take any natural number `u` less than `n xor m`.
    intro ou hu
    obtain ⟨u, rfl⟩ := Ordinal.lt_omega.1 (lt_transₓ hu (Ordinal.nat_lt_omega _))
    replace hu := Ordinal.nat_cast_lt.1 hu
    -- Our goal is to produce a move that gives the Grundy value `u`.
    rw [Set.mem_range]
    -- By a lemma about xor, either `u xor m < n` or `u xor n < m`.
    have : Nat.lxor u (Nat.lxor n m) ≠ 0 := by
      intro h
      rw [Nat.lxor_eq_zero] at h
      linarith
    rcases Nat.lxor_trichotomy this with (h | h | h)
    · linarith
      
    -- Therefore, we can play the corresponding move, and by the inductive hypothesis the new state
    -- is `(u xor m) xor m = u` or `n xor (u xor n) = u` as required.
    · obtain ⟨i, hi⟩ := nim.exists_move_left_eq (Ordinal.nat_cast_lt.2 h)
      refine' ⟨to_left_moves_add (Sum.inl i), _⟩
      simp only [hi, add_move_left_inl]
      rw [hn _ h, Nat.lxor_assoc, Nat.lxor_self, Nat.lxor_zero]
      
    · obtain ⟨i, hi⟩ := nim.exists_move_left_eq (Ordinal.nat_cast_lt.2 h)
      refine' ⟨to_left_moves_add (Sum.inr i), _⟩
      simp only [hi, add_move_left_inr]
      rw [hm _ h, Nat.lxor_comm, Nat.lxor_assoc, Nat.lxor_self, Nat.lxor_zero]
      
  -- We are done!
  apply (Ordinal.mex_le_of_ne.{u, u} h₀).antisymm
  contrapose! h₁
  exact ⟨_, ⟨h₁, Ordinal.mex_not_mem_range _⟩⟩

theorem nim_add_nim_equiv {n m : ℕ} : nim n + nim m ≈ nim (Nat.lxor n m) := by
  rw [← grundy_value_eq_iff_equiv_nim, grundy_value_nim_add_nim]

theorem grundy_value_add (G H : Pgame) [G.Impartial] [H.Impartial] {n m : ℕ} (hG : grundyValue G = n)
    (hH : grundyValue H = m) : grundyValue (G + H) = Nat.lxor n m := by
  rw [← nim.grundy_value (Nat.lxor n m), grundy_value_eq_iff_equiv]
  refine' Equivₓ.trans _ nim_add_nim_equiv
  convert add_congr (equiv_nim_grundy_value G) (equiv_nim_grundy_value H) <;> simp only [hG, hH]

end Pgame

