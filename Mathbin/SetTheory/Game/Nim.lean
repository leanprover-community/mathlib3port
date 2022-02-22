/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Markus Himmel
-/
import Mathbin.Data.Nat.Bitwise
import Mathbin.SetTheory.Game.Impartial
import Mathbin.SetTheory.OrdinalArithmetic

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

/-- `ordinal.out` and `ordinal.type_out'` are required to make the definition of nim computable.
 `ordinal.out` performs the same job as `quotient.out` but is specific to ordinals. -/
def Ordinal.out (o : Ordinal) : WellOrder :=
  ⟨o.out.α, fun x y => o.out.R x y, o.out.wo⟩

/-- This is the same as `ordinal.type_out` but defined to use `ordinal.out`. -/
theorem Ordinal.type_out' : ∀ o : Ordinal, Ordinal.type (Ordinal.out o).R = o :=
  Ordinal.type_out

/-- The definition of single-heap nim, which can be viewed as a pile of stones where each player can
 take a positive number of stones from it on their turn. -/
def nim : Ordinal → Pgame
  | O₁ =>
    ⟨O₁.out.α, O₁.out.α, fun O₂ =>
      have hwf : Ordinal.typein O₁.out.R O₂ < O₁ := by
        nth_rw_rhs 0[← Ordinal.type_out' O₁]
        exact Ordinal.typein_lt_type _ _
      nim (Ordinal.typein O₁.out.R O₂),
      fun O₂ =>
      have hwf : Ordinal.typein O₁.out.R O₂ < O₁ := by
        nth_rw_rhs 0[← Ordinal.type_out' O₁]
        exact Ordinal.typein_lt_type _ _
      nim (Ordinal.typein O₁.out.R O₂)⟩

namespace Pgame

-- mathport name: «expr ≈ »
local infixl:0 " ≈ " => Equiv

namespace nim

open Ordinal

theorem nim_def (O : Ordinal) :
    nim O =
      Pgame.mk O.out.α O.out.α (fun O₂ => nim (Ordinal.typein O.out.R O₂)) fun O₂ => nim (Ordinal.typein O.out.R O₂) :=
  by
  rw [nim]

theorem nim_wf_lemma {O₁ : Ordinal} (O₂ : O₁.out.α) : Ordinal.typein O₁.out.R O₂ < O₁ := by
  nth_rw_rhs 0[← Ordinal.type_out O₁]
  exact Ordinal.typein_lt_type _ _

instance nim_impartial : ∀ O : Ordinal, Impartial (nim O)
  | O => by
    rw [impartial_def, nim_def, neg_def]
    constructor
    constructor
    · rw [Pgame.le_def]
      constructor
      · intro i
        let hwf : typein O.out.r i < O := nim_wf_lemma i
        exact Or.inl ⟨i, (@impartial.neg_equiv_self _ <| nim_impartial <| typein O.out.r i).1⟩
        
      · intro j
        let hwf : typein O.out.r j < O := nim_wf_lemma j
        exact Or.inr ⟨j, (@impartial.neg_equiv_self _ <| nim_impartial <| typein O.out.r j).1⟩
        
      
    · rw [Pgame.le_def]
      constructor
      · intro i
        let hwf : typein O.out.r i < O := nim_wf_lemma i
        exact Or.inl ⟨i, (@impartial.neg_equiv_self _ <| nim_impartial <| typein O.out.r i).2⟩
        
      · intro j
        let hwf : typein O.out.r j < O := nim_wf_lemma j
        exact Or.inr ⟨j, (@impartial.neg_equiv_self _ <| nim_impartial <| typein O.out.r j).2⟩
        
      
    constructor
    · intro i
      let hwf : typein O.out.r i < O := nim_wf_lemma i
      simpa using nim_impartial (typein O.out.r i)
      
    · intro j
      let hwf : typein O.out.r j < O := nim_wf_lemma j
      simpa using nim_impartial (typein O.out.r j)
      

theorem exists_ordinal_move_left_eq (O : Ordinal) : ∀ i, ∃ O' < O, (nim O).moveLeft i = nim O' := by
  rw [nim_def]
  exact fun i => ⟨Ordinal.typein O.out.r i, ⟨nim_wf_lemma _, rfl⟩⟩

theorem exists_move_left_eq (O : Ordinal) : ∀, ∀ O' < O, ∀, ∃ i, (nim O).moveLeft i = nim O' := by
  rw [nim_def]
  exact fun _ h =>
    ⟨(Ordinal.principalSegOut h).top, by
      simp ⟩

theorem zero_first_loses : (nim (0 : Ordinal)).FirstLoses := by
  rw [impartial.first_loses_symm, nim_def, le_def_lt]
  constructor
  · rintro (i : (0 : Ordinal).out.α)
    have h := Ordinal.typein_lt_type _ i
    rw [Ordinal.type_out] at h
    exact False.elim (not_le_of_lt h (Ordinal.zero_le (Ordinal.typein _ i)))
    
  · tidy
    

theorem non_zero_first_wins (O : Ordinal) (hO : O ≠ 0) : (nim O).FirstWins := by
  rw [impartial.first_wins_symm, nim_def, lt_def_le]
  rw [← Ordinal.pos_iff_ne_zero] at hO
  exact
    Or.inr
      ⟨(Ordinal.principalSegOut hO).top, by
        simpa using zero_first_loses.1⟩

theorem sum_first_loses_iff_eq (O₁ O₂ : Ordinal) : (nim O₁ + nim O₂).FirstLoses ↔ O₁ = O₂ := by
  constructor
  · contrapose
    intro h
    rw [impartial.not_first_loses]
    wlog h' : O₁ ≤ O₂ using O₁ O₂, O₂ O₁
    · exact Ordinal.le_total O₁ O₂
      
    · have h : O₁ < O₂ := lt_of_le_of_neₓ h' h
      rw [impartial.first_wins_symm', lt_def_le, nim_def O₂]
      refine' Or.inl ⟨(left_moves_add (nim O₁) _).symm (Sum.inr _), _⟩
      · exact (Ordinal.principalSegOut h).top
        
      · simpa using (impartial.add_self (nim O₁)).2
        
      
    · exact first_wins_of_equiv add_comm_equiv (this (Ne.symm h))
      
    
  · rintro rfl
    exact impartial.add_self (nim O₁)
    

theorem sum_first_wins_iff_neq (O₁ O₂ : Ordinal) : (nim O₁ + nim O₂).FirstWins ↔ O₁ ≠ O₂ := by
  rw [iff_not_comm, impartial.not_first_wins, sum_first_loses_iff_eq]

theorem equiv_iff_eq (O₁ O₂ : Ordinal) : (nim O₁ ≈ nim O₂) ↔ O₁ = O₂ :=
  ⟨fun h =>
    (sum_first_loses_iff_eq _ _).1 <| by
      rw [first_loses_of_equiv_iff (add_congr h (equiv_refl _)), sum_first_loses_iff_eq],
    by
    rintro rfl
    rfl⟩

end nim

/-- This definition will be used in the proof of the Sprague-Grundy theorem. It takes a function
  from some type to ordinals and returns a nonempty set of ordinals with empty intersection with
  the image of the function. It is guaranteed that the smallest ordinal not in the image will be
  in the set, i.e. we can use this to find the mex. -/
def Nonmoves {α : Type u} (M : α → Ordinal.{u}) : Set Ordinal.{u} :=
  { O : Ordinal | ¬∃ a : α, M a = O }

theorem nonmoves_nonempty {α : Type u} (M : α → Ordinal.{u}) : ∃ O : Ordinal, O ∈ Nonmoves M := by
  classical
  by_contra h
  simp only [nonmoves, not_exists, not_forall, Set.mem_set_of_eq, not_not] at h
  have hle : Cardinal.univ.{u, u + 1} ≤ Cardinal.lift.{u + 1} (Cardinal.mk α) := by
    refine' ⟨⟨fun ⟨O⟩ => ⟨Classical.some (h O)⟩, _⟩⟩
    rintro ⟨O₁⟩ ⟨O₂⟩ heq
    ext
    refine' Eq.trans (Classical.some_spec (h O₁)).symm _
    injection HEq with heq
    rw [HEq]
    exact Classical.some_spec (h O₂)
  have hlt : Cardinal.lift.{u + 1} (Cardinal.mk α) < Cardinal.univ.{u, u + 1} := Cardinal.lt_univ.2 ⟨Cardinal.mk α, rfl⟩
  cases hlt
  contradiction

/-- The Grundy value of an impartial game, the ordinal which corresponds to the game of nim that the
 game is equivalent to -/
noncomputable def grundyValue : ∀ G : Pgame.{u} [G.Impartial], Ordinal.{u}
  | G => fun hG => Inf (nonmoves fun i => grundy_value (G.move_left i))

theorem grundy_value_def (G : Pgame) [G.Impartial] :
    grundyValue G = inf (Nonmoves fun i => grundyValue (G.moveLeft i)) := by
  rw [grundy_value]

/-- The Sprague-Grundy theorem which states that every impartial game is equivalent to a game of
 nim, namely the game of nim corresponding to the games Grundy value -/
theorem equiv_nim_grundy_value : ∀ G : Pgame.{u} [G.Impartial], G ≈ nim (grundy_value G)
  | G => by
    classical
    intro hG
    rw [impartial.equiv_iff_sum_first_loses, ← impartial.no_good_left_moves_iff_first_loses]
    intro i
    equiv_rw left_moves_add G (nim (grundy_value G))  at i
    cases' i with i₁ i₂
    · rw [add_move_left_inl]
      apply first_wins_of_equiv (add_congr (equiv_nim_grundy_value (G.move_left i₁)).symm (equiv_refl _))
      rw [nim.sum_first_wins_iff_neq]
      intro heq
      rw [eq_comm, grundy_value_def G] at heq
      have h := Inf_mem (nonmoves_nonempty _)
      rw [HEq] at h
      have hcontra :
        ∃ i' : G.left_moves,
          (fun i'' : G.left_moves => grundy_value (G.move_left i'')) i' = grundy_value (G.move_left i₁) :=
        ⟨i₁, rfl⟩
      contradiction
      
    · rw [add_move_left_inr, ← impartial.good_left_move_iff_first_wins]
      revert i₂
      rw [nim.nim_def]
      intro i₂
      have h' :
        ∃ i : G.left_moves, grundy_value (G.move_left i) = Ordinal.typein (Quotientₓ.out (grundy_value G)).R i₂ := by
        have hlt :
          Ordinal.typein (Quotientₓ.out (grundy_value G)).R i₂ < Ordinal.type (Quotientₓ.out (grundy_value G)).R :=
          Ordinal.typein_lt_type _ _
        rw [Ordinal.type_out] at hlt
        revert i₂ hlt
        rw [grundy_value_def]
        intro i₂ hlt
        have hnotin :
          Ordinal.typein (Inf (nonmoves fun i => grundy_value (G.move_left i))).out.R i₂ ∉
            nonmoves fun i : G.left_moves => grundy_value (G.move_left i) :=
          by
          intro hin
          have hge := cInf_le' hin
          have hcontra := (le_not_le_of_ltₓ hlt).2
          contradiction
        simpa [nonmoves] using hnotin
      cases' h' with i hi
      use (left_moves_add _ _).symm (Sum.inl i)
      rw [add_move_left_inl, move_left_mk]
      apply first_loses_of_equiv (add_congr (equiv_symm (equiv_nim_grundy_value (G.move_left i))) (equiv_refl _))
      simpa only [hi] using impartial.add_self (nim (grundy_value (G.move_left i)))
      

theorem equiv_nim_iff_grundy_value_eq (G : Pgame) [G.Impartial] (O : Ordinal) : (G ≈ nim O) ↔ grundyValue G = O :=
  ⟨by
    intro h
    rw [← nim.equiv_iff_eq]
    exact equiv_trans (equiv_symm (equiv_nim_grundy_value G)) h, by
    rintro rfl
    exact equiv_nim_grundy_value G⟩

theorem Nim.grundy_value (O : Ordinal.{u}) : grundyValue (nim O) = O := by
  rw [← equiv_nim_iff_grundy_value_eq]

theorem equiv_iff_grundy_value_eq (G H : Pgame) [G.Impartial] [H.Impartial] : (G ≈ H) ↔ grundyValue G = grundyValue H :=
  (equiv_congr_left.1 (equiv_nim_grundy_value H) _).trans <| equiv_nim_iff_grundy_value_eq _ _

theorem grundy_value_zero : grundyValue 0 = 0 := by
  rw [(equiv_iff_grundy_value_eq 0 (nim 0)).1 (equiv_symm nim.zero_first_loses), nim.grundy_value]

theorem equiv_zero_iff_grundy_value (G : Pgame) [G.Impartial] : (G ≈ 0) ↔ grundyValue G = 0 := by
  rw [equiv_iff_grundy_value_eq, grundy_value_zero]

theorem grundy_value_nim_add_nim (n m : ℕ) : grundyValue (nim n + nim m) = Nat.lxor n m := by
  induction' n using Nat.strong_induction_onₓ with n hn generalizing m
  induction' m using Nat.strong_induction_onₓ with m hm
  rw [grundy_value_def]
  -- We want to show that `n xor m` is the smallest unreachable Grundy value. We will do this in two
  -- steps:
  -- h₀: `n xor m` is not a reachable grundy number.
  -- h₁: every Grundy number strictly smaller than `n xor m` is reachable.
  have h₀ : (Nat.lxor n m : Ordinal) ∈ nonmoves fun i => grundy_value ((nim n + nim m).moveLeft i) := by
    -- To show that `n xor m` is unreachable, we show that every move produces a Grundy number
    -- different from `n xor m`.
    simp only [nonmoves, not_exists, Set.mem_set_of_eq]
    equiv_rw left_moves_add _ _
    -- The move operates either on the left pile or on the right pile.
    rintro (a | a)
    all_goals
      -- One of the piles is reduced to `k` stones, with `k < n` or `k < m`.
      obtain ⟨ok, ⟨hk, hk'⟩⟩ := nim.exists_ordinal_move_left_eq _ a
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
      exact _root_.ne_of_lt hk (Nat.lxor_left_inj h)
  have h₁ : ∀ u : Ordinal, u < Nat.lxor n m → u ∉ nonmoves fun i => grundy_value ((nim n + nim m).moveLeft i) := by
    -- Take any natural number `u` less than `n xor m`.
    intro ou hu
    obtain ⟨u, rfl⟩ := Ordinal.lt_omega.1 (lt_transₓ hu (Ordinal.nat_lt_omega _))
    replace hu := Ordinal.nat_cast_lt.1 hu
    -- Our goal is to produce a move that gives the Grundy value `u`.
    simp only [nonmoves, not_exists, not_not, Set.mem_set_of_eq, not_forall]
    -- By a lemma about xor, either `u xor m < n` or `u xor n < m`.
    have : Nat.lxor u (Nat.lxor n m) ≠ 0 := by
      intro h
      rw [Nat.lxor_eq_zero] at h
      linarith
    rcases Nat.lxor_trichotomy this with (h | h | h)
    · linarith
      
    -- Therefore, we can play the corresponding move, and by the inductive hypothesis the new state
    -- is `(u xor m) xor m = u` or `n xor (u xor n) = u` as required.
    · obtain ⟨i, hi⟩ := nim.exists_move_left_eq _ _ (Ordinal.nat_cast_lt.2 h)
      refine' ⟨(left_moves_add _ _).symm (Sum.inl i), _⟩
      simp only [hi, add_move_left_inl]
      rw [hn _ h, Nat.lxor_assoc, Nat.lxor_self, Nat.lxor_zero]
      
    · obtain ⟨i, hi⟩ := nim.exists_move_left_eq _ _ (Ordinal.nat_cast_lt.2 h)
      refine' ⟨(left_moves_add _ _).symm (Sum.inr i), _⟩
      simp only [hi, add_move_left_inr]
      rw [hm _ h, Nat.lxor_comm, Nat.lxor_assoc, Nat.lxor_self, Nat.lxor_zero]
      
  -- We are done!
  apply le_antisymmₓ (cInf_le' h₀)
  contrapose! h₁
  exact ⟨_, ⟨h₁, Inf_mem (nonmoves_nonempty _)⟩⟩

theorem nim_add_nim_equiv {n m : ℕ} : nim n + nim m ≈ nim (Nat.lxor n m) := by
  rw [equiv_nim_iff_grundy_value_eq, grundy_value_nim_add_nim]

theorem grundy_value_add (G H : Pgame) [G.Impartial] [H.Impartial] {n m : ℕ} (hG : grundyValue G = n)
    (hH : grundyValue H = m) : grundyValue (G + H) = Nat.lxor n m := by
  rw [← nim.grundy_value (Nat.lxor n m), ← equiv_iff_grundy_value_eq]
  refine' equiv_trans _ nim_add_nim_equiv
  convert add_congr (equiv_nim_grundy_value G) (equiv_nim_grundy_value H) <;> simp only [hG, hH]

end Pgame

