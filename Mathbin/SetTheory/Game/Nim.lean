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
  ⟨o.out.α, fun x y => o.out.r x y, o.out.wo⟩

/-- This is the same as `ordinal.type_out` but defined to use `ordinal.out`. -/
theorem Ordinal.type_out' : ∀ o : Ordinal, Ordinal.type (Ordinal.out o).R = o :=
  Ordinal.type_out

/-- The definition of single-heap nim, which can be viewed as a pile of stones where each player can
 take a positive number of stones from it on their turn. -/
def nim : Ordinal → Pgame
| O₁ =>
  ⟨O₁.out.α, O₁.out.α,
    fun O₂ =>
      have hwf : Ordinal.typein O₁.out.r O₂ < O₁ :=
        by 
          nthRwRHS 0[←Ordinal.type_out' O₁]
          exact Ordinal.typein_lt_type _ _ 
      nim (Ordinal.typein O₁.out.r O₂),
    fun O₂ =>
      have hwf : Ordinal.typein O₁.out.r O₂ < O₁ :=
        by 
          nthRwRHS 0[←Ordinal.type_out' O₁]
          exact Ordinal.typein_lt_type _ _ 
      nim (Ordinal.typein O₁.out.r O₂)⟩

namespace Pgame

local infixl:0 " ≈ " => Equiv

namespace nim

open Ordinal

theorem nim_def (O : Ordinal) :
  nim O =
    Pgame.mk O.out.α O.out.α (fun O₂ => nim (Ordinal.typein O.out.r O₂)) fun O₂ => nim (Ordinal.typein O.out.r O₂) :=
  by 
    rw [nim]

theorem nim_wf_lemma {O₁ : Ordinal} (O₂ : O₁.out.α) : Ordinal.typein O₁.out.r O₂ < O₁ :=
  by 
    nthRwRHS 0[←Ordinal.type_out O₁]
    exact Ordinal.typein_lt_type _ _

instance nim_impartial : ∀ O : Ordinal, impartial (nim O)
| O =>
  by 
    rw [impartial_def, nim_def, neg_def]
    split 
    split 
    ·
      rw [Pgame.le_def]
      split 
      ·
        intro i 
        let hwf : typein O.out.r i < O := nim_wf_lemma i 
        exact Or.inl ⟨i, (@impartial.neg_equiv_self _$ nim_impartial$ typein O.out.r i).1⟩
      ·
        intro j 
        let hwf : typein O.out.r j < O := nim_wf_lemma j 
        exact Or.inr ⟨j, (@impartial.neg_equiv_self _$ nim_impartial$ typein O.out.r j).1⟩
    ·
      rw [Pgame.le_def]
      split 
      ·
        intro i 
        let hwf : typein O.out.r i < O := nim_wf_lemma i 
        exact Or.inl ⟨i, (@impartial.neg_equiv_self _$ nim_impartial$ typein O.out.r i).2⟩
      ·
        intro j 
        let hwf : typein O.out.r j < O := nim_wf_lemma j 
        exact Or.inr ⟨j, (@impartial.neg_equiv_self _$ nim_impartial$ typein O.out.r j).2⟩
    split 
    ·
      intro i 
      let hwf : typein O.out.r i < O := nim_wf_lemma i 
      simpa using nim_impartial (typein O.out.r i)
    ·
      intro j 
      let hwf : typein O.out.r j < O := nim_wf_lemma j 
      simpa using nim_impartial (typein O.out.r j)

theorem exists_ordinal_move_left_eq (O : Ordinal) : ∀ i, ∃ (O' : _)(_ : O' < O), (nim O).moveLeft i = nim O' :=
  by 
    rw [nim_def]
    exact fun i => ⟨Ordinal.typein O.out.r i, ⟨nim_wf_lemma _, rfl⟩⟩

theorem exists_move_left_eq (O : Ordinal) : ∀ O' _ : O' < O, ∃ i, (nim O).moveLeft i = nim O' :=
  by 
    rw [nim_def]
    exact
      fun _ h =>
        ⟨(Ordinal.principalSegOut h).top,
          by 
            simp ⟩

-- error in SetTheory.Game.Nim: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem zero_first_loses : (nim (0 : ordinal)).first_loses :=
begin
  rw ["[", expr impartial.first_loses_symm, ",", expr nim_def, ",", expr le_def_lt, "]"] [],
  split,
  { rintro ["(", ident i, ":", expr (0 : ordinal).out.α, ")"],
    have [ident h] [] [":=", expr ordinal.typein_lt_type _ i],
    rw [expr ordinal.type_out] ["at", ident h],
    exact [expr false.elim (not_le_of_lt h (ordinal.zero_le (ordinal.typein _ i)))] },
  { tidy [] }
end

theorem non_zero_first_wins (O : Ordinal) (hO : O ≠ 0) : (nim O).FirstWins :=
  by 
    rw [impartial.first_wins_symm, nim_def, lt_def_le]
    rw [←Ordinal.pos_iff_ne_zero] at hO 
    exact
      Or.inr
        ⟨(Ordinal.principalSegOut hO).top,
          by 
            simpa using zero_first_loses.1⟩

-- error in SetTheory.Game.Nim: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sum_first_loses_iff_eq
(O₁ O₂ : ordinal) : «expr ↔ »(«expr + »(nim O₁, nim O₂).first_loses, «expr = »(O₁, O₂)) :=
begin
  split,
  { contrapose [] [],
    intro [ident h],
    rw ["[", expr impartial.not_first_loses, "]"] [],
    wlog [ident h'] [":", expr «expr ≤ »(O₁, O₂)] [] ["using", "[", ident O₁, ident O₂, ",", ident O₂, ident O₁, "]"],
    { exact [expr ordinal.le_total O₁ O₂] },
    { have [ident h] [":", expr «expr < »(O₁, O₂)] [":=", expr lt_of_le_of_ne h' h],
      rw ["[", expr impartial.first_wins_symm', ",", expr lt_def_le, ",", expr nim_def O₂, "]"] [],
      refine [expr or.inl ⟨(left_moves_add (nim O₁) _).symm (sum.inr _), _⟩],
      { exact [expr (ordinal.principal_seg_out h).top] },
      { simpa [] [] [] [] [] ["using", expr (impartial.add_self (nim O₁)).2] } },
    { exact [expr first_wins_of_equiv add_comm_equiv (this (ne.symm h))] } },
  { rintro [ident rfl],
    exact [expr impartial.add_self (nim O₁)] }
end

theorem sum_first_wins_iff_neq (O₁ O₂ : Ordinal) : (nim O₁+nim O₂).FirstWins ↔ O₁ ≠ O₂ :=
  by 
    rw [iff_not_comm, impartial.not_first_wins, sum_first_loses_iff_eq]

theorem equiv_iff_eq (O₁ O₂ : Ordinal) : (nim O₁ ≈ nim O₂) ↔ O₁ = O₂ :=
  ⟨fun h =>
      (sum_first_loses_iff_eq _ _).1$
        by 
          rw [first_loses_of_equiv_iff (add_congr h (equiv_refl _)), sum_first_loses_iff_eq],
    by 
      rintro rfl 
      rfl⟩

end nim

/-- This definition will be used in the proof of the Sprague-Grundy theorem. It takes a function
  from some type to ordinals and returns a nonempty set of ordinals with empty intersection with
  the image of the function. It is guaranteed that the smallest ordinal not in the image will be
  in the set, i.e. we can use this to find the mex. -/
def nonmoves {α : Type u} (M : α → Ordinal.{u}) : Set Ordinal.{u} :=
  { O:Ordinal | ¬∃ a : α, M a = O }

-- error in SetTheory.Game.Nim: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem nonmoves_nonempty {α : Type u} (M : α → ordinal.{u}) : «expr∃ , »((O : ordinal), «expr ∈ »(O, nonmoves M)) :=
begin
  classical,
  by_contra [ident h],
  simp [] [] ["only"] ["[", expr nonmoves, ",", expr not_exists, ",", expr not_forall, ",", expr set.mem_set_of_eq, ",", expr not_not, "]"] [] ["at", ident h],
  have [ident hle] [":", expr «expr ≤ »(cardinal.univ.{u, u+1}, cardinal.lift.{u+1} (cardinal.mk α))] [],
  { refine [expr ⟨⟨λ ⟨O⟩, ⟨classical.some (h O)⟩, _⟩⟩],
    rintros ["⟨", ident O₁, "⟩", "⟨", ident O₂, "⟩", ident heq],
    ext [] [] [],
    refine [expr eq.trans (classical.some_spec (h O₁)).symm _],
    injection [expr heq] ["with", ident heq],
    rw [expr heq] [],
    exact [expr classical.some_spec (h O₂)] },
  have [ident hlt] [":", expr «expr < »(cardinal.lift.{u+1} (cardinal.mk α), cardinal.univ.{u, u+1})] [":=", expr cardinal.lt_univ.2 ⟨cardinal.mk α, rfl⟩],
  cases [expr hlt] [],
  contradiction
end

/-- The Grundy value of an impartial game, the ordinal which corresponds to the game of nim that the
 game is equivalent to -/
noncomputable def grundy_value : ∀ G : Pgame.{u} [G.impartial], Ordinal.{u}
| G =>
  fun hG =>
    by 
      exact Ordinal.omin (nonmoves fun i => grundy_value (G.move_left i)) (nonmoves_nonempty _)

theorem grundy_value_def (G : Pgame) [G.impartial] :
  grundy_value G = Ordinal.omin (nonmoves fun i => grundy_value (G.move_left i)) (nonmoves_nonempty _) :=
  by 
    rw [grundy_value]
    rfl

-- error in SetTheory.Game.Nim: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The Sprague-Grundy theorem which states that every impartial game is equivalent to a game of
 nim, namely the game of nim corresponding to the games Grundy value -/
theorem equiv_nim_grundy_value : ∀ (G : pgame.{u}) [G.impartial], by exactI [expr «expr ≈ »(G, nim (grundy_value G))]
| G := begin
  classical,
  introI [ident hG],
  rw ["[", expr impartial.equiv_iff_sum_first_loses, ",", "<-", expr impartial.no_good_left_moves_iff_first_loses, "]"] [],
  intro [ident i],
  equiv_rw [expr left_moves_add G (nim (grundy_value G))] ["at", ident i],
  cases [expr i] ["with", ident i₁, ident i₂],
  { rw [expr add_move_left_inl] [],
    apply [expr first_wins_of_equiv (add_congr (equiv_nim_grundy_value (G.move_left i₁)).symm (equiv_refl _))],
    rw [expr nim.sum_first_wins_iff_neq] [],
    intro [ident heq],
    rw ["[", expr eq_comm, ",", expr grundy_value_def G, "]"] ["at", ident heq],
    have [ident h] [] [":=", expr ordinal.omin_mem (nonmoves (λ
       i : G.left_moves, grundy_value (G.move_left i))) (nonmoves_nonempty _)],
    rw [expr heq] ["at", ident h],
    have [ident hcontra] [":", expr «expr∃ , »((i' : G.left_moves), «expr = »(λ
       i'' : G.left_moves, grundy_value (G.move_left i'') i', grundy_value (G.move_left i₁)))] [":=", expr ⟨i₁, rfl⟩],
    contradiction },
  { rw ["[", expr add_move_left_inr, ",", "<-", expr impartial.good_left_move_iff_first_wins, "]"] [],
    revert [ident i₂],
    rw [expr nim.nim_def] [],
    intro [ident i₂],
    have [ident h'] [":", expr «expr∃ , »((i : G.left_moves), «expr = »(grundy_value (G.move_left i), ordinal.typein (quotient.out (grundy_value G)).r i₂))] [],
    { have [ident hlt] [":", expr «expr < »(ordinal.typein (quotient.out (grundy_value G)).r i₂, ordinal.type (quotient.out (grundy_value G)).r)] [":=", expr ordinal.typein_lt_type _ _],
      rw [expr ordinal.type_out] ["at", ident hlt],
      revert [ident i₂, ident hlt],
      rw [expr grundy_value_def] [],
      intros [ident i₂, ident hlt],
      have [ident hnotin] [":", expr «expr ∉ »(ordinal.typein (quotient.out (ordinal.omin (nonmoves (λ
            i, grundy_value (G.move_left i))) _)).r i₂, nonmoves (λ
         i : G.left_moves, grundy_value (G.move_left i)))] [],
      { intro [ident hin],
        have [ident hge] [] [":=", expr ordinal.omin_le hin],
        have [ident hcontra] [] [":=", expr (le_not_le_of_lt hlt).2],
        contradiction },
      simpa [] [] [] ["[", expr nonmoves, "]"] [] ["using", expr hnotin] },
    cases [expr h'] ["with", ident i, ident hi],
    use [expr (left_moves_add _ _).symm (sum.inl i)],
    rw ["[", expr add_move_left_inl, ",", expr move_left_mk, "]"] [],
    apply [expr first_loses_of_equiv (add_congr (equiv_symm (equiv_nim_grundy_value (G.move_left i))) (equiv_refl _))],
    simpa [] [] ["only"] ["[", expr hi, "]"] [] ["using", expr impartial.add_self (nim (grundy_value (G.move_left i)))] }
end

theorem equiv_nim_iff_grundy_value_eq (G : Pgame) [G.impartial] (O : Ordinal) : (G ≈ nim O) ↔ grundy_value G = O :=
  ⟨by 
      intro h 
      rw [←nim.equiv_iff_eq]
      exact equiv_trans (equiv_symm (equiv_nim_grundy_value G)) h,
    by 
      rintro rfl 
      exact equiv_nim_grundy_value G⟩

theorem nim.grundy_value (O : Ordinal.{u}) : grundy_value (nim O) = O :=
  by 
    rw [←equiv_nim_iff_grundy_value_eq]

theorem equiv_iff_grundy_value_eq (G H : Pgame) [G.impartial] [H.impartial] :
  (G ≈ H) ↔ grundy_value G = grundy_value H :=
  (equiv_congr_left.1 (equiv_nim_grundy_value H) _).trans$ equiv_nim_iff_grundy_value_eq _ _

theorem grundy_value_zero : grundy_value 0 = 0 :=
  by 
    rw [(equiv_iff_grundy_value_eq 0 (nim 0)).1 (equiv_symm nim.zero_first_loses), nim.grundy_value]

theorem equiv_zero_iff_grundy_value (G : Pgame) [G.impartial] : (G ≈ 0) ↔ grundy_value G = 0 :=
  by 
    rw [equiv_iff_grundy_value_eq, grundy_value_zero]

-- error in SetTheory.Game.Nim: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem grundy_value_nim_add_nim (n m : exprℕ()) : «expr = »(grundy_value «expr + »(nim n, nim m), nat.lxor n m) :=
begin
  induction [expr n] ["using", ident nat.strong_induction_on] ["with", ident n, ident hn] ["generalizing", ident m],
  induction [expr m] ["using", ident nat.strong_induction_on] ["with", ident m, ident hm] [],
  rw ["[", expr grundy_value_def, "]"] [],
  have [ident h₀] [":", expr «expr ∈ »((nat.lxor n m : ordinal), nonmoves (λ
     i, grundy_value («expr + »(nim n, nim m).move_left i)))] [],
  { simp [] [] ["only"] ["[", expr nonmoves, ",", expr not_exists, ",", expr set.mem_set_of_eq, "]"] [] [],
    equiv_rw [expr left_moves_add _ _] [],
    rintro ["(", ident a, "|", ident a, ")"],
    all_goals { obtain ["⟨", ident ok, ",", "⟨", ident hk, ",", ident hk', "⟩", "⟩", ":=", expr nim.exists_ordinal_move_left_eq _ a],
      obtain ["⟨", ident k, ",", ident rfl, "⟩", ":=", expr ordinal.lt_omega.1 (lt_trans hk (ordinal.nat_lt_omega _))],
      replace [ident hk] [] [":=", expr ordinal.nat_cast_lt.1 hk],
      simp [] [] ["only"] ["[", expr hk', ",", expr add_move_left_inl, ",", expr add_move_left_inr, ",", expr id, "]"] [] [],
      rw [expr hn _ hk] [] <|> rw [expr hm _ hk] [],
      intro [ident h],
      rw [expr ordinal.nat_cast_inj] ["at", ident h],
      try { rw ["[", expr nat.lxor_comm n k, ",", expr nat.lxor_comm n m, "]"] ["at", ident h] },
      exact [expr _root_.ne_of_lt hk (nat.lxor_left_inj h)] } },
  have [ident h₁] [":", expr ∀
   u : ordinal, «expr < »(u, nat.lxor n m) → «expr ∉ »(u, nonmoves (λ
     i, grundy_value («expr + »(nim n, nim m).move_left i)))] [],
  { intros [ident ou, ident hu],
    obtain ["⟨", ident u, ",", ident rfl, "⟩", ":=", expr ordinal.lt_omega.1 (lt_trans hu (ordinal.nat_lt_omega _))],
    replace [ident hu] [] [":=", expr ordinal.nat_cast_lt.1 hu],
    simp [] [] ["only"] ["[", expr nonmoves, ",", expr not_exists, ",", expr not_not, ",", expr set.mem_set_of_eq, ",", expr not_forall, "]"] [] [],
    have [] [":", expr «expr ≠ »(nat.lxor u (nat.lxor n m), 0)] [],
    { intro [ident h],
      rw [expr nat.lxor_eq_zero] ["at", ident h],
      linarith [] [] [] },
    rcases [expr nat.lxor_trichotomy this, "with", ident h, "|", ident h, "|", ident h],
    { linarith [] [] [] },
    { obtain ["⟨", ident i, ",", ident hi, "⟩", ":=", expr nim.exists_move_left_eq _ _ (ordinal.nat_cast_lt.2 h)],
      refine [expr ⟨(left_moves_add _ _).symm (sum.inl i), _⟩],
      simp [] [] ["only"] ["[", expr hi, ",", expr add_move_left_inl, "]"] [] [],
      rw ["[", expr hn _ h, ",", expr nat.lxor_assoc, ",", expr nat.lxor_self, ",", expr nat.lxor_zero, "]"] [] },
    { obtain ["⟨", ident i, ",", ident hi, "⟩", ":=", expr nim.exists_move_left_eq _ _ (ordinal.nat_cast_lt.2 h)],
      refine [expr ⟨(left_moves_add _ _).symm (sum.inr i), _⟩],
      simp [] [] ["only"] ["[", expr hi, ",", expr add_move_left_inr, "]"] [] [],
      rw ["[", expr hm _ h, ",", expr nat.lxor_comm, ",", expr nat.lxor_assoc, ",", expr nat.lxor_self, ",", expr nat.lxor_zero, "]"] [] } },
  apply [expr le_antisymm (ordinal.omin_le h₀)],
  contrapose ["!"] [ident h₁],
  exact [expr ⟨_, ⟨h₁, ordinal.omin_mem _ _⟩⟩]
end

theorem nim_add_nim_equiv {n m : ℕ} : (nim n+nim m) ≈ nim (Nat.lxor n m) :=
  by 
    rw [equiv_nim_iff_grundy_value_eq, grundy_value_nim_add_nim]

theorem grundy_value_add (G H : Pgame) [G.impartial] [H.impartial] {n m : ℕ} (hG : grundy_value G = n)
  (hH : grundy_value H = m) : grundy_value (G+H) = Nat.lxor n m :=
  by 
    rw [←nim.grundy_value (Nat.lxor n m), ←equiv_iff_grundy_value_eq]
    refine' equiv_trans _ nim_add_nim_equiv 
    convert add_congr (equiv_nim_grundy_value G) (equiv_nim_grundy_value H) <;> simp only [hG, hH]

end Pgame

