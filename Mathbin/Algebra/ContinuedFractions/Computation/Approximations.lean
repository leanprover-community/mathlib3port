import Mathbin.Algebra.ContinuedFractions.Computation.CorrectnessTerminating 
import Mathbin.Data.Nat.Fib 
import Mathbin.Tactic.SolveByElim

/-!
# Approximations for Continued Fraction Computations (`generalized_continued_fraction.of`)

## Summary

This file contains useful approximations for the values involved in the continued fractions
computation `generalized_continued_fraction.of`. In particular, we derive the so-called
*determinant formula* for `generalized_continued_fraction.of`:
`Aₙ * Bₙ₊₁ - Bₙ * Aₙ₊₁ = (-1)^(n + 1)`.

Moreover, we derive some upper bounds for the error term when computing a continued fraction up a
given position, i.e. bounds for the term
`|v - (generalized_continued_fraction.of v).convergents n|`. The derived bounds will show us that
the error term indeed gets smaller. As a corollary, we will be able to show that
`(generalized_continued_fraction.of v).convergents` converges to `v` in
`algebra.continued_fractions.computation.approximation_corollaries`.

## Main Theorems

- `generalized_continued_fraction.of_part_num_eq_one`: shows that all partial numerators `aᵢ` are
  equal to one.
- `generalized_continued_fraction.exists_int_eq_of_part_denom`: shows that all partial denominators
  `bᵢ` correspond to an integer.
- `generalized_continued_fraction.one_le_of_nth_part_denom`: shows that `1 ≤ bᵢ`.
- `generalized_continued_fraction.succ_nth_fib_le_of_nth_denom`: shows that the `n`th denominator
  `Bₙ` is greater than or equal to the `n + 1`th fibonacci number `nat.fib (n + 1)`.
- `generalized_continued_fraction.le_of_succ_nth_denom`: shows that `bₙ * Bₙ ≤ Bₙ₊₁`, where `bₙ` is
  the `n`th partial denominator of the continued fraction.
- `generalized_continued_fraction.abs_sub_convergents_le`: shows that
  `|v - Aₙ / Bₙ| ≤ 1 / (Bₙ * Bₙ₊₁)`, where `Aₙ` is the nth partial numerator.

## References

- [*Hardy, GH and Wright, EM and Heath-Brown, Roger and Silverman, Joseph*][hardy2008introduction]
- https://en.wikipedia.org/wiki/Generalized_continued_fraction#The_determinant_formula

-/


namespace GeneralizedContinuedFraction

open generalized_continued_fraction(of)

open Int

variable {K : Type _} {v : K} {n : ℕ} [LinearOrderedField K] [FloorRing K]

namespace IntFractPair

/-!
We begin with some lemmas about the stream of `int_fract_pair`s, which presumably are not
of great interest for the end user.
-/


/-- Shows that the fractional parts of the stream are in `[0,1)`. -/
theorem nth_stream_fr_nonneg_lt_one {ifp_n : int_fract_pair K}
  (nth_stream_eq : int_fract_pair.stream v n = some ifp_n) : 0 ≤ ifp_n.fr ∧ ifp_n.fr < 1 :=
  by 
    cases n 
    case nat.zero => 
      have  : int_fract_pair.of v = ifp_n
      ·
        injection nth_stream_eq 
      rw [←this, int_fract_pair.of]
      exact ⟨fract_nonneg _, fract_lt_one _⟩
    case nat.succ => 
      rcases succ_nth_stream_eq_some_iff.elim_left nth_stream_eq with ⟨_, _, _, ifp_of_eq_ifp_n⟩
      rw [←ifp_of_eq_ifp_n, int_fract_pair.of]
      exact ⟨fract_nonneg _, fract_lt_one _⟩

/-- Shows that the fractional parts of the stream are nonnegative. -/
theorem nth_stream_fr_nonneg {ifp_n : int_fract_pair K} (nth_stream_eq : int_fract_pair.stream v n = some ifp_n) :
  0 ≤ ifp_n.fr :=
  (nth_stream_fr_nonneg_lt_one nth_stream_eq).left

/-- Shows that the fractional parts of the stream are smaller than one. -/
theorem nth_stream_fr_lt_one {ifp_n : int_fract_pair K} (nth_stream_eq : int_fract_pair.stream v n = some ifp_n) :
  ifp_n.fr < 1 :=
  (nth_stream_fr_nonneg_lt_one nth_stream_eq).right

/-- Shows that the integer parts of the stream are at least one. -/
theorem one_le_succ_nth_stream_b {ifp_succ_n : int_fract_pair K}
  (succ_nth_stream_eq : int_fract_pair.stream v (n+1) = some ifp_succ_n) : 1 ≤ ifp_succ_n.b :=
  by 
    obtain ⟨ifp_n, nth_stream_eq, stream_nth_fr_ne_zero, ⟨-⟩⟩ :
      ∃ ifp_n, int_fract_pair.stream v n = some ifp_n ∧ ifp_n.fr ≠ 0 ∧ int_fract_pair.of (ifp_n.fr⁻¹) = ifp_succ_n 
    exact succ_nth_stream_eq_some_iff.elim_left succ_nth_stream_eq 
    suffices  : 1 ≤ ifp_n.fr⁻¹
    ·
      rwModCast [le_floor]
      assumption 
    suffices  : ifp_n.fr ≤ 1
    ·
      have h : 0 < ifp_n.fr 
      exact lt_of_le_of_neₓ (nth_stream_fr_nonneg nth_stream_eq) stream_nth_fr_ne_zero.symm 
      apply one_le_inv h this 
    simp only [le_of_ltₓ (nth_stream_fr_lt_one nth_stream_eq)]

/--
Shows that the `n + 1`th integer part `bₙ₊₁` of the stream is smaller or equal than the inverse of
the `n`th fractional part `frₙ` of the stream.
This result is straight-forward as `bₙ₊₁` is defined as the floor of `1 / frₙ`
-/
theorem succ_nth_stream_b_le_nth_stream_fr_inv {ifp_n ifp_succ_n : int_fract_pair K}
  (nth_stream_eq : int_fract_pair.stream v n = some ifp_n)
  (succ_nth_stream_eq : int_fract_pair.stream v (n+1) = some ifp_succ_n) : (ifp_succ_n.b : K) ≤ ifp_n.fr⁻¹ :=
  by 
    suffices  : (⌊ifp_n.fr⁻¹⌋ : K) ≤ ifp_n.fr⁻¹
    ·
      cases' ifp_n with _ ifp_n_fr 
      have  : ifp_n_fr ≠ 0
      ·
        intro h 
        simpa [h, int_fract_pair.stream, nth_stream_eq] using succ_nth_stream_eq 
      have  : int_fract_pair.of (ifp_n_fr⁻¹) = ifp_succ_n
      ·
        simpa [this, int_fract_pair.stream, nth_stream_eq, Option.coe_def] using succ_nth_stream_eq 
      rwa [←this]
    exact floor_le (ifp_n.fr⁻¹)

end IntFractPair

/-!
Next we translate above results about the stream of `int_fract_pair`s to the computed continued
fraction `generalized_continued_fraction.of`.
-/


/-- Shows that the integer parts of the continued fraction are at least one. -/
theorem of_one_le_nth_part_denom {b : K} (nth_part_denom_eq : (of v).partialDenominators.nth n = some b) : 1 ≤ b :=
  by 
    obtain ⟨gp_n, nth_s_eq, ⟨-⟩⟩ : ∃ gp_n, (of v).s.nth n = some gp_n ∧ gp_n.b = b 
    exact exists_s_b_of_part_denom nth_part_denom_eq 
    obtain ⟨ifp_n, succ_nth_stream_eq, ifp_n_b_eq_gp_n_b⟩ :
      ∃ ifp, int_fract_pair.stream v (n+1) = some ifp ∧ (ifp.b : K) = gp_n.b 
    exact int_fract_pair.exists_succ_nth_stream_of_gcf_of_nth_eq_some nth_s_eq 
    rw [←ifp_n_b_eq_gp_n_b]
    exactModCast int_fract_pair.one_le_succ_nth_stream_b succ_nth_stream_eq

/--
Shows that the partial numerators `aᵢ` of the continued fraction are equal to one and the partial
denominators `bᵢ` correspond to integers.
-/
theorem of_part_num_eq_one_and_exists_int_part_denom_eq {gp : GeneralizedContinuedFraction.Pair K}
  (nth_s_eq : (of v).s.nth n = some gp) : gp.a = 1 ∧ ∃ z : ℤ, gp.b = (z : K) :=
  by 
    obtain ⟨ifp, stream_succ_nth_eq, -⟩ : ∃ ifp, int_fract_pair.stream v (n+1) = some ifp ∧ _ 
    exact int_fract_pair.exists_succ_nth_stream_of_gcf_of_nth_eq_some nth_s_eq 
    have  : gp = ⟨1, ifp.b⟩
    ·
      ·
        have  : (of v).s.nth n = some ⟨1, ifp.b⟩
        exact nth_of_eq_some_of_succ_nth_int_fract_pair_stream stream_succ_nth_eq 
        have  : some gp = some ⟨1, ifp.b⟩
        ·
          rwa [nth_s_eq] at this 
        injection this 
    finish

/-- Shows that the partial numerators `aᵢ` are equal to one. -/
theorem of_part_num_eq_one {a : K} (nth_part_num_eq : (of v).partialNumerators.nth n = some a) : a = 1 :=
  by 
    obtain ⟨gp, nth_s_eq, gp_a_eq_a_n⟩ : ∃ gp, (of v).s.nth n = some gp ∧ gp.a = a 
    exact exists_s_a_of_part_num nth_part_num_eq 
    have  : gp.a = 1 
    exact (of_part_num_eq_one_and_exists_int_part_denom_eq nth_s_eq).left 
    rwa [gp_a_eq_a_n] at this

/-- Shows that the partial denominators `bᵢ` correspond to an integer. -/
theorem exists_int_eq_of_part_denom {b : K} (nth_part_denom_eq : (of v).partialDenominators.nth n = some b) :
  ∃ z : ℤ, b = (z : K) :=
  by 
    obtain ⟨gp, nth_s_eq, gp_b_eq_b_n⟩ : ∃ gp, (of v).s.nth n = some gp ∧ gp.b = b 
    exact exists_s_b_of_part_denom nth_part_denom_eq 
    have  : ∃ z : ℤ, gp.b = (z : K)
    exact (of_part_num_eq_one_and_exists_int_part_denom_eq nth_s_eq).right 
    rwa [gp_b_eq_b_n] at this

/-!
One of our next goals is to show that `bₙ * Bₙ ≤ Bₙ₊₁`. For this, we first show that the partial
denominators `Bₙ` are bounded from below by the fibonacci sequence `nat.fib`. This then implies that
`0 ≤ Bₙ` and hence `Bₙ₊₂ = bₙ₊₁ * Bₙ₊₁ + Bₙ ≥ bₙ₊₁ * Bₙ₊₁ + 0 = bₙ₊₁ * Bₙ₊₁`.
-/


open Nat

-- failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Meta.solveByElim'
-- failed to format: no declaration of attribute [formatter] found for 'Lean.Meta.solveByElim'
theorem
  fib_le_of_continuants_aux_b
  : n ≤ 1 ∨ ¬ of v . TerminatedAt n - 2 → ( fib n : K ) ≤ of v . continuantsAux n . b
  :=
    Nat.strong_induction_onₓ
      n
        by
          clear n
            intro n IH hyp
            rcases n with ( _ | _ | n )
            · simp [ fib_add_two , continuants_aux ]
            · simp [ fib_add_two , continuants_aux ]
            ·
              let g := of v
                have : ¬ n + 2 ≤ 1
                · linarith
                have not_terminated_at_n : ¬ g.terminated_at n
                exact Or.resolve_left hyp this
                obtain ⟨ gp , s_ppred_nth_eq ⟩ : ∃ gp , g.s.nth n = some gp
                exact option.ne_none_iff_exists'.mp not_terminated_at_n
                set pconts := g.continuants_aux n + 1 with pconts_eq
                set ppconts := g.continuants_aux n with ppconts_eq
                suffices : ( fib n : K ) + fib n + 1 ≤ gp.a * ppconts.b + gp.b * pconts.b
                · simpa [ fib_add_two , add_commₓ , continuants_aux_recurrence s_ppred_nth_eq ppconts_eq pconts_eq ]
                suffices : ( fib n : K ) + fib n + 1 ≤ ppconts.b + gp.b * pconts.b
                · simpa [ of_part_num_eq_one $ part_num_eq_s_a s_ppred_nth_eq ]
                have not_terminated_at_pred_n : ¬ g.terminated_at n - 1
                exact mt terminated_stable $ Nat.sub_leₓ n 1 not_terminated_at_n
                have not_terminated_at_ppred_n : ¬ terminated_at g n - 2
                exact mt terminated_stable n - 1 . pred_le not_terminated_at_pred_n
                have : ( fib n + 1 : K ) ≤ pconts.b
                exact IH _ Nat.Lt.base $ n + 1 Or.inr not_terminated_at_pred_n
                have ppred_nth_fib_le_ppconts_B : ( fib n : K ) ≤ ppconts.b
                exact IH n lt_transₓ Nat.Lt.base n $ Nat.Lt.base $ n + 1 Or.inr not_terminated_at_ppred_n
                suffices : ( fib n + 1 : K ) ≤ gp.b * pconts.b
                solveByElim [ add_le_add ppred_nth_fib_le_ppconts_B ]
                suffices : 1 * ( fib n + 1 : K ) ≤ gp.b * pconts.b
                · rwa [ one_mulₓ ] at this
                have one_le_gp_b : ( 1 : K ) ≤ gp.b
                exact of_one_le_nth_part_denom part_denom_eq_s_b s_ppred_nth_eq
                have : ( 0 : K ) ≤ fib n + 1
                · exactModCast fib n + 1 . zero_le
                have : ( 0 : K ) ≤ gp.b
                exact le_transₓ zero_le_one one_le_gp_b
                mono

/-- Shows that the `n`th denominator is greater than or equal to the `n + 1`th fibonacci number,
that is `nat.fib (n + 1) ≤ Bₙ`. -/
theorem succ_nth_fib_le_of_nth_denom (hyp : n = 0 ∨ ¬(of v).TerminatedAt (n - 1)) :
  (fib (n+1) : K) ≤ (of v).denominators n :=
  by 
    rw [denom_eq_conts_b, nth_cont_eq_succ_nth_cont_aux]
    have  : (n+1) ≤ 1 ∨ ¬(of v).TerminatedAt (n - 1)
    ·
      ·
        cases n 
        case nat.zero => 
          exact Or.inl$ le_reflₓ 1
        case nat.succ => 
          exact Or.inr (Or.resolve_left hyp n.succ_ne_zero)
    exact fib_le_of_continuants_aux_b this

/-! As a simple consequence, we can now derive that all denominators are nonnegative. -/


theorem zero_le_of_continuants_aux_b : 0 ≤ ((of v).continuantsAux n).b :=
  by 
    let g := of v 
    induction' n with n IH 
    case nat.zero => 
      rfl 
    case nat.succ => 
      cases' Decidable.em$ g.terminated_at (n - 1) with terminated not_terminated
      ·
        cases n
        ·
          simp [zero_le_one]
        ·
          have  : g.continuants_aux (n+2) = g.continuants_aux (n+1)
          exact continuants_aux_stable_step_of_terminated terminated 
          simp only [this, IH]
      ·
        calc (0 : K) ≤ fib (n+1) :=
          by 
            exactModCast (n+1).fib.zero_le _ ≤ ((of v).continuantsAux (n+1)).b :=
          fib_le_of_continuants_aux_b (Or.inr not_terminated)

/-- Shows that all denominators are nonnegative. -/
theorem zero_le_of_denom : 0 ≤ (of v).denominators n :=
  by 
    rw [denom_eq_conts_b, nth_cont_eq_succ_nth_cont_aux]
    exact zero_le_of_continuants_aux_b

-- failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Meta.solveByElim'
-- failed to format: no declaration of attribute [formatter] found for 'Lean.Meta.solveByElim'
theorem
  le_of_succ_succ_nth_continuants_aux_b
  { b : K } ( nth_part_denom_eq : of v . partialDenominators . nth n = some b )
    : b * of v . continuantsAux $ n + 1 . b ≤ of v . continuantsAux $ n + 2 . b
  :=
    by
      set g := of v with g_eq
        obtain ⟨ gp_n , nth_s_eq , gpnb_eq_b ⟩ : ∃ gp_n , g.s.nth n = some gp_n ∧ gp_n.b = b
        exact exists_s_b_of_part_denom nth_part_denom_eq
        let conts := g.continuants_aux n + 2
        set pconts := g.continuants_aux n + 1 with pconts_eq
        set ppconts := g.continuants_aux n with ppconts_eq
        suffices : gp_n.b * pconts.b ≤ ppconts.b + gp_n.b * pconts.b
        ·
          ·
            have : gp_n.a = 1
              exact of_part_num_eq_one part_num_eq_s_a nth_s_eq
              finish [ GeneralizedContinuedFraction.continuants_aux_recurrence nth_s_eq ppconts_eq pconts_eq ]
        have : 0 ≤ ppconts.b
        exact zero_le_of_continuants_aux_b
        solveByElim [ le_add_of_nonneg_of_le , le_reflₓ ]

/-- Shows that `bₙ * Bₙ ≤ Bₙ₊₁`, where `bₙ` is the `n`th partial denominator and `Bₙ₊₁` and `Bₙ` are
the `n + 1`th and `n`th denominator of the continued fraction. -/
theorem le_of_succ_nth_denom {b : K} (nth_part_denom_eq : (of v).partialDenominators.nth n = some b) :
  (b*(of v).denominators n) ≤ (of v).denominators (n+1) :=
  by 
    rw [denom_eq_conts_b, nth_cont_eq_succ_nth_cont_aux]
    exact le_of_succ_succ_nth_continuants_aux_b nth_part_denom_eq

/-- Shows that the sequence of denominators is monotone, that is `Bₙ ≤ Bₙ₊₁`. -/
theorem of_denom_mono : (of v).denominators n ≤ (of v).denominators (n+1) :=
  by 
    let g := of v 
    cases' Decidable.em$ g.partial_denominators.terminated_at n with terminated not_terminated
    ·
      have  : g.partial_denominators.nth n = none
      ·
        rwa [Seqₓₓ.TerminatedAt] at terminated 
      have  : g.terminated_at n 
      exact
        terminated_at_iff_part_denom_none.elim_right
          (by 
            rwa [Seqₓₓ.TerminatedAt] at terminated)
      have  : g.denominators (n+1) = g.denominators n 
      exact denominators_stable_of_terminated n.le_succ this 
      rw [this]
    ·
      obtain ⟨b, nth_part_denom_eq⟩ : ∃ b, g.partial_denominators.nth n = some b 
      exact option.ne_none_iff_exists'.mp not_terminated 
      have  : 1 ≤ b 
      exact of_one_le_nth_part_denom nth_part_denom_eq 
      calc g.denominators n ≤ b*g.denominators n :=
        by 
          simpa using mul_le_mul_of_nonneg_right this zero_le_of_denom _ ≤ g.denominators (n+1) :=
        le_of_succ_nth_denom nth_part_denom_eq

section Determinant

/-!
### Determinant Formula

Next we prove the so-called *determinant formula* for `generalized_continued_fraction.of`:
`Aₙ * Bₙ₊₁ - Bₙ * Aₙ₊₁ = (-1)^(n + 1)`.
-/


theorem determinant_aux (hyp : n = 0 ∨ ¬(of v).TerminatedAt (n - 1)) :
  ((((of v).continuantsAux n).a*((of v).continuantsAux (n+1)).b) -
      ((of v).continuantsAux n).b*((of v).continuantsAux (n+1)).a) =
    -1 ^ n :=
  by 
    induction' n with n IH 
    case nat.zero => 
      simp [continuants_aux]
    case nat.succ => 
      let g := of v 
      let conts := continuants_aux g (n+2)
      set pred_conts := continuants_aux g (n+1) with pred_conts_eq 
      set ppred_conts := continuants_aux g n with ppred_conts_eq 
      let pA := pred_conts.a 
      let pB := pred_conts.b 
      let ppA := ppred_conts.a 
      let ppB := ppred_conts.b 
      change ((pA*conts.b) - pB*conts.a) = -1 ^ n+1
      have not_terminated_at_n : ¬terminated_at g n 
      exact Or.resolve_left hyp n.succ_ne_zero 
      obtain ⟨gp, s_nth_eq⟩ : ∃ gp, g.s.nth n = some gp 
      exact option.ne_none_iff_exists'.elim_left not_terminated_at_n 
      suffices  : ((pA*ppB+gp.b*pB) - pB*ppA+gp.b*pA) = -1 ^ n+1
      ·
        ·
          simp only [conts, continuants_aux_recurrence s_nth_eq ppred_conts_eq pred_conts_eq]
          have gp_a_eq_one : gp.a = 1 
          exact of_part_num_eq_one (part_num_eq_s_a s_nth_eq)
          rw [gp_a_eq_one, this.symm]
          ring 
      suffices  : ((pA*ppB) - pB*ppA) = -1 ^ n+1
      calc ((pA*ppB+gp.b*pB) - pB*ppA+gp.b*pA) = (((pA*ppB)+(pA*gp.b)*pB) - pB*ppA) - (pB*gp.b)*pA :=
        by 
          ring _ = (pA*ppB) - pB*ppA :=
        by 
          ring _ = -1 ^ n+1 :=
        by 
          assumption 
      suffices  : ((ppA*pB) - ppB*pA) = -1 ^ n
      ·
        ·
          have pow_succ_n : ((-1 : K) ^ n+1) = (-1)*-1 ^ n 
          exact pow_succₓ (-1) n 
          rw [pow_succ_n, ←this]
          ring 
      exact IH$ Or.inr$ mt (terminated_stable$ n.sub_le 1) not_terminated_at_n

/-- The determinant formula `Aₙ * Bₙ₊₁ - Bₙ * Aₙ₊₁ = (-1)^(n + 1)` -/
theorem determinant (not_terminated_at_n : ¬(of v).TerminatedAt n) :
  (((of v).numerators n*(of v).denominators (n+1)) - (of v).denominators n*(of v).numerators (n+1)) = -1 ^ n+1 :=
  determinant_aux$ Or.inr$ not_terminated_at_n

end Determinant

section ErrorTerm

/-!
### Approximation of Error Term

Next we derive some approximations for the error term when computing a continued fraction up a given
position, i.e. bounds for the term `|v - (generalized_continued_fraction.of v).convergents n|`.
-/


/-- This lemma follows from the finite correctness proof, the determinant equality, and
by simplifying the difference. -/
theorem sub_convergents_eq {ifp : int_fract_pair K} (stream_nth_eq : int_fract_pair.stream v n = some ifp) :
  let g := of v 
  let B := (g.continuants_aux (n+1)).b 
  let pB := (g.continuants_aux n).b 
  v - g.convergents n = if ifp.fr = 0 then 0 else -1 ^ n / B*(ifp.fr⁻¹*B)+pB :=
  by 
    let g := of v 
    let conts := g.continuants_aux (n+1)
    let pred_conts := g.continuants_aux n 
    have g_finite_correctness : v = GeneralizedContinuedFraction.compExactValue pred_conts conts ifp.fr 
    exact comp_exact_value_correctness_of_stream_eq_some stream_nth_eq 
    cases' Decidable.em (ifp.fr = 0) with ifp_fr_eq_zero ifp_fr_ne_zero
    ·
      suffices  : v - g.convergents n = 0
      ·
        simpa [ifp_fr_eq_zero]
      replace g_finite_correctness : v = g.convergents n
      ·
        simpa [GeneralizedContinuedFraction.compExactValue, ifp_fr_eq_zero] using g_finite_correctness 
      exact sub_eq_zero.elim_right g_finite_correctness
    ·
      let A := conts.a 
      let B := conts.b 
      let pA := pred_conts.a 
      let pB := pred_conts.b 
      suffices  : v - A / B = -1 ^ n / B*(ifp.fr⁻¹*B)+pB
      ·
        simpa [ifp_fr_ne_zero]
      replace g_finite_correctness : v = (pA+ifp.fr⁻¹*A) / pB+ifp.fr⁻¹*B
      ·
        simpa [GeneralizedContinuedFraction.compExactValue, ifp_fr_ne_zero, next_continuants, next_numerator,
          next_denominator, add_commₓ] using g_finite_correctness 
      suffices  : ((pA+ifp.fr⁻¹*A) / pB+ifp.fr⁻¹*B) - A / B = -1 ^ n / B*(ifp.fr⁻¹*B)+pB
      ·
        rwa [g_finite_correctness]
      have n_eq_zero_or_not_terminated_at_pred_n : n = 0 ∨ ¬g.terminated_at (n - 1)
      ·
        ·
          cases' n with n'
          ·
            simp 
          ·
            have  : int_fract_pair.stream v (n'+1) ≠ none
            ·
              simp [stream_nth_eq]
            have  : ¬g.terminated_at n' 
            exact (not_iff_not_of_iff of_terminated_at_n_iff_succ_nth_int_fract_pair_stream_eq_none).elim_right this 
            exact Or.inr this 
      have determinant_eq : ((pA*B) - pB*A) = -1 ^ n 
      exact determinant_aux n_eq_zero_or_not_terminated_at_pred_n 
      have pB_ineq : (fib n : K) ≤ pB
      ·
        ·
          have  : n ≤ 1 ∨ ¬g.terminated_at (n - 2)
          ·
            ·
              cases' n_eq_zero_or_not_terminated_at_pred_n with n_eq_zero not_terminated_at_pred_n
              ·
                simp [n_eq_zero]
              ·
                exact Or.inr$ mt (terminated_stable (n - 1).pred_le) not_terminated_at_pred_n 
          exact fib_le_of_continuants_aux_b this 
      have B_ineq : (fib (n+1) : K) ≤ B
      ·
        ·
          have  : (n+1) ≤ 1 ∨ ¬g.terminated_at ((n+1) - 2)
          ·
            ·
              cases' n_eq_zero_or_not_terminated_at_pred_n with n_eq_zero not_terminated_at_pred_n
              ·
                simp [n_eq_zero, le_reflₓ]
              ·
                exact Or.inr not_terminated_at_pred_n 
          exact fib_le_of_continuants_aux_b this 
      have zero_lt_B : 0 < B
      ·
        have  : 1 ≤ B 
        exact
          le_transₓ
            (by 
              exactModCast fib_pos (lt_of_le_of_neₓ n.succ.zero_le n.succ_ne_zero.symm))
            B_ineq 
        exact lt_of_lt_of_leₓ zero_lt_one this 
      have zero_ne_B : 0 ≠ B 
      exact ne_of_ltₓ zero_lt_B 
      have  : 0 ≠ pB+ifp.fr⁻¹*B
      ·
        ·
          have  : (0 : K) ≤ fib n
          ·
            exactModCast (fib n).zero_le 
          have zero_le_pB : 0 ≤ pB 
          exact le_transₓ this pB_ineq 
          have  : 0 < ifp.fr⁻¹
          ·
            ·
              suffices  : 0 < ifp.fr
              ·
                rwa [inv_pos]
              have  : 0 ≤ ifp.fr 
              exact int_fract_pair.nth_stream_fr_nonneg stream_nth_eq 
              change ifp.fr ≠ 0 at ifp_fr_ne_zero 
              exact lt_of_le_of_neₓ this ifp_fr_ne_zero.symm 
          have  : 0 < ifp.fr⁻¹*B 
          exact mul_pos this zero_lt_B 
          have  : 0 < pB+ifp.fr⁻¹*B 
          exact add_pos_of_nonneg_of_pos zero_le_pB this 
          exact ne_of_ltₓ this 
      calc ((pA+ifp.fr⁻¹*A) / pB+ifp.fr⁻¹*B) - A / B = (((pA+ifp.fr⁻¹*A)*B) - (pB+ifp.fr⁻¹*B)*A) / (pB+ifp.fr⁻¹*B)*B :=
        by 
          rw [div_sub_div _ _ this.symm zero_ne_B.symm]_ = (((pA*B)+(ifp.fr⁻¹*A)*B) - (pB*A)+(ifp.fr⁻¹*B)*A) / _ :=
        by 
          repeat' 
            rw [add_mulₓ]_ = ((pA*B) - pB*A) / (pB+ifp.fr⁻¹*B)*B :=
        by 
          ring _ = -1 ^ n / (pB+ifp.fr⁻¹*B)*B :=
        by 
          rw [determinant_eq]_ = -1 ^ n / B*(ifp.fr⁻¹*B)+pB :=
        by 
          acRfl

-- failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Meta.solveByElim'
-- failed to format: no declaration of attribute [formatter] found for 'Lean.Meta.solveByElim'
/-- Shows that `|v - Aₙ / Bₙ| ≤ 1 / (Bₙ * Bₙ₊₁)` -/
  theorem
    abs_sub_convergents_le
    ( not_terminated_at_n : ¬ of v . TerminatedAt n )
      : | v - of v . convergents n | ≤ 1 / of v . denominators n * of v . denominators $ n + 1
    :=
      by
        let g := of v
          let nextConts := g.continuants_aux n + 2
          set conts := continuants_aux g n + 1 with conts_eq
          set pred_conts := continuants_aux g n with pred_conts_eq
          change | v - convergents g n | ≤ 1 / conts.b * nextConts.b
          obtain ⟨ gp , s_nth_eq ⟩ : ∃ gp , g.s.nth n = some gp
          exact option.ne_none_iff_exists'.elim_left not_terminated_at_n
          have gp_a_eq_one : gp.a = 1
          exact of_part_num_eq_one part_num_eq_s_a s_nth_eq
          have nextConts_b_eq : nextConts.b = pred_conts.b + gp.b * conts.b
          ·
            simp
              [
                nextConts
                  ,
                  continuants_aux_recurrence s_nth_eq pred_conts_eq conts_eq
                  ,
                  gp_a_eq_one
                  ,
                  pred_conts_eq.symm
                  ,
                  conts_eq.symm
                  ,
                  add_commₓ
                ]
          let denom := conts.b * pred_conts.b + gp.b * conts.b
          suffices : | v - g.convergents n | ≤ 1 / denom
          · · rw [ nextConts_b_eq ] congr 1
          obtain
            ⟨ ifp_succ_n , succ_nth_stream_eq , ifp_succ_n_b_eq_gp_b ⟩
            : ∃ ifp_succ_n , int_fract_pair.stream v n + 1 = some ifp_succ_n ∧ ( ifp_succ_n.b : K ) = gp.b
          exact int_fract_pair.exists_succ_nth_stream_of_gcf_of_nth_eq_some s_nth_eq
          obtain
            ⟨ ifp_n , stream_nth_eq , stream_nth_fr_ne_zero , if_of_eq_ifp_succ_n ⟩
            :
              ∃
                ifp_n
                ,
                int_fract_pair.stream v n = some ifp_n ∧ ifp_n.fr ≠ 0 ∧ int_fract_pair.of ifp_n.fr ⁻¹ = ifp_succ_n
          exact int_fract_pair.succ_nth_stream_eq_some_iff.elim_left succ_nth_stream_eq
          let denom' := conts.b * pred_conts.b + ifp_n.fr ⁻¹ * conts.b
          suffices : | - 1 ^ n / denom' | ≤ 1 / denom
          ·
            ·
              have : v - g.convergents n = - 1 ^ n / denom'
                ·
                  ·
                    have tmp
                      exact sub_convergents_eq stream_nth_eq
                      delta' at tmp
                      simp only [ stream_nth_fr_ne_zero , conts_eq.symm , pred_conts_eq.symm ] at tmp
                      rw [ tmp ]
                      simp only [ denom' ]
                      ringNF
                      acRfl
                rwa [ this ]
          have nextConts_b_ineq : ( fib n + 2 : K ) ≤ pred_conts.b + gp.b * conts.b
          ·
            ·
              have : ( fib n + 2 : K ) ≤ nextConts.b
                exact fib_le_of_continuants_aux_b Or.inr not_terminated_at_n
                rwa [ nextConts_b_eq ] at this
          have conts_b_ineq : ( fib n + 1 : K ) ≤ conts.b
          ·
            ·
              have : ¬ g.terminated_at n - 1
                exact mt terminated_stable n.pred_le not_terminated_at_n
                exact fib_le_of_continuants_aux_b $ Or.inr this
          have zero_lt_conts_b : 0 < conts.b
          ·
            ·
              have : ( 0 : K ) < fib n + 1
                · exactModCast fib_pos lt_of_le_of_neₓ n.succ.zero_le n.succ_ne_zero.symm
                exact lt_of_lt_of_leₓ this conts_b_ineq
          suffices : 1 / denom' ≤ 1 / denom
          ·
            ·
              have : | - 1 ^ n / denom' | = 1 / denom'
                ·
                  ·
                    suffices : 1 / | denom' | = 1 / denom'
                      · rwa [ abs_div , abs_neg_one_pow n ]
                      have : 0 < denom'
                      ·
                        ·
                          have : 0 ≤ pred_conts.b
                            ·
                              ·
                                have : ( fib n : K ) ≤ pred_conts.b
                                  ·
                                    ·
                                      have : ¬ g.terminated_at n - 2
                                        exact mt terminated_stable n.sub_le 2 not_terminated_at_n
                                        exact fib_le_of_continuants_aux_b $ Or.inr this
                                  exact le_transₓ by exactModCast fib n . zero_le this
                            have : 0 < ifp_n.fr ⁻¹
                            ·
                              ·
                                have zero_le_ifp_n_fract : 0 ≤ ifp_n.fr
                                  exact int_fract_pair.nth_stream_fr_nonneg stream_nth_eq
                                  exact
                                    inv_pos.elim_right lt_of_le_of_neₓ zero_le_ifp_n_fract stream_nth_fr_ne_zero.symm
                            any_goals repeat' first | apply mul_pos | apply add_pos_of_nonneg_of_pos <;> assumption
                      rwa [ abs_of_pos this ]
                rwa [ this ]
          suffices : 0 < denom ∧ denom ≤ denom'
          exact div_le_div_of_le_left zero_le_one this.left this.right
          constructor
          ·
            have : 0 < pred_conts.b + gp.b * conts.b
              exact
                lt_of_lt_of_leₓ
                  by exactModCast fib_pos lt_of_le_of_neₓ n.succ.succ.zero_le n.succ.succ_ne_zero.symm nextConts_b_ineq
              solveByElim [ mul_pos ]
          ·
            suffices : gp.b * conts.b ≤ ifp_n.fr ⁻¹ * conts.b
              exact mul_le_mul_left zero_lt_conts_b . elim_right $ add_le_add_iff_left pred_conts.b . elim_right this
              suffices : ( ifp_succ_n.b : K ) * conts.b ≤ ifp_n.fr ⁻¹ * conts.b
              · rwa [ ← ifp_succ_n_b_eq_gp_b ]
              have : ( ifp_succ_n.b : K ) ≤ ifp_n.fr ⁻¹
              exact int_fract_pair.succ_nth_stream_b_le_nth_stream_fr_inv stream_nth_eq succ_nth_stream_eq
              have : 0 ≤ conts.b
              exact le_of_ltₓ zero_lt_conts_b
              mono

/--
Shows that `|v - Aₙ / Bₙ| ≤ 1 / (bₙ * Bₙ * Bₙ)`. This bound is worse than the one shown in
`gcf.abs_sub_convergents_le`, but sometimes it is easier to apply and sufficient for one's use case.
 -/
theorem abs_sub_convergents_le' {b : K} (nth_part_denom_eq : (of v).partialDenominators.nth n = some b) :
  |v - (of v).convergents n| ≤ 1 / (b*(of v).denominators n)*(of v).denominators n :=
  by 
    let g := of v 
    let B := g.denominators n 
    let nB := g.denominators (n+1)
    have not_terminated_at_n : ¬g.terminated_at n
    ·
      ·
        have  : g.partial_denominators.nth n ≠ none
        ·
          simp [nth_part_denom_eq]
        exact (not_iff_not_of_iff terminated_at_iff_part_denom_none).elim_right this 
    suffices  : (1 / B*nB) ≤ (1 : K) / (b*B)*B
    ·
      ·
        have  : |v - g.convergents n| ≤ 1 / B*nB 
        exact abs_sub_convergents_le not_terminated_at_n 
        trans <;> assumption 
    have zero_lt_B : 0 < B
    ·
      ·
        have  : (fib (n+1) : K) ≤ B 
        exact succ_nth_fib_le_of_nth_denom (Or.inr$ mt (terminated_stable n.pred_le) not_terminated_at_n)
        exact
          lt_of_lt_of_leₓ
            (by 
              exactModCast fib_pos (lt_of_le_of_neₓ n.succ.zero_le n.succ_ne_zero.symm))
            this 
    have denoms_ineq : ((b*B)*B) ≤ B*nB
    ·
      ·
        have  : (b*B) ≤ nB 
        exact le_of_succ_nth_denom nth_part_denom_eq 
        rwa [mul_commₓ B nB, mul_le_mul_right zero_lt_B]
    have  : (0 : K) < (b*B)*B
    ·
      ·
        have  : 0 < b 
        exact lt_of_lt_of_leₓ zero_lt_one (of_one_le_nth_part_denom nth_part_denom_eq)
        any_goals 
            repeat' 
              apply mul_pos <;>
          assumption 
    exact div_le_div_of_le_left zero_le_one this denoms_ineq

end ErrorTerm

end GeneralizedContinuedFraction

