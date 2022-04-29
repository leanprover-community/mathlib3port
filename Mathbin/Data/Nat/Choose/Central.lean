/-
Copyright (c) 2021 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens, Thomas Browning
-/
import Mathbin.Data.Nat.Prime
import Mathbin.Data.Nat.Choose.Basic
import Mathbin.Data.Nat.Choose.Sum
import Mathbin.Data.Nat.Multiplicity
import Mathbin.NumberTheory.Padics.PadicNorm
import Mathbin.Tactic.NormNum
import Mathbin.Tactic.Linarith.Default

/-!
# Central binomial coefficients

This file proves properties of the central binomial coefficients (that is, `nat.choose (2 * n) n`).

## Main definition and results

* `nat.central_binom`: the central binomial coefficient, `(2 * n).choose n`.
* `nat.succ_mul_central_binom_succ`: the inductive relationship between successive central binomial
  coefficients.
* `nat.four_pow_lt_mul_central_binom`: an exponential lower bound on the central binomial
  coefficient.
* `nat.multiplicity_central_binom_le`: a logarithmic upper bound on the multiplicity of a prime in
  the central binomial coefficient.
* `nat.multiplicity_central_binom_of_large_le_one`: sufficiently large primes appear at most once
  in the factorisation of the central binomial coefficient.
* `nat.multiplicity_central_binom_of_large_eq_zero`: sufficiently large primes less than n do not
  appear in the factorisation of the central binomial coefficient.
-/


namespace Nat

/-- The central binomial coefficient, `nat.choose (2 * n) n`.
-/
def centralBinom (n : ℕ) :=
  (2 * n).choose n

theorem central_binom_eq_two_mul_choose (n : ℕ) : centralBinom n = (2 * n).choose n :=
  rfl

theorem central_binom_pos (n : ℕ) : 0 < centralBinom n :=
  choose_pos (Nat.le_mul_of_pos_left zero_lt_two)

theorem central_binom_ne_zero (n : ℕ) : centralBinom n ≠ 0 :=
  (central_binom_pos n).ne'

@[simp]
theorem central_binom_zero : centralBinom 0 = 1 :=
  choose_zero_right _

/-- The central binomial coefficient is the largest binomial coefficient.
-/
theorem choose_le_central_binom (r n : ℕ) : choose (2 * n) r ≤ centralBinom n :=
  calc
    (2 * n).choose r ≤ (2 * n).choose (2 * n / 2) := choose_le_middle r (2 * n)
    _ = (2 * n).choose n := by
      rw [Nat.mul_div_cancel_leftₓ n zero_lt_two]
    

theorem two_le_central_binom (n : ℕ) (n_pos : 0 < n) : 2 ≤ centralBinom n :=
  calc
    2 ≤ 2 * n := le_mul_of_pos_right n_pos
    _ = (2 * n).choose 1 := (choose_one_right (2 * n)).symm
    _ ≤ centralBinom n := choose_le_central_binom 1 n
    

/-- An inductive property of the central binomial coefficient.
-/
theorem succ_mul_central_binom_succ (n : ℕ) : (n + 1) * centralBinom (n + 1) = 2 * (2 * n + 1) * centralBinom n :=
  calc
    (n + 1) * (2 * (n + 1)).choose (n + 1) = (2 * n + 2).choose (n + 1) * (n + 1) := mul_comm _ _
    _ = (2 * n + 1).choose n * (2 * n + 2) := by
      rw [choose_succ_right_eq, choose_mul_succ_eq]
    _ = 2 * ((2 * n + 1).choose n * (n + 1)) := by
      ring
    _ = 2 * ((2 * n + 1).choose n * (2 * n + 1 - n)) := by
      rw [two_mul n, add_assocₓ, Nat.add_sub_cancel_left]
    _ = 2 * ((2 * n).choose n * (2 * n + 1)) := by
      rw [choose_mul_succ_eq]
    _ = 2 * (2 * n + 1) * (2 * n).choose n := by
      rw [mul_assoc, mul_comm (2 * n + 1)]
    

/-- An exponential lower bound on the central binomial coefficient.
This bound is of interest because it appears in
[Tochiori's refinement of Erdős's proof of Bertrand's postulate](https://en.wikipedia.org/w/index.php?title=Proof_of_Bertrand%27s_postulate&oldid=859165151#Proof_by_Shigenori_Tochiori).
-/
theorem four_pow_lt_mul_central_binom (n : ℕ) (n_big : 4 ≤ n) : 4 ^ n < n * centralBinom n := by
  induction' n using Nat.strong_induction_onₓ with n IH
  rcases lt_trichotomyₓ n 4 with (hn | rfl | hn)
  · clear IH
    decide!
    
  · norm_num [central_binom, choose]
    
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (zero_lt_four.trans hn).ne'
  calc 4 ^ (n + 1) < 4 * (n * central_binom n) :=
      (mul_lt_mul_left zero_lt_four).mpr
        (IH n n.lt_succ_self (Nat.le_of_lt_succₓ hn))_ ≤ 2 * (2 * n + 1) * central_binom n :=
      by
      rw [← mul_assoc]
      linarith _ = (n + 1) * central_binom (n + 1) := (succ_mul_central_binom_succ n).symm

/-- An exponential lower bound on the central binomial coefficient.
This bound is weaker than `four_pow_n_lt_n_mul_central_binom`, but it is of historical interest
because it appears in Erdős's proof of Bertrand's postulate.
-/
theorem four_pow_le_two_mul_self_mul_central_binom : ∀ n : ℕ n_pos : 0 < n, 4 ^ n ≤ 2 * n * centralBinom n
  | 0, pr => (Nat.not_lt_zeroₓ _ pr).elim
  | 1, pr => by
    norm_num [central_binom, choose]
  | 2, pr => by
    norm_num [central_binom, choose]
  | 3, pr => by
    norm_num [central_binom, choose]
  | n@(m + 4), _ =>
    calc
      4 ^ n ≤ n * centralBinom n := (four_pow_lt_mul_central_binom _ le_add_self).le
      _ ≤ 2 * n * centralBinom n := by
        rw [mul_assoc]
        refine' le_mul_of_pos_left zero_lt_two
      

variable {p n : ℕ}

/-- A logarithmic upper bound on the multiplicity of a prime in the central binomial coefficient.
-/
theorem padic_val_nat_central_binom_le (hp : p.Prime) : padicValNat p (centralBinom n) ≤ log p (2 * n) := by
  rw [@padic_val_nat_def _ ⟨hp⟩ _ (central_binom_pos n)]
  unfold central_binom
  have two_n_sub : 2 * n - n = n := by
    rw [two_mul n, Nat.add_sub_cancel n n]
  simp only [Nat.Prime.multiplicity_choose hp (le_mul_of_pos_left zero_lt_two) (lt_add_one _), two_n_sub, ← two_mul,
    Enat.get_coe', Finset.filter_congr_decidable]
  calc _ ≤ (Finset.ico 1 (log p (2 * n) + 1)).card := Finset.card_filter_le _ _ _ = log p (2 * n) + 1 - 1 :=
      Nat.card_Ico _ _

/-- Sufficiently large primes appear only to multiplicity 0 or 1 in the central binomial coefficient.
-/
theorem padic_val_nat_central_binom_of_large_le_one (hp : p.Prime) (p_large : 2 * n < p ^ 2) :
    padicValNat p (centralBinom n) ≤ 1 := by
  have log_weak_bound : log p (2 * n) ≤ 2 := by
    calc log p (2 * n) ≤ log p (p ^ 2) := log_le_log_of_le (le_of_ltₓ p_large)_ = 2 := log_pow hp.one_lt 2
  have log_bound : log p (2 * n) ≤ 1 := by
    cases' le_or_ltₓ (log p (2 * n)) 1 with log_le lt_log
    · exact log_le
      
    · have v : log p (2 * n) = 2 := by
        linarith
      cases' le_or_ltₓ p (2 * n) with h h
      · exfalso
        rw [log_of_one_lt_of_le hp.one_lt h, succ_inj', log_eq_one_iff] at v
        have bad : p ^ 2 ≤ 2 * n := by
          rw [pow_two]
          exact (Nat.le_div_iff_mul_leₓ _ _ (prime.pos hp)).1 v.2.2
        exact lt_irreflₓ _ (lt_of_le_of_ltₓ bad p_large)
        
      · rw [log_eq_zero (Or.inl h)]
        exact zero_le 1
        
      
  exact le_transₓ (padic_val_nat_central_binom_le hp) log_bound

/-- Sufficiently large primes less than `n` do not appear in the factorisation of `central_binom n`.
-/
theorem padic_val_nat_central_binom_of_large_eq_zero (hp : p.Prime) (n_big : 2 < n) (p_le_n : p ≤ n)
    (big : 2 * n < 3 * p) : padicValNat p (centralBinom n) = 0 := by
  rw [@padic_val_nat_def _ ⟨hp⟩ _ (central_binom_pos n)]
  unfold central_binom
  have two_n_sub : 2 * n - n = n := by
    rw [two_mul n, Nat.add_sub_cancel n n]
  simp only [Nat.Prime.multiplicity_choose hp (le_mul_of_pos_left zero_lt_two) (lt_add_one _), two_n_sub, ← two_mul,
    Finset.card_eq_zero, Enat.get_coe', Finset.filter_congr_decidable]
  clear two_n_sub
  have three_lt_p : 3 ≤ p := by
    linarith
  have p_pos : 0 < p := Nat.Prime.pos hp
  apply Finset.filter_false_of_mem
  intro i i_in_interval
  rw [Finset.mem_Ico] at i_in_interval
  refine' not_le.mpr _
  rcases lt_trichotomyₓ 1 i with (H | rfl | H)
  · have two_le_i : 2 ≤ i := Nat.succ_le_of_ltₓ H
    have two_n_lt_pow_p_i : 2 * n < p ^ i := by
      calc 2 * n < 3 * p := big _ ≤ p * p := (mul_le_mul_right p_pos).2 three_lt_p _ = p ^ 2 := (sq _).symm _ ≤ p ^ i :=
          Nat.pow_le_pow_of_le_rightₓ p_pos two_le_i
    have n_mod : n % p ^ i = n := by
      apply Nat.mod_eq_of_ltₓ
      calc n ≤ n + n := Nat.Le.intro rfl _ = 2 * n := (two_mul n).symm _ < p ^ i := two_n_lt_pow_p_i
    rw [n_mod]
    exact two_n_lt_pow_p_i
    
  · rw [pow_oneₓ]
    suffices h23 : 2 * (p * (n / p)) + 2 * (n % p) < 2 * (p * (n / p)) + p
    · exact (add_lt_add_iff_left (2 * (p * (n / p)))).mp h23
      
    have n_big : 1 ≤ n / p := (Nat.le_div_iff_mul_le' p_pos).2 (trans (one_mulₓ _).le p_le_n)
    rw [← mul_addₓ, Nat.div_add_mod]
    calc 2 * n < 3 * p := big _ = 2 * p + p := Nat.succ_mul _ _ _ ≤ 2 * (p * (n / p)) + p :=
        add_le_add_right ((mul_le_mul_left zero_lt_two).mpr <| (le_mul_iff_one_le_right p_pos).mpr n_big) _
    
  · have i_zero : i = 0 := nat.le_zero_iff.mp (Nat.le_of_lt_succₓ H)
    rw [i_zero, pow_zeroₓ, Nat.mod_oneₓ, mul_zero]
    exact zero_lt_one
    

end Nat

