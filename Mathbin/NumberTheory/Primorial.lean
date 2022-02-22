/-
Copyright (c) 2020 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens
-/
import Mathbin.Tactic.RingExp
import Mathbin.Data.Nat.Parity
import Mathbin.Data.Nat.Choose.Sum

/-!
# Primorial

This file defines the primorial function (the product of primes less than or equal to some bound),
and proves that `primorial n ≤ 4 ^ n`.

## Notations

We use the local notation `n#` for the primorial of `n`: that is, the product of the primes less
than or equal to `n`.
-/


open Finset

open Nat

open_locale BigOperators Nat

/-- The primorial `n#` of `n` is the product of the primes less than or equal to `n`.
-/
def primorial (n : ℕ) : ℕ :=
  ∏ p in filter Nat.Prime (range (n + 1)), p

-- mathport name: «expr #»
local notation x "#" => primorial x

theorem primorial_succ {n : ℕ} (n_big : 1 < n) (r : n % 2 = 1) : (n + 1)# = n# := by
  have not_prime : ¬Nat.Prime (n + 1) := by
    intro is_prime
    cases' prime.eq_two_or_odd is_prime with _ n_even
    · linarith
      
    · apply Nat.zero_ne_one
      rwa [add_mod, r, Nat.one_mod, ← two_mul, mul_oneₓ, Nat.mod_selfₓ] at n_even
      
  apply Finset.prod_congr
  · rw [@range_succ (n + 1), filter_insert, if_neg not_prime]
    
  · exact fun _ _ => rfl
    

theorem dvd_choose_of_middling_prime (p : ℕ) (is_prime : Nat.Prime p) (m : ℕ) (p_big : m + 1 < p)
    (p_small : p ≤ 2 * m + 1) : p ∣ choose (2 * m + 1) (m + 1) := by
  have m_size : m + 1 ≤ 2 * m + 1 := le_of_ltₓ (lt_of_lt_of_leₓ p_big p_small)
  have s : ¬p ∣ (m + 1)! := by
    intro p_div_fact
    have p_le_succ_m : p ≤ m + 1 := (prime.dvd_factorial is_prime).mp p_div_fact
    linarith
  have t : ¬p ∣ (2 * m + 1 - (m + 1))! := by
    intro p_div_fact
    have p_small : p ≤ 2 * m + 1 - (m + 1) := (prime.dvd_factorial is_prime).mp p_div_fact
    linarith
  have expanded : choose (2 * m + 1) (m + 1) * (m + 1)! * (2 * m + 1 - (m + 1))! = (2 * m + 1)! :=
    @choose_mul_factorial_mul_factorial (2 * m + 1) (m + 1) m_size
  have p_div_big_fact : p ∣ (2 * m + 1)! := (prime.dvd_factorial is_prime).mpr p_small
  rw [← expanded, mul_assoc] at p_div_big_fact
  obtain p_div_choose | p_div_facts : p ∣ choose (2 * m + 1) (m + 1) ∨ p ∣ _ ! * _ ! :=
    (prime.dvd_mul is_prime).1 p_div_big_fact
  · exact p_div_choose
    
  cases (prime.dvd_mul is_prime).1 p_div_facts
  cc
  cc

theorem prod_primes_dvd {s : Finset ℕ} :
    ∀ n : ℕ h : ∀, ∀ a ∈ s, ∀, Nat.Prime a div : ∀, ∀ a ∈ s, ∀, a ∣ n, (∏ p in s, p) ∣ n := by
  apply Finset.induction_on s
  · simp
    
  · intro a s a_not_in_s induct n primes divs
    rw [Finset.prod_insert a_not_in_s]
    obtain ⟨k, rfl⟩ : a ∣ n := divs a (Finset.mem_insert_self a s)
    apply mul_dvd_mul_left a
    apply induct k
    · intro b b_in_s
      exact primes b (Finset.mem_insert_of_mem b_in_s)
      
    · intro b b_in_s
      have b_div_n := divs b (Finset.mem_insert_of_mem b_in_s)
      have a_prime := primes a (Finset.mem_insert_self a s)
      have b_prime := primes b (Finset.mem_insert_of_mem b_in_s)
      refine' ((prime.dvd_mul b_prime).mp b_div_n).resolve_left fun b_div_a => _
      obtain rfl : b = a := ((Nat.dvd_prime a_prime).1 b_div_a).resolve_left b_prime.ne_one
      exact a_not_in_s b_in_s
      
    

theorem primorial_le_4_pow : ∀ n : ℕ, n# ≤ 4 ^ n
  | 0 => le_rfl
  | 1 => le_of_inf_eq rfl
  | n + 2 =>
    match Nat.mod_two_eq_zero_or_oneₓ (n + 1) with
    | Or.inl n_odd =>
      match Nat.even_iff.2 n_odd with
      | ⟨m, twice_m⟩ => by
        let recurse : m + 1 < n + 2 := by
          linarith
        calc (n + 2)# = ∏ i in filter Nat.Prime (range (2 * m + 2)), i := by
            simpa [← twice_m]_ = ∏ i in filter Nat.Prime (Finset.ico (m + 2) (2 * m + 2) ∪ range (m + 2)), i := by
            rw [range_eq_Ico, Finset.union_comm, Finset.Ico_union_Ico_eq_Ico]
            exact bot_le
            simp only [add_le_add_iff_right]
            linarith _ =
              ∏ i in filter Nat.Prime (Finset.ico (m + 2) (2 * m + 2)) ∪ filter Nat.Prime (range (m + 2)), i :=
            by
            rw
              [filter_union]_ =
              (∏ i in filter Nat.Prime (Finset.ico (m + 2) (2 * m + 2)), i) *
                ∏ i in filter Nat.Prime (range (m + 2)), i :=
            by
            apply Finset.prod_union
            have disj : Disjoint (Finset.ico (m + 2) (2 * m + 2)) (range (m + 2)) := by
              simp only [Finset.disjoint_left, and_imp, Finset.mem_Ico, not_ltₓ, Finset.mem_range]
              intro _ pr _
              exact pr
            exact
              Finset.disjoint_filter_filter
                disj _ ≤ (∏ i in filter Nat.Prime (Finset.ico (m + 2) (2 * m + 2)), i) * 4 ^ (m + 1) :=
            Nat.mul_le_mul_leftₓ _ (primorial_le_4_pow (m + 1))_ ≤ choose (2 * m + 1) (m + 1) * 4 ^ (m + 1) := by
            have s : (∏ i in filter Nat.Prime (Finset.ico (m + 2) (2 * m + 2)), i) ∣ choose (2 * m + 1) (m + 1) := by
              refine' prod_primes_dvd (choose (2 * m + 1) (m + 1)) _ _
              · intro a
                rw [Finset.mem_filter]
                cc
                
              · intro a
                rw [Finset.mem_filter]
                intro pr
                rcases pr with ⟨size, is_prime⟩
                simp only [Finset.mem_Ico] at size
                rcases size with ⟨a_big, a_small⟩
                exact dvd_choose_of_middling_prime a is_prime m a_big (nat.lt_succ_iff.mp a_small)
                
            have r : (∏ i in filter Nat.Prime (Finset.ico (m + 2) (2 * m + 2)), i) ≤ choose (2 * m + 1) (m + 1) := by
              refine' @Nat.le_of_dvdₓ _ _ _ s
              exact
                @choose_pos (2 * m + 1) (m + 1)
                  (by
                    linarith)
            exact Nat.mul_le_mul_rightₓ _ r _ = choose (2 * m + 1) m * 4 ^ (m + 1) := by
            rw [choose_symm_half m]_ ≤ 4 ^ m * 4 ^ (m + 1) :=
            Nat.mul_le_mul_rightₓ _ (choose_middle_le_pow m)_ = 4 ^ (2 * m + 1) := by
            ring_exp _ = 4 ^ (n + 2) := by
            rw [← twice_m]
    | Or.inr n_even => by
      obtain one_lt_n | n_le_one : 1 < n + 1 ∨ n + 1 ≤ 1 := lt_or_leₓ 1 (n + 1)
      · rw
          [primorial_succ
            (by
              linarith)
            n_even]
        calc (n + 1)# ≤ 4 ^ n.succ := primorial_le_4_pow (n + 1)_ ≤ 4 ^ (n + 2) :=
            pow_le_pow
              (by
                norm_num)
              (Nat.le_succₓ _)
        
      · have n_zero : n = 0 := eq_bot_iff.2 (succ_le_succ_iff.1 n_le_one)
        norm_num [n_zero, primorial, range_succ, prod_filter, Nat.not_prime_zero, Nat.prime_two]
        

