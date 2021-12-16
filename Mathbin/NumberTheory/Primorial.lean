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
  ∏ p in filter prime (range (n+1)), p

local notation x "#" => primorial x

theorem primorial_succ {n : ℕ} (n_big : 1 < n) (r : n % 2 = 1) : (n+1)# = n# :=
  by 
    have not_prime : ¬prime (n+1)
    ·
      intro is_prime 
      cases' prime.eq_two_or_odd is_prime with _ n_even
      ·
        linarith
      ·
        exfalso 
        rw [←not_even_iff] at n_even r 
        have e : Even ((n+1) - n) := (even_sub (lt_add_one n).le).2 (iff_of_false n_even r)
        simp only [add_tsub_cancel_left, not_even_one] at e 
        exact e 
    apply Finset.prod_congr
    ·
      rw [@range_succ (n+1), filter_insert, if_neg not_prime]
    ·
      exact fun _ _ => rfl

theorem dvd_choose_of_middling_prime (p : ℕ) (is_prime : prime p) (m : ℕ) (p_big : (m+1) < p) (p_small : p ≤ (2*m)+1) :
  p ∣ choose ((2*m)+1) (m+1) :=
  by 
    have m_size : (m+1) ≤ (2*m)+1 := le_of_ltₓ (lt_of_lt_of_leₓ p_big p_small)
    have s : ¬p ∣ (m+1)!
    ·
      intro p_div_fact 
      have p_le_succ_m : p ≤ m+1 := (prime.dvd_factorial is_prime).mp p_div_fact 
      linarith 
    have t : ¬p ∣ (((2*m)+1) - m+1)!
    ·
      intro p_div_fact 
      have p_small : p ≤ ((2*m)+1) - m+1 := (prime.dvd_factorial is_prime).mp p_div_fact 
      linarith 
    have expanded : ((choose ((2*m)+1) (m+1)*(m+1)!)*(((2*m)+1) - m+1)!) = ((2*m)+1)! :=
      @choose_mul_factorial_mul_factorial ((2*m)+1) (m+1) m_size 
    have p_div_big_fact : p ∣ ((2*m)+1)! := (prime.dvd_factorial is_prime).mpr p_small 
    rw [←expanded, mul_assocₓ] at p_div_big_fact 
    obtain p_div_choose | p_div_facts : p ∣ choose ((2*m)+1) (m+1) ∨ p ∣ _ !*_ ! :=
      (prime.dvd_mul is_prime).1 p_div_big_fact
    ·
      exact p_div_choose 
    cases (prime.dvd_mul is_prime).1 p_div_facts 
    cc 
    cc

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (a «expr ∈ » s)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (a «expr ∈ » s)
theorem prod_primes_dvd {s : Finset ℕ} :
  ∀ n : ℕ h : ∀ a _ : a ∈ s, prime a div : ∀ a _ : a ∈ s, a ∣ n, (∏ p in s, p) ∣ n :=
  by 
    apply Finset.induction_on s
    ·
      simp 
    ·
      intro a s a_not_in_s induct n primes divs 
      rw [Finset.prod_insert a_not_in_s]
      obtain ⟨k, rfl⟩ : a ∣ n
      ·
        exact divs a (Finset.mem_insert_self a s)
      have step : (∏ p in s, p) ∣ k
      ·
        apply induct k
        ·
          intro b b_in_s 
          exact primes b (Finset.mem_insert_of_mem b_in_s)
        ·
          intro b b_in_s 
          have b_div_n
          ·
            exact divs b (Finset.mem_insert_of_mem b_in_s)
          have a_prime : prime a
          ·
            exact primes a (Finset.mem_insert_self a s)
          have b_prime : prime b
          ·
            exact primes b (Finset.mem_insert_of_mem b_in_s)
          obtain b_div_a | b_div_k : b ∣ a ∨ b ∣ k 
          exact (prime.dvd_mul b_prime).mp b_div_n
          ·
            exfalso 
            have b_eq_a : b = a
            ·
              cases' (Nat.dvd_prime a_prime).1 b_div_a with b_eq_1 b_eq_a
              ·
                subst b_eq_1 
                exfalso 
                exact prime.ne_one b_prime rfl
              ·
                exact b_eq_a 
            subst b_eq_a 
            exact a_not_in_s b_in_s
          ·
            exact b_div_k 
      exact mul_dvd_mul_left a step

theorem primorial_le_4_pow : ∀ n : ℕ, n# ≤ 4 ^ n
| 0 => le_reflₓ _
| 1 => le_of_inf_eq rfl
| n+2 =>
  match Nat.mod_two_eq_zero_or_oneₓ (n+1) with 
  | Or.inl n_odd =>
    match Nat.even_iff.2 n_odd with 
    | ⟨m, twice_m⟩ =>
      let recurse : (m+1) < n+2 :=
        by 
          linarith 
      by 
        calc (n+2)# = ∏ i in filter prime (range ((2*m)+2)), i :=
          by 
            simpa [←twice_m]_ = ∏ i in filter prime (Finset.ico (m+2) ((2*m)+2) ∪ range (m+2)), i :=
          by 
            rw [range_eq_Ico, Finset.union_comm, Finset.Ico_union_Ico_eq_Ico]
            exact bot_le 
            simp only [add_le_add_iff_right]
            linarith _ = ∏ i in filter prime (Finset.ico (m+2) ((2*m)+2)) ∪ filter prime (range (m+2)), i :=
          by 
            rw
              [filter_union]_ =
            (∏ i in filter prime (Finset.ico (m+2) ((2*m)+2)), i)*∏ i in filter prime (range (m+2)), i :=
          by 
            apply Finset.prod_union 
            have disj : Disjoint (Finset.ico (m+2) ((2*m)+2)) (range (m+2))
            ·
              simp only [Finset.disjoint_left, and_imp, Finset.mem_Ico, not_ltₓ, Finset.mem_range]
              intro _ pr _ 
              exact pr 
            exact
              Finset.disjoint_filter_filter disj _ ≤ (∏ i in filter prime (Finset.ico (m+2) ((2*m)+2)), i)*4 ^ m+1 :=
          by 
            exact Nat.mul_le_mul_leftₓ _ (primorial_le_4_pow (m+1))_ ≤ choose ((2*m)+1) (m+1)*4 ^ m+1 :=
          by 
            have s : (∏ i in filter prime (Finset.ico (m+2) ((2*m)+2)), i) ∣ choose ((2*m)+1) (m+1)
            ·
              refine' prod_primes_dvd (choose ((2*m)+1) (m+1)) _ _
              ·
                intro a 
                rw [Finset.mem_filter]
                cc
              ·
                intro a 
                rw [Finset.mem_filter]
                intro pr 
                rcases pr with ⟨size, is_prime⟩
                simp only [Finset.mem_Ico] at size 
                rcases size with ⟨a_big, a_small⟩
                exact dvd_choose_of_middling_prime a is_prime m a_big (nat.lt_succ_iff.mp a_small)
            have r : (∏ i in filter prime (Finset.ico (m+2) ((2*m)+2)), i) ≤ choose ((2*m)+1) (m+1)
            ·
              refine' @Nat.le_of_dvdₓ _ _ _ s 
              exact
                @choose_pos ((2*m)+1) (m+1)
                  (by 
                    linarith)
            exact Nat.mul_le_mul_rightₓ _ r _ = choose ((2*m)+1) m*4 ^ m+1 :=
          by 
            rw [choose_symm_half m]_ ≤ (4 ^ m)*4 ^ m+1 :=
          Nat.mul_le_mul_rightₓ _ (choose_middle_le_pow m)_ = 4 ^ (2*m)+1 :=
          by 
            ringExp _ = 4 ^ n+2 :=
          by 
            rw [←twice_m]
  | Or.inr n_even =>
    by 
      obtain one_lt_n | n_le_one : (1 < n+1) ∨ (n+1) ≤ 1 := lt_or_leₓ 1 (n+1)
      ·
        rw
          [primorial_succ
            (by 
              linarith)
            n_even]
        calc (n+1)# ≤ 4 ^ n.succ := primorial_le_4_pow (n+1)_ ≤ 4 ^ n+2 :=
          pow_le_pow
            (by 
              normNum)
            (Nat.le_succₓ _)
      ·
        have n_zero : n = 0 := eq_bot_iff.2 (succ_le_succ_iff.1 n_le_one)
        normNum [n_zero, primorial, range_succ, prod_filter, not_prime_zero, prime_two]

