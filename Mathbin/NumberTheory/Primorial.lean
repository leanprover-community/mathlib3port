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
  ∏p in filter prime (range (n+1)), p

local notation x "#" => primorial x

-- error in NumberTheory.Primorial: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem primorial_succ
{n : exprℕ()}
(n_big : «expr < »(1, n))
(r : «expr = »(«expr % »(n, 2), 1)) : «expr = »(«expr #»(«expr + »(n, 1)), «expr #»(n)) :=
begin
  have [ident not_prime] [":", expr «expr¬ »(prime «expr + »(n, 1))] [],
  { intros [ident is_prime],
    cases [expr prime.eq_two_or_odd is_prime] ["with", "_", ident n_even],
    { linarith [] [] [] },
    { exfalso,
      rw ["<-", expr not_even_iff] ["at", ident n_even, ident r],
      have [ident e] [":", expr even «expr - »(«expr + »(n, 1), n)] [":=", expr (even_sub (lt_add_one n).le).2 (iff_of_false n_even r)],
      simp [] [] ["only"] ["[", expr add_tsub_cancel_left, ",", expr not_even_one, "]"] [] ["at", ident e],
      exact [expr e] } },
  apply [expr finset.prod_congr],
  { rw ["[", expr @range_succ «expr + »(n, 1), ",", expr filter_insert, ",", expr if_neg not_prime, "]"] [] },
  { exact [expr λ _ _, rfl] }
end

-- error in NumberTheory.Primorial: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem dvd_choose_of_middling_prime
(p : exprℕ())
(is_prime : prime p)
(m : exprℕ())
(p_big : «expr < »(«expr + »(m, 1), p))
(p_small : «expr ≤ »(p, «expr + »(«expr * »(2, m), 1))) : «expr ∣ »(p, choose «expr + »(«expr * »(2, m), 1) «expr + »(m, 1)) :=
begin
  have [ident m_size] [":", expr «expr ≤ »(«expr + »(m, 1), «expr + »(«expr * »(2, m), 1))] [":=", expr le_of_lt (lt_of_lt_of_le p_big p_small)],
  have [ident expanded] [":", expr «expr = »(«expr * »(«expr * »(choose «expr + »(«expr * »(2, m), 1) «expr + »(m, 1), «expr !»(«expr + »(m, 1))), «expr !»(«expr - »(«expr + »(«expr * »(2, m), 1), «expr + »(m, 1)))), «expr !»(«expr + »(«expr * »(2, m), 1)))] [":=", expr @choose_mul_factorial_mul_factorial «expr + »(«expr * »(2, m), 1) «expr + »(m, 1) m_size],
  have [ident p_div_big_fact] [":", expr «expr ∣ »(p, «expr !»(«expr + »(«expr * »(2, m), 1)))] [":=", expr (prime.dvd_factorial is_prime).mpr p_small],
  rw ["[", "<-", expr expanded, ",", expr mul_assoc, "]"] ["at", ident p_div_big_fact],
  have [ident s] [":", expr «expr¬ »(«expr ∣ »(p, «expr !»(«expr + »(m, 1))))] [],
  { intros [ident p_div_fact],
    have [ident p_le_succ_m] [":", expr «expr ≤ »(p, «expr + »(m, 1))] [":=", expr (prime.dvd_factorial is_prime).mp p_div_fact],
    linarith [] [] [] },
  have [ident t] [":", expr «expr¬ »(«expr ∣ »(p, «expr !»(«expr - »(«expr + »(«expr * »(2, m), 1), «expr + »(m, 1)))))] [],
  { intros [ident p_div_fact],
    have [ident p_small] [":", expr «expr ≤ »(p, «expr - »(«expr + »(«expr * »(2, m), 1), «expr + »(m, 1)))] [":=", expr (prime.dvd_factorial is_prime).mp p_div_fact],
    have [ident t] [":", expr «expr = »(«expr - »(«expr + »(«expr * »(2, m), 1), «expr + »(m, 1)), m)] [],
    { norm_num [] [],
      rw [expr two_mul m] [],
      exact [expr add_tsub_cancel_right m m] },
    rw [expr t] ["at", ident p_small],
    obtain [ident p_lt_m, "|", ident rfl, "|", ident m_lt_p, ":", expr _, ":=", expr lt_trichotomy p m],
    { have [ident r] [":", expr «expr < »(m, «expr + »(m, 1))] [":=", expr lt_add_one m],
      linarith [] [] [] },
    { linarith [] [] [] },
    { linarith [] [] [] } },
  obtain [ident p_div_choose, "|", ident p_div_facts, ":", expr «expr ∨ »(«expr ∣ »(p, choose «expr + »(«expr * »(2, m), 1) «expr + »(m, 1)), «expr ∣ »(p, «expr * »(«expr !»(_), «expr !»(_)))), ":=", expr (prime.dvd_mul is_prime).1 p_div_big_fact],
  { exact [expr p_div_choose] },
  cases [expr (prime.dvd_mul is_prime).1 p_div_facts] [],
  cc,
  cc
end

-- error in NumberTheory.Primorial: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem prod_primes_dvd
{s : finset exprℕ()} : ∀
(n : exprℕ())
(h : ∀ a «expr ∈ » s, prime a)
(div : ∀ a «expr ∈ » s, «expr ∣ »(a, n)), «expr ∣ »(«expr∏ in , »((p), s, p), n) :=
begin
  apply [expr finset.induction_on s],
  { simp [] [] [] [] [] [] },
  { intros [ident a, ident s, ident a_not_in_s, ident induct, ident n, ident primes, ident divs],
    rw [expr finset.prod_insert a_not_in_s] [],
    obtain ["⟨", ident k, ",", ident rfl, "⟩", ":", expr «expr ∣ »(a, n)],
    by exact [expr divs a (finset.mem_insert_self a s)],
    have [ident step] [":", expr «expr ∣ »(«expr∏ in , »((p), s, p), k)] [],
    { apply [expr induct k],
      { intros [ident b, ident b_in_s],
        exact [expr primes b (finset.mem_insert_of_mem b_in_s)] },
      { intros [ident b, ident b_in_s],
        have [ident b_div_n] [] [],
        by exact [expr divs b (finset.mem_insert_of_mem b_in_s)],
        have [ident a_prime] [":", expr prime a] [],
        { exact [expr primes a (finset.mem_insert_self a s)] },
        have [ident b_prime] [":", expr prime b] [],
        { exact [expr primes b (finset.mem_insert_of_mem b_in_s)] },
        obtain [ident b_div_a, "|", ident b_div_k, ":", expr «expr ∨ »(«expr ∣ »(b, a), «expr ∣ »(b, k))],
        exact [expr (prime.dvd_mul b_prime).mp b_div_n],
        { exfalso,
          have [ident b_eq_a] [":", expr «expr = »(b, a)] [],
          { cases [expr (nat.dvd_prime a_prime).1 b_div_a] ["with", ident b_eq_1, ident b_eq_a],
            { subst [expr b_eq_1],
              exfalso,
              exact [expr prime.ne_one b_prime rfl] },
            { exact [expr b_eq_a] } },
          subst [expr b_eq_a],
          exact [expr a_not_in_s b_in_s] },
        { exact [expr b_div_k] } } },
    exact [expr mul_dvd_mul_left a step] }
end

-- error in NumberTheory.Primorial: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem primorial_le_4_pow : ∀ n : exprℕ(), «expr ≤ »(«expr #»(n), «expr ^ »(4, n))
| 0 := le_refl _
| 1 := le_of_inf_eq rfl
| «expr + »(n, 2) := match nat.mod_two_eq_zero_or_one «expr + »(n, 1) with
| or.inl n_odd := match nat.even_iff.2 n_odd with
| ⟨m, twice_m⟩ := let recurse : «expr < »(«expr + »(m, 1), «expr + »(n, 2)) := by linarith [] [] [] in
begin
  calc
    «expr = »(«expr #»(«expr + »(n, 2)), «expr∏ in , »((i), filter prime (range «expr + »(«expr * »(2, m), 2)), i)) : by simpa [] [] [] ["[", "<-", expr twice_m, "]"] [] []
    «expr = »(..., «expr∏ in , »((i), filter prime «expr ∪ »(finset.Ico «expr + »(m, 2) «expr + »(«expr * »(2, m), 2), range «expr + »(m, 2)), i)) : begin
      rw ["[", expr range_eq_Ico, ",", expr finset.union_comm, ",", expr finset.Ico_union_Ico_eq_Ico, "]"] [],
      exact [expr bot_le],
      simp [] [] ["only"] ["[", expr add_le_add_iff_right, "]"] [] [],
      linarith [] [] []
    end
    «expr = »(..., «expr∏ in , »((i), «expr ∪ »(filter prime (finset.Ico «expr + »(m, 2) «expr + »(«expr * »(2, m), 2)), filter prime (range «expr + »(m, 2))), i)) : by rw [expr filter_union] []
    «expr = »(..., «expr * »(«expr∏ in , »((i), filter prime (finset.Ico «expr + »(m, 2) «expr + »(«expr * »(2, m), 2)), i), «expr∏ in , »((i), filter prime (range «expr + »(m, 2)), i))) : begin
      apply [expr finset.prod_union],
      have [ident disj] [":", expr disjoint (finset.Ico «expr + »(m, 2) «expr + »(«expr * »(2, m), 2)) (range «expr + »(m, 2))] [],
      { simp [] [] ["only"] ["[", expr finset.disjoint_left, ",", expr and_imp, ",", expr finset.mem_Ico, ",", expr not_lt, ",", expr finset.mem_range, "]"] [] [],
        intros ["_", ident pr, "_"],
        exact [expr pr] },
      exact [expr finset.disjoint_filter_filter disj]
    end
    «expr ≤ »(..., «expr * »(«expr∏ in , »((i), filter prime (finset.Ico «expr + »(m, 2) «expr + »(«expr * »(2, m), 2)), i), «expr ^ »(4, «expr + »(m, 1)))) : by exact [expr nat.mul_le_mul_left _ (primorial_le_4_pow «expr + »(m, 1))]
    «expr ≤ »(..., «expr * »(choose «expr + »(«expr * »(2, m), 1) «expr + »(m, 1), «expr ^ »(4, «expr + »(m, 1)))) : begin
      have [ident s] [":", expr «expr ∣ »(«expr∏ in , »((i), filter prime (finset.Ico «expr + »(m, 2) «expr + »(«expr * »(2, m), 2)), i), choose «expr + »(«expr * »(2, m), 1) «expr + »(m, 1))] [],
      { refine [expr prod_primes_dvd (choose «expr + »(«expr * »(2, m), 1) «expr + »(m, 1)) _ _],
        { intros [ident a],
          rw [expr finset.mem_filter] [],
          cc },
        { intros [ident a],
          rw [expr finset.mem_filter] [],
          intros [ident pr],
          rcases [expr pr, "with", "⟨", ident size, ",", ident is_prime, "⟩"],
          simp [] [] ["only"] ["[", expr finset.mem_Ico, "]"] [] ["at", ident size],
          rcases [expr size, "with", "⟨", ident a_big, ",", ident a_small, "⟩"],
          exact [expr dvd_choose_of_middling_prime a is_prime m a_big (nat.lt_succ_iff.mp a_small)] } },
      have [ident r] [":", expr «expr ≤ »(«expr∏ in , »((i), filter prime (finset.Ico «expr + »(m, 2) «expr + »(«expr * »(2, m), 2)), i), choose «expr + »(«expr * »(2, m), 1) «expr + »(m, 1))] [],
      { refine [expr @nat.le_of_dvd _ _ _ s],
        exact [expr @choose_pos «expr + »(«expr * »(2, m), 1) «expr + »(m, 1) (by linarith [] [] [])] },
      exact [expr nat.mul_le_mul_right _ r]
    end
    «expr = »(..., «expr * »(choose «expr + »(«expr * »(2, m), 1) m, «expr ^ »(4, «expr + »(m, 1)))) : by rw [expr choose_symm_half m] []
    «expr ≤ »(..., «expr * »(«expr ^ »(4, m), «expr ^ »(4, «expr + »(m, 1)))) : nat.mul_le_mul_right _ (choose_middle_le_pow m)
    «expr = »(..., «expr ^ »(4, «expr + »(«expr * »(2, m), 1))) : by ring_exp [] []
    «expr = »(..., «expr ^ »(4, «expr + »(n, 2))) : by rw ["<-", expr twice_m] []
end
end
| or.inr n_even := begin
  obtain [ident one_lt_n, "|", ident n_le_one, ":", expr «expr ∨ »(«expr < »(1, «expr + »(n, 1)), «expr ≤ »(«expr + »(n, 1), 1)), ":=", expr lt_or_le 1 «expr + »(n, 1)],
  { rw [expr primorial_succ (by linarith [] [] []) n_even] [],
    calc
      «expr ≤ »(«expr #»(«expr + »(n, 1)), «expr ^ »(4, n.succ)) : primorial_le_4_pow «expr + »(n, 1)
      «expr ≤ »(..., «expr ^ »(4, «expr + »(n, 2))) : pow_le_pow (by norm_num [] []) (nat.le_succ _) },
  { have [ident n_zero] [":", expr «expr = »(n, 0)] [":=", expr eq_bot_iff.2 (succ_le_succ_iff.1 n_le_one)],
    norm_num ["[", expr n_zero, ",", expr primorial, ",", expr range_succ, ",", expr prod_filter, ",", expr not_prime_zero, ",", expr prime_two, "]"] [] }
end
end

