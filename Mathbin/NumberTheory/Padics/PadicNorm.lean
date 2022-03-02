/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathbin.Algebra.Order.AbsoluteValue
import Mathbin.Algebra.FieldPower
import Mathbin.RingTheory.Int.Basic
import Mathbin.Tactic.Basic
import Mathbin.Tactic.RingExp
import Mathbin.NumberTheory.Divisors
import Mathbin.Data.Nat.Factorization

/-!
# p-adic norm

This file defines the p-adic valuation and the p-adic norm on ℚ.

The p-adic valuation on ℚ is the difference of the multiplicities of `p` in the numerator and
denominator of `q`. This function obeys the standard properties of a valuation, with the appropriate
assumptions on p.

The valuation induces a norm on ℚ. This norm is a nonarchimedean absolute value.
It takes values in {0} ∪ {1/p^k | k ∈ ℤ}.

## Notations

This file uses the local notation `/.` for `rat.mk`.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[fact (prime p)]` as a type class argument.

## References

* [F. Q. Gouvêa, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, norm, valuation
-/


universe u

open Nat

open_locale Rat

open multiplicity

/-- For `p ≠ 1`, the p-adic valuation of an integer `z ≠ 0` is the largest natural number `n` such that
p^n divides z.

`padic_val_rat` defines the valuation of a rational `q` to be the valuation of `q.num` minus the
valuation of `q.denom`.
If `q = 0` or `p = 1`, then `padic_val_rat p q` defaults to 0.
-/
def padicValRat (p : ℕ) (q : ℚ) : ℤ :=
  if h : q ≠ 0 ∧ p ≠ 1 then
    (multiplicity (p : ℤ) q.num).get (multiplicity.finite_int_iff.2 ⟨h.2, Rat.num_ne_zero_of_ne_zero h.1⟩) -
      (multiplicity (p : ℤ) q.denom).get
        (multiplicity.finite_int_iff.2
          ⟨h.2, by
            exact_mod_cast Rat.denom_ne_zero _⟩)
  else 0

/-- A simplification of the definition of `padic_val_rat p q` when `q ≠ 0` and `p` is prime.
-/
theorem padic_val_rat_def (p : ℕ) [hp : Fact p.Prime] {q : ℚ} (hq : q ≠ 0) :
    padicValRat p q =
      (multiplicity (p : ℤ) q.num).get (finite_int_iff.2 ⟨hp.1.ne_one, Rat.num_ne_zero_of_ne_zero hq⟩) -
        (multiplicity (p : ℤ) q.denom).get
          (finite_int_iff.2
            ⟨hp.1.ne_one, by
              exact_mod_cast Rat.denom_ne_zero _⟩) :=
  dif_pos ⟨hq, hp.1.ne_one⟩

namespace padicValRat

open multiplicity

variable {p : ℕ}

/-- `padic_val_rat p q` is symmetric in `q`.
-/
@[simp]
protected theorem neg (q : ℚ) : padicValRat p (-q) = padicValRat p q := by
  unfold padicValRat
  split_ifs
  · simp [-add_commₓ] <;> rfl
    
  · exfalso
    simp_all
    
  · exfalso
    simp_all
    
  · rfl
    

/-- `padic_val_rat p 0` is 0 for any `p`.
-/
@[simp]
protected theorem zero (m : Nat) : padicValRat m 0 = 0 :=
  rfl

/-- `padic_val_rat p 1` is 0 for any `p`.
-/
@[simp]
protected theorem one : padicValRat p 1 = 0 := by
  unfold padicValRat <;> split_ifs <;> simp [*]

/-- For `p ≠ 0, p ≠ 1, `padic_val_rat p p` is 1.
-/
@[simp]
theorem padic_val_rat_self (hp : 1 < p) : padicValRat p p = 1 := by
  unfold padicValRat <;> split_ifs <;> simp_all [Nat.one_lt_iff_ne_zero_and_ne_one]

/-- The p-adic value of an integer `z ≠ 0` is the multiplicity of `p` in `z`.
-/
theorem padic_val_rat_of_int (z : ℤ) (hp : p ≠ 1) (hz : z ≠ 0) :
    padicValRat p (z : ℚ) = (multiplicity (p : ℤ) z).get (finite_int_iff.2 ⟨hp, hz⟩) := by
  rw [padicValRat, dif_pos] <;> simp [*] <;> rfl

end padicValRat

/-- A convenience function for the case of `padic_val_rat` when both inputs are natural numbers.
-/
def padicValNat (p : ℕ) (n : ℕ) : ℕ :=
  Int.toNat (padicValRat p n)

section padicValNat

/-- `padic_val_nat` is defined as an `int.to_nat` cast;
this lemma ensures that the cast is well-behaved.
-/
theorem zero_le_padic_val_rat_of_nat (p n : ℕ) : 0 ≤ padicValRat p n := by
  unfold padicValRat
  split_ifs
  · simp
    
  · trivial
    

/-- `padic_val_rat` coincides with `padic_val_nat`.
-/
@[simp, norm_cast]
theorem padic_val_rat_of_nat (p n : ℕ) : ↑(padicValNat p n) = padicValRat p n := by
  unfold padicValNat
  rw [Int.to_nat_of_nonneg (zero_le_padic_val_rat_of_nat p n)]

/-- A simplification of `padic_val_nat` when one input is prime, by analogy with `padic_val_rat_def`.
-/
theorem padic_val_nat_def {p : ℕ} [hp : Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    padicValNat p n =
      (multiplicity p n).get (multiplicity.finite_nat_iff.2 ⟨Nat.Prime.ne_one hp.1, bot_lt_iff_ne_bot.mpr hn⟩) :=
  by
  have n_nonzero : (n : ℚ) ≠ 0 := by
    simpa only [cast_eq_zero, Ne.def]
  -- Infinite loop with @simp padic_val_rat_of_nat unless we restrict the available lemmas here,
  -- hence the very long list
  simpa only [int.coe_nat_multiplicity p n, Rat.coe_nat_denom n, (padic_val_rat_of_nat p n).symm, Int.coe_nat_zero,
    Int.coe_nat_inj', sub_zero, get_one_right, Int.coe_nat_succ, zero_addₓ, Rat.coe_nat_num] using
    padic_val_rat_def p n_nonzero

@[simp]
theorem padic_val_nat_self (p : ℕ) [Fact p.Prime] : padicValNat p p = 1 := by
  simp [padic_val_nat_def (Fact.out p.prime).ne_zero]

theorem one_le_padic_val_nat_of_dvd {n p : Nat} [prime : Fact p.Prime] (nonzero : n ≠ 0) (div : p ∣ n) :
    1 ≤ padicValNat p n := by
  rw [@padic_val_nat_def _ Prime _ nonzero]
  let one_le_mul : _ ≤ multiplicity p n :=
    @multiplicity.le_multiplicity_of_pow_dvd _ _ _ p n 1
      (by
        norm_num
        exact div)
  simp only [Nat.cast_oneₓ] at one_le_mul
  rcases one_le_mul with ⟨_, q⟩
  dsimp  at q
  solve_by_elim

@[simp]
theorem padic_val_nat_zero (m : Nat) : padicValNat m 0 = 0 :=
  rfl

@[simp]
theorem padic_val_nat_one (m : Nat) : padicValNat m 1 = 0 := by
  simp [padicValNat]

end padicValNat

namespace padicValRat

open multiplicity

variable (p : ℕ) [p_prime : Fact p.Prime]

include p_prime

/-- The multiplicity of `p : ℕ` in `a : ℤ` is finite exactly when `a ≠ 0`.
-/
theorem finite_int_prime_iff {p : ℕ} [p_prime : Fact p.Prime] {a : ℤ} : Finite (p : ℤ) a ↔ a ≠ 0 := by
  simp [finite_int_iff, Ne.symm (ne_of_ltₓ p_prime.1.one_lt)]

/-- A rewrite lemma for `padic_val_rat p q` when `q` is expressed in terms of `rat.mk`.
-/
protected theorem defn {q : ℚ} {n d : ℤ} (hqz : q ≠ 0) (qdf : q = n /. d) :
    padicValRat p q =
      (multiplicity (p : ℤ) n).get
          (finite_int_iff.2
            ⟨Ne.symm <| ne_of_ltₓ p_prime.1.one_lt, fun hn => by
              simp_all ⟩) -
        (multiplicity (p : ℤ) d).get
          (finite_int_iff.2
            ⟨Ne.symm <| ne_of_ltₓ p_prime.1.one_lt, fun hd => by
              simp_all ⟩) :=
  by
  have hn : n ≠ 0 := Rat.mk_num_ne_zero_of_ne_zero hqz qdf
  have hd : d ≠ 0 := Rat.mk_denom_ne_zero_of_ne_zero hqz qdf
  let ⟨c, hc1, hc2⟩ := Rat.num_denom_mk hn hd qdf
  rw [padicValRat, dif_pos] <;>
    simp [hc1, hc2, multiplicity.mul' (Nat.prime_iff_prime_int.1 p_prime.1), Ne.symm (ne_of_ltₓ p_prime.1.one_lt), hqz]

/-- A rewrite lemma for `padic_val_rat p (q * r)` with conditions `q ≠ 0`, `r ≠ 0`.
-/
protected theorem mul {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) : padicValRat p (q * r) = padicValRat p q + padicValRat p r :=
  by
  have : q * r = q.num * r.num /. (↑q.denom * ↑r.denom) := by
    rw_mod_cast[Rat.mul_num_denom]
  have hq' : q.num /. q.denom ≠ 0 := by
    rw [Rat.num_denom] <;> exact hq
  have hr' : r.num /. r.denom ≠ 0 := by
    rw [Rat.num_denom] <;> exact hr
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 p_prime.1
  rw [padicValRat.defn p (mul_ne_zero hq hr) this]
  conv_rhs => rw [← @Rat.num_denom q, padicValRat.defn p hq', ← @Rat.num_denom r, padicValRat.defn p hr']
  rw [multiplicity.mul' hp', multiplicity.mul' hp'] <;> simp [add_commₓ, add_left_commₓ, sub_eq_add_neg]

/-- A rewrite lemma for `padic_val_rat p (q^k)` with condition `q ≠ 0`.
-/
protected theorem pow {q : ℚ} (hq : q ≠ 0) {k : ℕ} : padicValRat p (q ^ k) = k * padicValRat p q := by
  induction k <;> simp [*, padicValRat.mul _ hq (pow_ne_zero _ hq), pow_succₓ, add_mulₓ, add_commₓ]

/-- A rewrite lemma for `padic_val_rat p (q⁻¹)` with condition `q ≠ 0`.
-/
protected theorem inv {q : ℚ} (hq : q ≠ 0) : padicValRat p q⁻¹ = -padicValRat p q := by
  rw [eq_neg_iff_add_eq_zero, ← padicValRat.mul p (inv_ne_zero hq) hq, inv_mul_cancel hq, padicValRat.one]

/-- A rewrite lemma for `padic_val_rat p (q / r)` with conditions `q ≠ 0`, `r ≠ 0`.
-/
protected theorem div {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) : padicValRat p (q / r) = padicValRat p q - padicValRat p r :=
  by
  rw [div_eq_mul_inv, padicValRat.mul p hq (inv_ne_zero hr), padicValRat.inv p hr, sub_eq_add_neg]

/-- A condition for `padic_val_rat p (n₁ / d₁) ≤ padic_val_rat p (n₂ / d₂),
in terms of divisibility by `p^n`.
-/
theorem padic_val_rat_le_padic_val_rat_iff {n₁ n₂ d₁ d₂ : ℤ} (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0) (hd₁ : d₁ ≠ 0)
    (hd₂ : d₂ ≠ 0) :
    padicValRat p (n₁ /. d₁) ≤ padicValRat p (n₂ /. d₂) ↔ ∀ n : ℕ, ↑p ^ n ∣ n₁ * d₂ → ↑p ^ n ∣ n₂ * d₁ := by
  have hf1 : Finite (p : ℤ) (n₁ * d₂) := finite_int_prime_iff.2 (mul_ne_zero hn₁ hd₂)
  have hf2 : Finite (p : ℤ) (n₂ * d₁) := finite_int_prime_iff.2 (mul_ne_zero hn₂ hd₁)
  conv =>
    lhs rw [padicValRat.defn p (Rat.mk_ne_zero_of_ne_zero hn₁ hd₁) rfl,
      padicValRat.defn p (Rat.mk_ne_zero_of_ne_zero hn₂ hd₂) rfl, sub_le_iff_le_add', ← add_sub_assoc,
      le_sub_iff_add_le]norm_cast rw [← multiplicity.mul' (Nat.prime_iff_prime_int.1 p_prime.1) hf1, add_commₓ, ←
      multiplicity.mul' (Nat.prime_iff_prime_int.1 p_prime.1) hf2, Enat.get_le_get, multiplicity_le_multiplicity_iff]

/-- Sufficient conditions to show that the p-adic valuation of `q` is less than or equal to the
p-adic vlauation of `q + r`.
-/
theorem le_padic_val_rat_add_of_le {q r : ℚ} (hqr : q + r ≠ 0) (h : padicValRat p q ≤ padicValRat p r) :
    padicValRat p q ≤ padicValRat p (q + r) :=
  if hq : q = 0 then by
    simpa [hq] using h
  else
    if hr : r = 0 then by
      simp [hr]
    else by
      have hqn : q.num ≠ 0 := Rat.num_ne_zero_of_ne_zero hq
      have hqd : (q.denom : ℤ) ≠ 0 := by
        exact_mod_cast Rat.denom_ne_zero _
      have hrn : r.num ≠ 0 := Rat.num_ne_zero_of_ne_zero hr
      have hrd : (r.denom : ℤ) ≠ 0 := by
        exact_mod_cast Rat.denom_ne_zero _
      have hqreq : q + r = (q.num * r.denom + q.denom * r.num : ℤ) /. (↑q.denom * ↑r.denom : ℤ) := Rat.add_num_denom _ _
      have hqrd : q.num * ↑r.denom + ↑q.denom * r.num ≠ 0 := Rat.mk_num_ne_zero_of_ne_zero hqr hqreq
      conv_lhs => rw [← @Rat.num_denom q]
      rw [hqreq, padic_val_rat_le_padic_val_rat_iff p hqn hqrd hqd (mul_ne_zero hqd hrd), ←
        multiplicity_le_multiplicity_iff, mul_left_commₓ, multiplicity.mul (Nat.prime_iff_prime_int.1 p_prime.1),
        add_mulₓ]
      rw [← @Rat.num_denom q, ← @Rat.num_denom r, padic_val_rat_le_padic_val_rat_iff p hqn hrn hqd hrd, ←
        multiplicity_le_multiplicity_iff] at h
      calc
        _ ≤ min (multiplicity (↑p) (q.num * ↑r.denom * ↑q.denom)) (multiplicity (↑p) (↑q.denom * r.num * ↑q.denom)) :=
          le_minₓ
            (by
              rw [@multiplicity.mul _ _ _ _ (_ * _) _ (Nat.prime_iff_prime_int.1 p_prime.1), add_commₓ])
            (by
              rw [mul_assoc, @multiplicity.mul _ _ _ _ (q.denom : ℤ) (_ * _) (Nat.prime_iff_prime_int.1 p_prime.1)] <;>
                exact add_le_add_left h _)_ ≤ _ :=
          min_le_multiplicity_add

/-- The minimum of the valuations of `q` and `r` is less than or equal to the valuation of `q + r`.
-/
theorem min_le_padic_val_rat_add {q r : ℚ} (hqr : q + r ≠ 0) :
    min (padicValRat p q) (padicValRat p r) ≤ padicValRat p (q + r) :=
  (le_totalₓ (padicValRat p q) (padicValRat p r)).elim
    (fun h => by
      rw [min_eq_leftₓ h] <;> exact le_padic_val_rat_add_of_le _ hqr h)
    fun h => by
    rw [min_eq_rightₓ h, add_commₓ] <;>
      exact
        le_padic_val_rat_add_of_le _
          (by
            rwa [add_commₓ])
          h

open_locale BigOperators

/-- A finite sum of rationals with positive p-adic valuation has positive p-adic valuation
  (if the sum is non-zero). -/
theorem sum_pos_of_pos {n : ℕ} {F : ℕ → ℚ} (hF : ∀ i, i < n → 0 < padicValRat p (F i))
    (hn0 : (∑ i in Finset.range n, F i) ≠ 0) : 0 < padicValRat p (∑ i in Finset.range n, F i) := by
  induction' n with d hd
  · exact False.elim (hn0 rfl)
    
  · rw [Finset.sum_range_succ] at hn0⊢
    by_cases' h : (∑ x : ℕ in Finset.range d, F x) = 0
    · rw [h, zero_addₓ]
      exact hF d (lt_add_one _)
      
    · refine' lt_of_lt_of_leₓ _ (min_le_padic_val_rat_add p hn0)
      · refine' lt_minₓ (hd (fun i hi => _) h) (hF d (lt_add_one _))
        exact hF _ (lt_transₓ hi (lt_add_one _))
        
      
    

end padicValRat

namespace padicValNat

/-- A rewrite lemma for `padic_val_nat p (q * r)` with conditions `q ≠ 0`, `r ≠ 0`.
-/
protected theorem mul (p : ℕ) [p_prime : Fact p.Prime] {q r : ℕ} (hq : q ≠ 0) (hr : r ≠ 0) :
    padicValNat p (q * r) = padicValNat p q + padicValNat p r := by
  apply Int.coe_nat_inj
  simp only [padic_val_rat_of_nat, Nat.cast_mulₓ]
  rw [padicValRat.mul]
  norm_cast
  exact cast_ne_zero.mpr hq
  exact cast_ne_zero.mpr hr

protected theorem div_of_dvd (p : ℕ) [hp : Fact p.Prime] {a b : ℕ} (h : b ∣ a) :
    padicValNat p (a / b) = padicValNat p a - padicValNat p b := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp
    
  obtain ⟨k, rfl⟩ := h
  obtain ⟨hb, hk⟩ := mul_ne_zero_iff.mp ha
  rw [mul_comm, k.mul_div_cancel hb.bot_lt, padicValNat.mul p hk hb, Nat.add_sub_cancel]

/-- Dividing out by a prime factor reduces the padic_val_nat by 1.
-/
protected theorem div {p : ℕ} [p_prime : Fact p.Prime] {b : ℕ} (dvd : p ∣ b) :
    padicValNat p (b / p) = padicValNat p b - 1 := by
  convert padicValNat.div_of_dvd p dvd
  rw [padic_val_nat_self p]

/-- A version of `padic_val_rat.pow` for `padic_val_nat` -/
protected theorem pow (p q n : ℕ) [Fact p.Prime] (hq : q ≠ 0) : padicValNat p (q ^ n) = n * padicValNat p q := by
  apply @Nat.cast_injective ℤ
  push_cast
  exact padicValRat.pow _ (cast_ne_zero.mpr hq)

@[simp]
protected theorem prime_pow (p n : ℕ) [Fact p.Prime] : padicValNat p (p ^ n) = n := by
  rw [padicValNat.pow p _ _ (Fact.out p.prime).ne_zero, padic_val_nat_self p, mul_oneₓ]

protected theorem div_pow {p : ℕ} [p_prime : Fact p.Prime] {b k : ℕ} (dvd : p ^ k ∣ b) :
    padicValNat p (b / p ^ k) = padicValNat p b - k := by
  convert padicValNat.div_of_dvd p dvd
  rw [padicValNat.prime_pow]

end padicValNat

section padicValNat

/-- If a prime doesn't appear in `n`, `padic_val_nat p n` is `0`.
-/
theorem padic_val_nat_of_not_dvd {p : ℕ} [Fact p.Prime] {n : ℕ} (not_dvd : ¬p ∣ n) : padicValNat p n = 0 := by
  by_cases' hn : n = 0
  · subst hn
    simp at not_dvd
    trivial
    
  · rw [padic_val_nat_def hn]
    exact
      (@multiplicity.unique' _ _ _ p n 0
          (by
            simp )
          (by
            simpa using not_dvd)).symm
    assumption
    

theorem dvd_of_one_le_padic_val_nat {n p : Nat} [prime : Fact p.Prime] (hp : 1 ≤ padicValNat p n) : p ∣ n := by
  by_contra h
  rw [padic_val_nat_of_not_dvd h] at hp
  exact lt_irreflₓ 0 (lt_of_lt_of_leₓ zero_lt_one hp)

theorem pow_padic_val_nat_dvd {p n : ℕ} [Fact (Nat.Prime p)] : p ^ padicValNat p n ∣ n := by
  cases' Nat.eq_zero_or_posₓ n with hn hn
  · rw [hn]
    exact dvd_zero (p ^ padicValNat p 0)
    
  · rw [multiplicity.pow_dvd_iff_le_multiplicity]
    apply le_of_eqₓ
    rw [padic_val_nat_def (ne_of_gtₓ hn)]
    · apply Enat.coe_get
      
    · infer_instance
      
    

theorem pow_succ_padic_val_nat_not_dvd {p n : ℕ} [hp : Fact (Nat.Prime p)] (hn : 0 < n) :
    ¬p ^ (padicValNat p n + 1) ∣ n := by
  rw [multiplicity.pow_dvd_iff_le_multiplicity]
  rw [padic_val_nat_def (ne_of_gtₓ hn)]
  · rw [Nat.cast_addₓ, Enat.coe_get]
    simp only [Nat.cast_oneₓ, not_leₓ]
    apply Enat.lt_add_one (ne_top_iff_finite.2 (finite_nat_iff.2 ⟨hp.elim.ne_one, hn⟩))
    
  · infer_instance
    

theorem padic_val_nat_primes {p q : ℕ} [p_prime : Fact p.Prime] [q_prime : Fact q.Prime] (neq : p ≠ q) :
    padicValNat p q = 0 :=
  @padic_val_nat_of_not_dvd p p_prime q <| (not_congr (Iff.symm (prime_dvd_prime_iff_eq p_prime.1 q_prime.1))).mp neq

protected theorem padicValNat.div' {p : ℕ} [p_prime : Fact p.Prime] :
    ∀ {m : ℕ} cpm : Coprime p m {b : ℕ} dvd : m ∣ b, padicValNat p (b / m) = padicValNat p b
  | 0 => fun cpm b dvd => by
    rw [zero_dvd_iff] at dvd
    rw [dvd, Nat.zero_divₓ]
  | n + 1 => fun cpm b dvd => by
    rcases dvd with ⟨c, rfl⟩
    rw [mul_div_right c (Nat.succ_posₓ _)]
    by_cases' hc : c = 0
    · rw [hc, mul_zero]
      
    · rw [padicValNat.mul]
      · suffices ¬p ∣ n + 1 by
          rw [padic_val_nat_of_not_dvd this, zero_addₓ]
        contrapose! cpm
        exact p_prime.1.dvd_iff_not_coprime.mp cpm
        
      · exact Nat.succ_ne_zero _
        
      · exact hc
        
      

theorem padic_val_nat_eq_factorization (p n : ℕ) [hp : Fact p.Prime] : padicValNat p n = n.factorization p := by
  by_cases' hn : n = 0
  · subst hn
    simp
    
  rw [@padic_val_nat_def p _ n hn]
  simp [@multiplicity_eq_factorization n p hp.elim hn]

open_locale BigOperators

theorem prod_pow_prime_padic_val_nat (n : Nat) (hn : n ≠ 0) (m : Nat) (pr : n < m) :
    (∏ p in Finset.filter Nat.Prime (Finset.range m), p ^ padicValNat p n) = n := by
  nth_rw_rhs 0[← factorization_prod_pow_eq_self hn]
  rw [eq_comm]
  apply Finset.prod_subset_one_on_sdiff
  · exact fun p hp =>
      finset.mem_filter.mpr
        ⟨finset.mem_range.mpr (gt_of_gt_of_geₓ pr (le_of_mem_factorization hp)), prime_of_mem_factorization hp⟩
    
  · intro p hp
    cases' finset.mem_sdiff.mp hp with hp1 hp2
    have := fact_iff.mpr (finset.mem_filter.mp hp1).2
    rw [padic_val_nat_eq_factorization p n]
    simp [finsupp.not_mem_support_iff.mp hp2]
    
  · intro p hp
    have := fact_iff.mpr (prime_of_mem_factorization hp)
    simp [padic_val_nat_eq_factorization]
    

theorem range_pow_padic_val_nat_subset_divisors {n : ℕ} (p : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    (Finset.range (padicValNat p n + 1)).Image (pow p) ⊆ n.divisors := by
  intro t ht
  simp only [exists_prop, Finset.mem_image, Finset.mem_range] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  rw [Nat.mem_divisors]
  exact
    ⟨(pow_dvd_pow p <| by
            linarith).trans
        pow_padic_val_nat_dvd,
      hn⟩

theorem range_pow_padic_val_nat_subset_divisors' {n : ℕ} (p : ℕ) [h : Fact p.Prime] :
    ((Finset.range (padicValNat p n)).Image fun t => p ^ (t + 1)) ⊆ n.divisors \ {1} := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
    
  intro t ht
  simp only [exists_prop, Finset.mem_image, Finset.mem_range] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  rw [Finset.mem_sdiff, Nat.mem_divisors]
  refine'
    ⟨⟨(pow_dvd_pow p <| by
              linarith).trans
          pow_padic_val_nat_dvd,
        hn⟩,
      _⟩
  rw [Finset.mem_singleton]
  nth_rw 1[← one_pow (k + 1)]
  exact (Nat.pow_lt_pow_of_lt_left h.1.one_lt <| Nat.succ_posₓ k).ne'

end padicValNat

/-- If `q ≠ 0`, the p-adic norm of a rational `q` is `p ^ (-(padic_val_rat p q))`.
If `q = 0`, the p-adic norm of `q` is 0.
-/
def padicNorm (p : ℕ) (q : ℚ) : ℚ :=
  if q = 0 then 0 else (↑p : ℚ) ^ -padicValRat p q

namespace padicNorm

section padicNorm

open padicValRat

variable (p : ℕ)

/-- Unfolds the definition of the p-adic norm of `q` when `q ≠ 0`.
-/
@[simp]
protected theorem eq_zpow_of_nonzero {q : ℚ} (hq : q ≠ 0) : padicNorm p q = p ^ -padicValRat p q := by
  simp [hq, padicNorm]

/-- The p-adic norm is nonnegative.
-/
protected theorem nonneg (q : ℚ) : 0 ≤ padicNorm p q :=
  if hq : q = 0 then by
    simp [hq, padicNorm]
  else by
    unfold padicNorm <;> split_ifs
    apply zpow_nonneg
    exact_mod_cast Nat.zero_leₓ _

/-- The p-adic norm of 0 is 0.
-/
@[simp]
protected theorem zero : padicNorm p 0 = 0 := by
  simp [padicNorm]

/-- The p-adic norm of 1 is 1.
-/
@[simp]
protected theorem one : padicNorm p 1 = 1 := by
  simp [padicNorm]

/-- The p-adic norm of `p` is `1/p` if `p > 1`.

See also `padic_norm.padic_norm_p_of_prime` for a version that assumes `p` is prime.
-/
theorem padic_norm_p {p : ℕ} (hp : 1 < p) : padicNorm p p = 1 / p := by
  simp [padicNorm,
    show p ≠ 0 by
      linarith,
    padicValRat.padic_val_rat_self hp]

/-- The p-adic norm of `p` is `1/p` if `p` is prime.

See also `padic_norm.padic_norm_p` for a version that assumes `1 < p`.
-/
@[simp]
theorem padic_norm_p_of_prime (p : ℕ) [Fact p.Prime] : padicNorm p p = 1 / p :=
  padic_norm_p <| Nat.Prime.one_lt (Fact.out _)

/-- The p-adic norm of `q` is `1` if `q` is prime and not equal to `p`. -/
theorem padic_norm_of_prime_of_ne {p q : ℕ} [p_prime : Fact p.Prime] [q_prime : Fact q.Prime] (neq : p ≠ q) :
    padicNorm p q = 1 := by
  have p : padicValRat p q = 0 := by
    exact_mod_cast @padic_val_nat_primes p q p_prime q_prime neq
  simp [padicNorm, p, q_prime.1.1, q_prime.1.ne_zero]

/-- The p-adic norm of `p` is less than 1 if `1 < p`.

See also `padic_norm.padic_norm_p_lt_one_of_prime` for a version assuming `prime p`.
-/
theorem padic_norm_p_lt_one {p : ℕ} (hp : 1 < p) : padicNorm p p < 1 := by
  rw [padic_norm_p hp, div_lt_iff, one_mulₓ]
  · exact_mod_cast hp
    
  · exact_mod_cast zero_lt_one.trans hp
    

/-- The p-adic norm of `p` is less than 1 if `p` is prime.

See also `padic_norm.padic_norm_p_lt_one` for a version assuming `1 < p`.
-/
theorem padic_norm_p_lt_one_of_prime (p : ℕ) [Fact p.Prime] : padicNorm p p < 1 :=
  padic_norm_p_lt_one <| Nat.Prime.one_lt (Fact.out _)

/-- `padic_norm p q` takes discrete values `p ^ -z` for `z : ℤ`.
-/
protected theorem values_discrete {q : ℚ} (hq : q ≠ 0) : ∃ z : ℤ, padicNorm p q = p ^ -z :=
  ⟨padicValRat p q, by
    simp [padicNorm, hq]⟩

/-- `padic_norm p` is symmetric.
-/
@[simp]
protected theorem neg (q : ℚ) : padicNorm p (-q) = padicNorm p q :=
  if hq : q = 0 then by
    simp [hq]
  else by
    simp [padicNorm, hq]

variable [hp : Fact p.Prime]

include hp

/-- If `q ≠ 0`, then `padic_norm p q ≠ 0`.
-/
protected theorem nonzero {q : ℚ} (hq : q ≠ 0) : padicNorm p q ≠ 0 := by
  rw [padicNorm.eq_zpow_of_nonzero p hq]
  apply zpow_ne_zero_of_ne_zero
  exact_mod_cast ne_of_gtₓ hp.1.Pos

/-- If the p-adic norm of `q` is 0, then `q` is 0.
-/
theorem zero_of_padic_norm_eq_zero {q : ℚ} (h : padicNorm p q = 0) : q = 0 := by
  apply by_contradiction
  intro hq
  unfold padicNorm  at h
  rw [if_neg hq] at h
  apply absurd h
  apply zpow_ne_zero_of_ne_zero
  exact_mod_cast hp.1.ne_zero

/-- The p-adic norm is multiplicative.
-/
@[simp]
protected theorem mul (q r : ℚ) : padicNorm p (q * r) = padicNorm p q * padicNorm p r :=
  if hq : q = 0 then by
    simp [hq]
  else
    if hr : r = 0 then by
      simp [hr]
    else by
      have : q * r ≠ 0 := mul_ne_zero hq hr
      have : (↑p : ℚ) ≠ 0 := by
        simp [hp.1.ne_zero]
      simp [padicNorm, *, padicValRat.mul, zpow_add₀ this, mul_comm]

/-- The p-adic norm respects division.
-/
@[simp]
protected theorem div (q r : ℚ) : padicNorm p (q / r) = padicNorm p q / padicNorm p r :=
  if hr : r = 0 then by
    simp [hr]
  else
    eq_div_of_mul_eq (padicNorm.nonzero _ hr)
      (by
        rw [← padicNorm.mul, div_mul_cancel _ hr])

/-- The p-adic norm of an integer is at most 1.
-/
protected theorem of_int (z : ℤ) : padicNorm p ↑z ≤ 1 :=
  if hz : z = 0 then by
    simp [hz, zero_le_one]
  else by
    unfold padicNorm
    rw [if_neg _]
    · refine' zpow_le_one_of_nonpos _ _
      · exact_mod_cast le_of_ltₓ hp.1.one_lt
        
      · rw [padic_val_rat_of_int _ hp.1.ne_one hz, neg_nonpos]
        norm_cast
        simp
        
      
    exact_mod_cast hz

private theorem nonarchimedean_aux {q r : ℚ} (h : padicValRat p q ≤ padicValRat p r) :
    padicNorm p (q + r) ≤ max (padicNorm p q) (padicNorm p r) :=
  have hnqp : padicNorm p q ≥ 0 := padicNorm.nonneg _ _
  have hnrp : padicNorm p r ≥ 0 := padicNorm.nonneg _ _
  if hq : q = 0 then by
    simp [hq, max_eq_rightₓ hnrp, le_max_rightₓ]
  else
    if hr : r = 0 then by
      simp [hr, max_eq_leftₓ hnqp, le_max_leftₓ]
    else
      if hqr : q + r = 0 then
        le_transₓ
          (by
            simpa [hqr] using hnqp)
          (le_max_leftₓ _ _)
      else by
        unfold padicNorm
        split_ifs
        apply le_max_iff.2
        left
        apply zpow_le_of_le
        · exact_mod_cast le_of_ltₓ hp.1.one_lt
          
        · apply neg_le_neg
          have : padicValRat p q = min (padicValRat p q) (padicValRat p r) := (min_eq_leftₓ h).symm
          rw [this]
          apply min_le_padic_val_rat_add <;> assumption
          

/-- The p-adic norm is nonarchimedean: the norm of `p + q` is at most the max of the norm of `p` and
the norm of `q`.
-/
protected theorem nonarchimedean {q r : ℚ} : padicNorm p (q + r) ≤ max (padicNorm p q) (padicNorm p r) := by
  wlog hle := le_totalₓ (padicValRat p q) (padicValRat p r) using q r
  exact nonarchimedean_aux p hle

/-- The p-adic norm respects the triangle inequality: the norm of `p + q` is at most the norm of `p`
plus the norm of `q`.
-/
theorem triangle_ineq (q r : ℚ) : padicNorm p (q + r) ≤ padicNorm p q + padicNorm p r :=
  calc
    padicNorm p (q + r) ≤ max (padicNorm p q) (padicNorm p r) := padicNorm.nonarchimedean p
    _ ≤ padicNorm p q + padicNorm p r := max_le_add_of_nonneg (padicNorm.nonneg p _) (padicNorm.nonneg p _)
    

/-- The p-adic norm of a difference is at most the max of each component. Restates the archimedean
property of the p-adic norm.
-/
protected theorem sub {q r : ℚ} : padicNorm p (q - r) ≤ max (padicNorm p q) (padicNorm p r) := by
  rw [sub_eq_add_neg, ← padicNorm.neg p r] <;> apply padicNorm.nonarchimedean

/-- If the p-adic norms of `q` and `r` are different, then the norm of `q + r` is equal to the max of
the norms of `q` and `r`.
-/
theorem add_eq_max_of_ne {q r : ℚ} (hne : padicNorm p q ≠ padicNorm p r) :
    padicNorm p (q + r) = max (padicNorm p q) (padicNorm p r) := by
  wlog hle := le_totalₓ (padicNorm p r) (padicNorm p q) using q r
  have hlt : padicNorm p r < padicNorm p q := lt_of_le_of_neₓ hle hne.symm
  have : padicNorm p q ≤ max (padicNorm p (q + r)) (padicNorm p r) :=
    calc
      padicNorm p q = padicNorm p (q + r - r) := by
        congr <;> ring
      _ ≤ max (padicNorm p (q + r)) (padicNorm p (-r)) := padicNorm.nonarchimedean p
      _ = max (padicNorm p (q + r)) (padicNorm p r) := by
        simp
      
  have hnge : padicNorm p r ≤ padicNorm p (q + r) := by
    apply le_of_not_gtₓ
    intro hgt
    rw [max_eq_right_of_ltₓ hgt] at this
    apply not_lt_of_geₓ this
    assumption
  have : padicNorm p q ≤ padicNorm p (q + r) := by
    rwa [max_eq_leftₓ hnge] at this
  apply _root_.le_antisymm
  · apply padicNorm.nonarchimedean p
    
  · rw [max_eq_left_of_ltₓ hlt]
    assumption
    

/-- The p-adic norm is an absolute value: positive-definite and multiplicative, satisfying the triangle
inequality.
-/
instance : IsAbsoluteValue (padicNorm p) where
  abv_nonneg := padicNorm.nonneg p
  abv_eq_zero := by
    intros
    constructor <;> intro
    · apply zero_of_padic_norm_eq_zero p
      assumption
      
    · simp [*]
      
  abv_add := padicNorm.triangle_ineq p
  abv_mul := padicNorm.mul p

variable {p}

theorem dvd_iff_norm_le {n : ℕ} {z : ℤ} : ↑(p ^ n) ∣ z ↔ padicNorm p z ≤ ↑p ^ (-n : ℤ) := by
  unfold padicNorm
  split_ifs with hz
  · norm_cast  at hz
    have : 0 ≤ (p ^ n : ℚ) := by
      apply pow_nonneg
      exact_mod_cast le_of_ltₓ hp.1.Pos
    simp [hz, this]
    
  · rw [zpow_le_iff_le, neg_le_neg_iff, padic_val_rat_of_int _ hp.1.ne_one _]
    · norm_cast
      rw [← Enat.coe_le_coe, Enat.coe_get, ← multiplicity.pow_dvd_iff_le_multiplicity]
      simp
      
    · exact_mod_cast hz
      
    · exact_mod_cast hp.1.one_lt
      
    

end padicNorm

end padicNorm

