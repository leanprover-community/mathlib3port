/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathbin.Data.Nat.Gcd
import Mathbin.Logic.Function.Iterate
import Mathbin.Data.Finset.NatAntidiagonal
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Tactic.Ring

/-!
# The Fibonacci Sequence

## Summary

Definition of the Fibonacci sequence `F₀ = 0, F₁ = 1, Fₙ₊₂ = Fₙ + Fₙ₊₁`.

## Main Definitions

- `nat.fib` returns the stream of Fibonacci numbers.

## Main Statements

- `nat.fib_add_two`: shows that `fib` indeed satisfies the Fibonacci recurrence `Fₙ₊₂ = Fₙ + Fₙ₊₁.`.
- `nat.fib_gcd`: `fib n` is a strong divisibility sequence.
- `nat.fib_succ_eq_sum_choose`: `fib` is given by the sum of `nat.choose` along an antidiagonal.

## Implementation Notes

For efficiency purposes, the sequence is defined using `stream.iterate`.

## Tags

fib, fibonacci
-/


open_locale BigOperators

namespace Nat

/-- Implementation of the fibonacci sequence satisfying
`fib 0 = 0, fib 1 = 1, fib (n + 2) = fib n + fib (n + 1)`.

*Note:* We use a stream iterator for better performance when compared to the naive recursive
implementation.
-/
@[pp_nodot]
def fib (n : ℕ) : ℕ :=
  (((fun p : ℕ × ℕ => (p.snd, p.fst + p.snd))^[n]) (0, 1)).fst

@[simp]
theorem fib_zero : fib 0 = 0 :=
  rfl

@[simp]
theorem fib_one : fib 1 = 1 :=
  rfl

@[simp]
theorem fib_two : fib 2 = 1 :=
  rfl

/-- Shows that `fib` indeed satisfies the Fibonacci recurrence `Fₙ₊₂ = Fₙ + Fₙ₊₁.` -/
theorem fib_add_two {n : ℕ} : fib (n + 2) = fib n + fib (n + 1) := by
  simp only [fib, Function.iterate_succ']

theorem fib_le_fib_succ {n : ℕ} : fib n ≤ fib (n + 1) := by
  cases n <;> simp [fib_add_two]

@[mono]
theorem fib_mono : Monotone fib :=
  monotone_nat_of_le_succ fun _ => fib_le_fib_succ

theorem fib_pos {n : ℕ} (n_pos : 0 < n) : 0 < fib n :=
  calc
    0 < fib 1 := by
      decide
    _ ≤ fib n := fib_mono n_pos
    

theorem fib_lt_fib_succ {n : ℕ} (hn : 2 ≤ n) : fib n < fib (n + 1) := by
  rcases le_iff_exists_add.1 hn with ⟨n, rfl⟩
  simp only [add_commₓ 2, fib_add_two]
  rw [add_commₓ]
  exact lt_add_of_pos_left _ (fib_pos succ_pos')

/-- `fib (n + 2)` is strictly monotone. -/
theorem fib_add_two_strict_mono : StrictMono fun n => fib (n + 2) := by
  refine' strict_mono_nat_of_lt_succ fun n => _
  rw [add_right_commₓ]
  exact fib_lt_fib_succ (self_le_add_left _ _)

theorem le_fib_self {n : ℕ} (five_le_n : 5 ≤ n) : n ≤ fib n := by
  induction' five_le_n with n five_le_n IH
  · -- 5 ≤ fib 5
    rfl
    
  · -- n + 1 ≤ fib (n + 1) for 5 ≤ n
    rw [succ_le_iff]
    calc n ≤ fib n := IH _ < fib (n + 1) :=
        fib_lt_fib_succ
          (le_transₓ
            (by
              decide)
            five_le_n)
    

/-- Subsequent Fibonacci numbers are coprime,
  see https://proofwiki.org/wiki/Consecutive_Fibonacci_Numbers_are_Coprime -/
theorem fib_coprime_fib_succ (n : ℕ) : Nat.Coprime (fib n) (fib (n + 1)) := by
  induction' n with n ih
  · simp
    
  · rw [fib_add_two, coprime_add_self_right]
    exact ih.symm
    

/-- See https://proofwiki.org/wiki/Fibonacci_Number_in_terms_of_Smaller_Fibonacci_Numbers -/
theorem fib_add (m n : ℕ) : fib m * fib n + fib (m + 1) * fib (n + 1) = fib (m + n + 1) := by
  induction' n with n ih generalizing m
  · simp
    
  · intros
    specialize ih (m + 1)
    rw [add_assocₓ m 1 n, add_commₓ 1 n] at ih
    simp only [fib_add_two, ← ih]
    ring
    

theorem gcd_fib_add_self (m n : ℕ) : gcdₓ (fib m) (fib (n + m)) = gcdₓ (fib m) (fib n) := by
  cases Nat.eq_zero_or_posₓ n
  · rw [h]
    simp
    
  replace h := Nat.succ_pred_eq_of_posₓ h
  rw [← h, succ_eq_add_one]
  calc gcd (fib m) (fib (n.pred + 1 + m)) = gcd (fib m) (fib n.pred * fib m + fib (n.pred + 1) * fib (m + 1)) := by
      rw [fib_add n.pred _]
      ring_nf _ = gcd (fib m) (fib (n.pred + 1) * fib (m + 1)) := by
      rw [add_commₓ, gcd_add_mul_right_right (fib m) _ (fib n.pred)]_ = gcd (fib m) (fib (n.pred + 1)) :=
      coprime.gcd_mul_right_cancel_right (fib (n.pred + 1)) (coprime.symm (fib_coprime_fib_succ m))

theorem gcd_fib_add_mul_self (m n : ℕ) : ∀ k, gcdₓ (fib m) (fib (n + k * m)) = gcdₓ (fib m) (fib n)
  | 0 => by
    simp
  | k + 1 => by
    rw [← gcd_fib_add_mul_self k, add_mulₓ, ← add_assocₓ, one_mulₓ, gcd_fib_add_self _ _]

/-- `fib n` is a strong divisibility sequence,
  see https://proofwiki.org/wiki/GCD_of_Fibonacci_Numbers -/
theorem fib_gcd (m n : ℕ) : fib (gcdₓ m n) = gcdₓ (fib m) (fib n) := by
  wlog h : m ≤ n using n m, m n
  exact le_totalₓ m n
  · apply gcd.induction m n
    · simp
      
    intro m n mpos h
    rw [← gcd_rec m n] at h
    conv_rhs => rw [← mod_add_div' n m]
    rwa [gcd_fib_add_mul_self m (n % m) (n / m), gcd_comm (fib m) _]
    
  rwa [gcd_comm, gcd_comm (fib m)]

theorem fib_dvd (m n : ℕ) (h : m ∣ n) : fib m ∣ fib n := by
  rwa [gcd_eq_left_iff_dvd, ← fib_gcd, gcd_eq_left_iff_dvd.mp]

theorem fib_succ_eq_sum_choose : ∀ n : ℕ, fib (n + 1) = ∑ p in Finset.Nat.antidiagonal n, choose p.1 p.2 :=
  twoStepInduction rfl rfl fun n h1 h2 => by
    rw [fib_add_two, h1, h2, Finset.Nat.antidiagonal_succ_succ', Finset.Nat.antidiagonal_succ']
    simp [choose_succ_succ, Finset.sum_add_distrib, add_left_commₓ]

end Nat

