/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Benjamin Davidson
-/
import Mathbin.Data.Nat.Modeq
import Mathbin.Data.Nat.Prime
import Mathbin.Algebra.Parity

/-!
# Parity of natural numbers

This file contains theorems about the `even` and `odd` predicates on the natural numbers.

## Tags

even, odd
-/


namespace Nat

variable {m n : ℕ}

@[simp]
theorem mod_two_ne_one : ¬n % 2 = 1 ↔ n % 2 = 0 := by cases' mod_two_eq_zero_or_one n with h h <;> simp [h]

@[simp]
theorem mod_two_ne_zero : ¬n % 2 = 0 ↔ n % 2 = 1 := by cases' mod_two_eq_zero_or_one n with h h <;> simp [h]

theorem even_iff : Even n ↔ n % 2 = 0 :=
  ⟨fun ⟨m, hm⟩ => by simp [← two_mul, hm], fun h => ⟨n / 2, (mod_add_div n 2).symm.trans (by simp [← two_mul, h])⟩⟩

theorem odd_iff : Odd n ↔ n % 2 = 1 :=
  ⟨fun ⟨m, hm⟩ => by norm_num [hm, add_mod] , fun h => ⟨n / 2, (mod_add_div n 2).symm.trans (by rw [h, add_comm])⟩⟩

theorem not_even_iff : ¬Even n ↔ n % 2 = 1 := by rw [even_iff, mod_two_ne_zero]

theorem not_odd_iff : ¬Odd n ↔ n % 2 = 0 := by rw [odd_iff, mod_two_ne_one]

theorem even_iff_not_odd : Even n ↔ ¬Odd n := by rw [not_odd_iff, even_iff]

@[simp]
theorem odd_iff_not_even : Odd n ↔ ¬Even n := by rw [not_even_iff, odd_iff]

theorem isComplEvenOdd : IsCompl { n : ℕ | Even n } { n | Odd n } := by
  simp only [← Set.compl_set_of, isComplCompl, odd_iff_not_even]

theorem even_or_odd (n : ℕ) : Even n ∨ Odd n :=
  Or.imp_right odd_iff_not_even.2 <| em <| Even n

theorem even_or_odd' (n : ℕ) : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := by
  simpa only [← two_mul, exists_or_distrib, ← Odd, ← Even] using even_or_odd n

theorem even_xor_odd (n : ℕ) : Xor' (Even n) (Odd n) := by
  cases' even_or_odd n with h
  · exact Or.inl ⟨h, even_iff_not_odd.mp h⟩
    
  · exact Or.inr ⟨h, odd_iff_not_even.mp h⟩
    

theorem even_xor_odd' (n : ℕ) : ∃ k, Xor' (n = 2 * k) (n = 2 * k + 1) := by
  rcases even_or_odd n with (⟨k, rfl⟩ | ⟨k, rfl⟩) <;> use k
  · simpa only [← two_mul, Xor', true_and_iff, eq_self_iff_true, not_true, or_false_iff, and_false_iff] using
      (succ_ne_self (2 * k)).symm
    
  · simp only [Xor', add_right_eq_self, false_or_iff, eq_self_iff_true, not_true, not_false_iff, one_ne_zero,
      and_self_iff]
    

@[simp]
theorem two_dvd_ne_zero : ¬2 ∣ n ↔ n % 2 = 1 :=
  even_iff_two_dvd.symm.Not.trans not_even_iff

instance : DecidablePred (Even : ℕ → Prop) := fun n => decidableOfIff _ even_iff.symm

instance : DecidablePred (Odd : ℕ → Prop) := fun n => decidableOfIff _ odd_iff_not_even.symm

/- failed to parenthesize: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
[PrettyPrinter.parenthesize.input] (Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr
     [(Command.docComment "/--" "Simp attribute for lemmas about `even` -/")]
     "register_simp_attr"
     `parity_simps)-/-- failed to format: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
/-- Simp attribute for lemmas about `even` -/ register_simp_attr parity_simps

@[simp]
theorem not_even_one : ¬Even 1 := by rw [even_iff] <;> norm_num

@[parity_simps]
theorem even_add : Even (m + n) ↔ (Even m ↔ Even n) := by
  cases' mod_two_eq_zero_or_one m with h₁ h₁ <;>
    cases' mod_two_eq_zero_or_one n with h₂ h₂ <;> simp [even_iff, h₁, h₂, Nat.add_mod] <;> norm_num

theorem even_add' : Even (m + n) ↔ (Odd m ↔ Odd n) := by rw [even_add, even_iff_not_odd, even_iff_not_odd, not_iff_not]

@[parity_simps]
theorem even_add_one : Even (n + 1) ↔ ¬Even n := by simp [even_add]

@[simp]
theorem not_even_bit1 (n : ℕ) : ¬Even (bit1 n) := by simp [bit1, parity_simps]

theorem two_not_dvd_two_mul_add_one (n : ℕ) : ¬2 ∣ 2 * n + 1 := by simp [add_mod]

theorem two_not_dvd_two_mul_sub_one : ∀ {n} (w : 0 < n), ¬2 ∣ 2 * n - 1
  | n + 1, _ => two_not_dvd_two_mul_add_one n

@[parity_simps]
theorem even_sub (h : n ≤ m) : Even (m - n) ↔ (Even m ↔ Even n) := by
  conv =>
  rhs
  rw [← tsub_add_cancel_of_le h, even_add]
  by_cases h:Even n <;> simp [h]

theorem even_sub' (h : n ≤ m) : Even (m - n) ↔ (Odd m ↔ Odd n) := by
  rw [even_sub h, even_iff_not_odd, even_iff_not_odd, not_iff_not]

theorem Odd.sub_odd (hm : Odd m) (hn : Odd n) : Even (m - n) :=
  (le_total n m).elim (fun h => by simp only [even_sub' h, *]) fun h => by
    simp only [tsub_eq_zero_iff_le.mpr h, even_zero]

@[parity_simps]
theorem even_mul : Even (m * n) ↔ Even m ∨ Even n := by
  cases' mod_two_eq_zero_or_one m with h₁ h₁ <;>
    cases' mod_two_eq_zero_or_one n with h₂ h₂ <;> simp [even_iff, h₁, h₂, Nat.mul_mod] <;> norm_num

theorem odd_mul : Odd (m * n) ↔ Odd m ∧ Odd n := by simp [not_or_distrib, parity_simps]

theorem Odd.of_mul_left (h : Odd (m * n)) : Odd m :=
  (odd_mul.mp h).1

theorem Odd.of_mul_right (h : Odd (m * n)) : Odd n :=
  (odd_mul.mp h).2

/-- If `m` and `n` are natural numbers, then the natural number `m^n` is even
if and only if `m` is even and `n` is positive. -/
@[parity_simps]
theorem even_pow : Even (m ^ n) ↔ Even m ∧ n ≠ 0 := by
  induction' n with n ih <;> simp [*, pow_succ', even_mul]
  tauto

theorem even_pow' (h : n ≠ 0) : Even (m ^ n) ↔ Even m :=
  even_pow.trans <| and_iff_left h

theorem even_div : Even (m / n) ↔ m % (2 * n) / n = 0 := by
  rw [even_iff_two_dvd, dvd_iff_mod_eq_zero, Nat.div_mod_eq_mod_mul_div, mul_comm]

@[parity_simps]
theorem odd_add : Odd (m + n) ↔ (Odd m ↔ Even n) := by rw [odd_iff_not_even, even_add, not_iff, odd_iff_not_even]

theorem odd_add' : Odd (m + n) ↔ (Odd n ↔ Even m) := by rw [add_comm, odd_add]

theorem ne_of_odd_add (h : Odd (m + n)) : m ≠ n := fun hnot => by simpa [hnot, parity_simps] using h

@[parity_simps]
theorem odd_sub (h : n ≤ m) : Odd (m - n) ↔ (Odd m ↔ Even n) := by
  rw [odd_iff_not_even, even_sub h, not_iff, odd_iff_not_even]

theorem Odd.sub_even (h : n ≤ m) (hm : Odd m) (hn : Even n) : Odd (m - n) :=
  (odd_sub h).mpr <| iff_of_true hm hn

theorem odd_sub' (h : n ≤ m) : Odd (m - n) ↔ (Odd n ↔ Even m) := by
  rw [odd_iff_not_even, even_sub h, not_iff, not_iff_comm, odd_iff_not_even]

theorem Even.sub_odd (h : n ≤ m) (hm : Even m) (hn : Odd n) : Odd (m - n) :=
  (odd_sub' h).mpr <| iff_of_true hn hm

theorem even_mul_succ_self (n : ℕ) : Even (n * (n + 1)) := by
  rw [even_mul]
  convert n.even_or_odd
  simp [parity_simps]

theorem even_mul_self_pred (n : ℕ) : Even (n * (n - 1)) := by
  cases n
  · exact even_zero
    
  · rw [mul_comm]
    apply even_mul_succ_self
    

theorem even_sub_one_of_prime_ne_two {p : ℕ} (hp : Prime p) (hodd : p ≠ 2) : Even (p - 1) :=
  Odd.sub_odd (odd_iff.2 <| hp.eq_two_or_odd.resolve_left hodd) (odd_iff.2 rfl)

theorem two_mul_div_two_of_even : Even n → 2 * (n / 2) = n := fun h => Nat.mul_div_cancel_left' (even_iff_two_dvd.mp h)

theorem div_two_mul_two_of_even : Even n → n / 2 * 2 = n :=
  fun
    --nat.div_mul_cancel
    h =>
  Nat.div_mul_cancel (even_iff_two_dvd.mp h)

theorem two_mul_div_two_add_one_of_odd (h : Odd n) : 2 * (n / 2) + 1 = n := by
  rw [mul_comm]
  convert Nat.div_add_mod' n 2
  rw [odd_iff.mp h]

theorem div_two_mul_two_add_one_of_odd (h : Odd n) : n / 2 * 2 + 1 = n := by
  convert Nat.div_add_mod' n 2
  rw [odd_iff.mp h]

theorem one_add_div_two_mul_two_of_odd (h : Odd n) : 1 + n / 2 * 2 = n := by
  rw [add_comm]
  convert Nat.div_add_mod' n 2
  rw [odd_iff.mp h]

theorem bit0_div_two : bit0 n / 2 = n := by
  rw [← Nat.bit0_eq_bit0, bit0_eq_two_mul, two_mul_div_two_of_even (even_bit0 n)]

theorem bit1_div_two : bit1 n / 2 = n := by
  rw [← Nat.bit1_eq_bit1, bit1, bit0_eq_two_mul, Nat.two_mul_div_two_add_one_of_odd (odd_bit1 n)]

@[simp]
theorem bit0_div_bit0 : bit0 n / bit0 m = n / m := by rw [bit0_eq_two_mul m, ← Nat.div_div_eq_div_mul, bit0_div_two]

@[simp]
theorem bit1_div_bit0 : bit1 n / bit0 m = n / m := by rw [bit0_eq_two_mul, ← Nat.div_div_eq_div_mul, bit1_div_two]

@[simp]
theorem bit0_mod_bit0 : bit0 n % bit0 m = bit0 (n % m) := by
  rw [bit0_eq_two_mul n, bit0_eq_two_mul m, bit0_eq_two_mul (n % m), Nat.mul_mod_mul_left]

@[simp]
theorem bit1_mod_bit0 : bit1 n % bit0 m = bit1 (n % m) := by
  have h₁ := congr_arg bit1 (Nat.div_add_mod n m)
  -- `∀ m n : ℕ, bit0 m * n = bit0 (m * n)` seems to be missing...
  rw [bit1_add, bit0_eq_two_mul, ← mul_assoc, ← bit0_eq_two_mul] at h₁
  have h₂ := Nat.div_add_mod (bit1 n) (bit0 m)
  rw [bit1_div_bit0] at h₂
  exact add_left_cancel (h₂.trans h₁.symm)

-- Here are examples of how `parity_simps` can be used with `nat`.
example (m n : ℕ) (h : Even m) : ¬Even (n + 3) ↔ Even (m ^ 2 + m + n) := by simp [*, (by decide : ¬2 = 0), parity_simps]

example : ¬Even 25394535 := by simp

end Nat

open Nat

namespace Function

namespace Involutive

variable {α : Type _} {f : α → α} {n : ℕ}

theorem iterate_bit0 (hf : Involutive f) (n : ℕ) : f^[bit0 n] = id := by
  rw [bit0, ← two_mul, iterate_mul, involutive_iff_iter_2_eq_id.1 hf, iterate_id]

theorem iterate_bit1 (hf : Involutive f) (n : ℕ) : f^[bit1 n] = f := by
  rw [bit1, iterate_succ, hf.iterate_bit0, comp.left_id]

theorem iterate_even (hf : Involutive f) (hn : Even n) : f^[n] = id :=
  let ⟨m, hm⟩ := hn
  hm.symm ▸ hf.iterate_bit0 m

theorem iterate_odd (hf : Involutive f) (hn : Odd n) : f^[n] = f :=
  let ⟨m, hm⟩ := odd_iff_exists_bit1.mp hn
  hm.symm ▸ hf.iterate_bit1 m

theorem iterate_eq_self (hf : Involutive f) (hne : f ≠ id) : f^[n] = f ↔ Odd n :=
  ⟨fun H => odd_iff_not_even.2 fun hn => hne <| by rwa [hf.iterate_even hn, eq_comm] at H, hf.iterate_odd⟩

theorem iterate_eq_id (hf : Involutive f) (hne : f ≠ id) : f^[n] = id ↔ Even n :=
  ⟨fun H => even_iff_not_odd.2 fun hn => hne <| by rwa [hf.iterate_odd hn] at H, hf.iterate_even⟩

end Involutive

end Function

variable {R : Type _} [Monoid R] [HasDistribNeg R] {n : ℕ}

theorem neg_one_pow_eq_one_iff_even (h : (-1 : R) ≠ 1) : (-1 : R) ^ n = 1 ↔ Even n :=
  ⟨fun h' => of_not_not fun hn => h <| (Odd.neg_one_pow <| odd_iff_not_even.mpr hn).symm.trans h', Even.neg_one_pow⟩

/-- If `a` is even, then `n` is odd iff `n % a` is odd. -/
theorem Odd.mod_even_iff {n a : ℕ} (ha : Even a) : Odd (n % a) ↔ Odd n :=
  ((even_sub' <| mod_le n a).mp <| even_iff_two_dvd.mpr <| (even_iff_two_dvd.mp ha).trans <| dvd_sub_mod n).symm

/-- If `a` is even, then `n` is even iff `n % a` is even. -/
theorem Even.mod_even_iff {n a : ℕ} (ha : Even a) : Even (n % a) ↔ Even n :=
  ((even_sub <| mod_le n a).mp <| even_iff_two_dvd.mpr <| (even_iff_two_dvd.mp ha).trans <| dvd_sub_mod n).symm

/-- If `n` is odd and `a` is even, then `n % a` is odd. -/
theorem Odd.mod_even {n a : ℕ} (hn : Odd n) (ha : Even a) : Odd (n % a) :=
  (Odd.mod_even_iff ha).mpr hn

/-- If `n` is even and `a` is even, then `n % a` is even. -/
theorem Even.mod_even {n a : ℕ} (hn : Even n) (ha : Even a) : Even (n % a) :=
  (Even.mod_even_iff ha).mpr hn

/-- `2` is not a prime factor of an odd natural number. -/
theorem Odd.factors_ne_two {n p : ℕ} (hn : Odd n) (hp : p ∈ n.factors) : p ≠ 2 := by
  rintro rfl
  exact two_dvd_ne_zero.mpr (odd_iff.mp hn) (dvd_of_mem_factors hp)

