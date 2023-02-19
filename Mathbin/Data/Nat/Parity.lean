/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Benjamin Davidson

! This file was ported from Lean 3 source module data.nat.parity
! leanprover-community/mathlib commit e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Modeq
import Mathbin.Algebra.Parity

/-!
# Parity of natural numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains theorems about the `even` and `odd` predicates on the natural numbers.

## Tags

even, odd
-/


namespace Nat

variable {m n : ℕ}

#print Nat.mod_two_ne_one /-
@[simp]
theorem mod_two_ne_one : ¬n % 2 = 1 ↔ n % 2 = 0 := by
  cases' mod_two_eq_zero_or_one n with h h <;> simp [h]
#align nat.mod_two_ne_one Nat.mod_two_ne_one
-/

#print Nat.mod_two_ne_zero /-
@[simp]
theorem mod_two_ne_zero : ¬n % 2 = 0 ↔ n % 2 = 1 := by
  cases' mod_two_eq_zero_or_one n with h h <;> simp [h]
#align nat.mod_two_ne_zero Nat.mod_two_ne_zero
-/

#print Nat.even_iff /-
theorem even_iff : Even n ↔ n % 2 = 0 :=
  ⟨fun ⟨m, hm⟩ => by simp [← two_mul, hm], fun h =>
    ⟨n / 2, (mod_add_div n 2).symm.trans (by simp [← two_mul, h])⟩⟩
#align nat.even_iff Nat.even_iff
-/

#print Nat.odd_iff /-
theorem odd_iff : Odd n ↔ n % 2 = 1 :=
  ⟨fun ⟨m, hm⟩ => by norm_num [hm, add_mod] , fun h =>
    ⟨n / 2, (mod_add_div n 2).symm.trans (by rw [h, add_comm])⟩⟩
#align nat.odd_iff Nat.odd_iff
-/

#print Nat.not_even_iff /-
theorem not_even_iff : ¬Even n ↔ n % 2 = 1 := by rw [even_iff, mod_two_ne_zero]
#align nat.not_even_iff Nat.not_even_iff
-/

#print Nat.not_odd_iff /-
theorem not_odd_iff : ¬Odd n ↔ n % 2 = 0 := by rw [odd_iff, mod_two_ne_one]
#align nat.not_odd_iff Nat.not_odd_iff
-/

#print Nat.even_iff_not_odd /-
theorem even_iff_not_odd : Even n ↔ ¬Odd n := by rw [not_odd_iff, even_iff]
#align nat.even_iff_not_odd Nat.even_iff_not_odd
-/

#print Nat.odd_iff_not_even /-
@[simp]
theorem odd_iff_not_even : Odd n ↔ ¬Even n := by rw [not_even_iff, odd_iff]
#align nat.odd_iff_not_even Nat.odd_iff_not_even
-/

/- warning: nat.is_compl_even_odd -> Nat.isCompl_even_odd is a dubious translation:
lean 3 declaration is
  IsCompl.{0} (Set.{0} Nat) (SemilatticeInf.toPartialOrder.{0} (Set.{0} Nat) (Lattice.toSemilatticeInf.{0} (Set.{0} Nat) (GeneralizedCoheytingAlgebra.toLattice.{0} (Set.{0} Nat) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{0} (Set.{0} Nat) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} (Set.{0} Nat) (Set.booleanAlgebra.{0} Nat)))))) (BooleanAlgebra.toBoundedOrder.{0} (Set.{0} Nat) (Set.booleanAlgebra.{0} Nat)) (setOf.{0} Nat (fun (n : Nat) => Even.{0} Nat Nat.hasAdd n)) (setOf.{0} Nat (fun (n : Nat) => Odd.{0} Nat Nat.semiring n))
but is expected to have type
  IsCompl.{0} (Set.{0} Nat) (SemilatticeInf.toPartialOrder.{0} (Set.{0} Nat) (Lattice.toSemilatticeInf.{0} (Set.{0} Nat) (GeneralizedCoheytingAlgebra.toLattice.{0} (Set.{0} Nat) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{0} (Set.{0} Nat) (BiheytingAlgebra.toCoheytingAlgebra.{0} (Set.{0} Nat) (BooleanAlgebra.toBiheytingAlgebra.{0} (Set.{0} Nat) (Set.instBooleanAlgebraSet.{0} Nat))))))) (BooleanAlgebra.toBoundedOrder.{0} (Set.{0} Nat) (Set.instBooleanAlgebraSet.{0} Nat)) (setOf.{0} Nat (fun (n : Nat) => Even.{0} Nat instAddNat n)) (setOf.{0} Nat (fun (n : Nat) => Odd.{0} Nat Nat.semiring n))
Case conversion may be inaccurate. Consider using '#align nat.is_compl_even_odd Nat.isCompl_even_oddₓ'. -/
theorem isCompl_even_odd : IsCompl { n : ℕ | Even n } { n | Odd n } := by
  simp only [← Set.compl_setOf, isCompl_compl, odd_iff_not_even]
#align nat.is_compl_even_odd Nat.isCompl_even_odd

#print Nat.even_or_odd /-
theorem even_or_odd (n : ℕ) : Even n ∨ Odd n :=
  Or.imp_right odd_iff_not_even.2 <| em <| Even n
#align nat.even_or_odd Nat.even_or_odd
-/

#print Nat.even_or_odd' /-
theorem even_or_odd' (n : ℕ) : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := by
  simpa only [← two_mul, exists_or, ← Odd, ← Even] using even_or_odd n
#align nat.even_or_odd' Nat.even_or_odd'
-/

#print Nat.even_xor_odd /-
theorem even_xor_odd (n : ℕ) : Xor' (Even n) (Odd n) :=
  by
  cases' even_or_odd n with h
  · exact Or.inl ⟨h, even_iff_not_odd.mp h⟩
  · exact Or.inr ⟨h, odd_iff_not_even.mp h⟩
#align nat.even_xor_odd Nat.even_xor_odd
-/

#print Nat.even_xor_odd' /-
theorem even_xor_odd' (n : ℕ) : ∃ k, Xor' (n = 2 * k) (n = 2 * k + 1) :=
  by
  rcases even_or_odd n with (⟨k, rfl⟩ | ⟨k, rfl⟩) <;> use k
  ·
    simpa only [← two_mul, Xor', true_and_iff, eq_self_iff_true, not_true, or_false_iff,
      and_false_iff] using (succ_ne_self (2 * k)).symm
  ·
    simp only [Xor', add_right_eq_self, false_or_iff, eq_self_iff_true, not_true, not_false_iff,
      one_ne_zero, and_self_iff]
#align nat.even_xor_odd' Nat.even_xor_odd'
-/

#print Nat.two_dvd_ne_zero /-
@[simp]
theorem two_dvd_ne_zero : ¬2 ∣ n ↔ n % 2 = 1 :=
  even_iff_two_dvd.symm.Not.trans not_even_iff
#align nat.two_dvd_ne_zero Nat.two_dvd_ne_zero
-/

instance : DecidablePred (Even : ℕ → Prop) := fun n => decidable_of_iff _ even_iff.symm

instance : DecidablePred (Odd : ℕ → Prop) := fun n => decidable_of_iff _ odd_iff_not_even.symm

#print Nat.mod_two_add_add_odd_mod_two /-
theorem mod_two_add_add_odd_mod_two (m : ℕ) {n : ℕ} (hn : Odd n) : m % 2 + (m + n) % 2 = 1 :=
  (even_or_odd m).elim (fun hm => by rw [even_iff.1 hm, odd_iff.1 (hm.add_odd hn)]) fun hm => by
    rw [odd_iff.1 hm, even_iff.1 (hm.add_odd hn)]
#align nat.mod_two_add_add_odd_mod_two Nat.mod_two_add_add_odd_mod_two
-/

#print Nat.mod_two_add_succ_mod_two /-
@[simp]
theorem mod_two_add_succ_mod_two (m : ℕ) : m % 2 + (m + 1) % 2 = 1 :=
  mod_two_add_add_odd_mod_two m odd_one
#align nat.mod_two_add_succ_mod_two Nat.mod_two_add_succ_mod_two
-/

#print Nat.succ_mod_two_add_mod_two /-
@[simp]
theorem succ_mod_two_add_mod_two (m : ℕ) : (m + 1) % 2 + m % 2 = 1 := by
  rw [add_comm, mod_two_add_succ_mod_two]
#align nat.succ_mod_two_add_mod_two Nat.succ_mod_two_add_mod_two
-/

/- failed to parenthesize: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
[PrettyPrinter.parenthesize.input] (Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr
     [(Command.docComment "/--" "Simp attribute for lemmas about `even` -/")]
     "register_simp_attr"
     `parity_simps)-/-- failed to format: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
/-- Simp attribute for lemmas about `even` -/ register_simp_attr parity_simps

#print Nat.not_even_one /-
@[simp]
theorem not_even_one : ¬Even 1 := by rw [even_iff] <;> norm_num
#align nat.not_even_one Nat.not_even_one
-/

#print Nat.even_add /-
@[parity_simps]
theorem even_add : Even (m + n) ↔ (Even m ↔ Even n) := by
  cases' mod_two_eq_zero_or_one m with h₁ h₁ <;> cases' mod_two_eq_zero_or_one n with h₂ h₂ <;>
      simp [even_iff, h₁, h₂, Nat.add_mod] <;>
    norm_num
#align nat.even_add Nat.even_add
-/

#print Nat.even_add' /-
theorem even_add' : Even (m + n) ↔ (Odd m ↔ Odd n) := by
  rw [even_add, even_iff_not_odd, even_iff_not_odd, not_iff_not]
#align nat.even_add' Nat.even_add'
-/

#print Nat.even_add_one /-
@[parity_simps]
theorem even_add_one : Even (n + 1) ↔ ¬Even n := by simp [even_add]
#align nat.even_add_one Nat.even_add_one
-/

#print Nat.not_even_bit1 /-
@[simp]
theorem not_even_bit1 (n : ℕ) : ¬Even (bit1 n) := by simp [bit1, parity_simps]
#align nat.not_even_bit1 Nat.not_even_bit1
-/

#print Nat.two_not_dvd_two_mul_add_one /-
theorem two_not_dvd_two_mul_add_one (n : ℕ) : ¬2 ∣ 2 * n + 1 := by simp [add_mod]
#align nat.two_not_dvd_two_mul_add_one Nat.two_not_dvd_two_mul_add_one
-/

#print Nat.two_not_dvd_two_mul_sub_one /-
theorem two_not_dvd_two_mul_sub_one : ∀ {n} (w : 0 < n), ¬2 ∣ 2 * n - 1
  | n + 1, _ => two_not_dvd_two_mul_add_one n
#align nat.two_not_dvd_two_mul_sub_one Nat.two_not_dvd_two_mul_sub_one
-/

#print Nat.even_sub /-
@[parity_simps]
theorem even_sub (h : n ≤ m) : Even (m - n) ↔ (Even m ↔ Even n) :=
  by
  conv =>
    rhs
    rw [← tsub_add_cancel_of_le h, even_add]
  by_cases h : Even n <;> simp [h]
#align nat.even_sub Nat.even_sub
-/

#print Nat.even_sub' /-
theorem even_sub' (h : n ≤ m) : Even (m - n) ↔ (Odd m ↔ Odd n) := by
  rw [even_sub h, even_iff_not_odd, even_iff_not_odd, not_iff_not]
#align nat.even_sub' Nat.even_sub'
-/

#print Nat.Odd.sub_odd /-
theorem Odd.sub_odd (hm : Odd m) (hn : Odd n) : Even (m - n) :=
  (le_total n m).elim (fun h => by simp only [even_sub' h, *]) fun h => by
    simp only [tsub_eq_zero_iff_le.mpr h, even_zero]
#align nat.odd.sub_odd Nat.Odd.sub_odd
-/

#print Nat.even_mul /-
@[parity_simps]
theorem even_mul : Even (m * n) ↔ Even m ∨ Even n := by
  cases' mod_two_eq_zero_or_one m with h₁ h₁ <;> cases' mod_two_eq_zero_or_one n with h₂ h₂ <;>
      simp [even_iff, h₁, h₂, Nat.mul_mod] <;>
    norm_num
#align nat.even_mul Nat.even_mul
-/

#print Nat.odd_mul /-
theorem odd_mul : Odd (m * n) ↔ Odd m ∧ Odd n := by simp [not_or, parity_simps]
#align nat.odd_mul Nat.odd_mul
-/

#print Nat.Odd.of_mul_left /-
theorem Odd.of_mul_left (h : Odd (m * n)) : Odd m :=
  (odd_mul.mp h).1
#align nat.odd.of_mul_left Nat.Odd.of_mul_left
-/

#print Nat.Odd.of_mul_right /-
theorem Odd.of_mul_right (h : Odd (m * n)) : Odd n :=
  (odd_mul.mp h).2
#align nat.odd.of_mul_right Nat.Odd.of_mul_right
-/

#print Nat.even_pow /-
/-- If `m` and `n` are natural numbers, then the natural number `m^n` is even
if and only if `m` is even and `n` is positive. -/
@[parity_simps]
theorem even_pow : Even (m ^ n) ↔ Even m ∧ n ≠ 0 :=
  by
  induction' n with n ih <;> simp [*, pow_succ', even_mul]
  tauto
#align nat.even_pow Nat.even_pow
-/

#print Nat.even_pow' /-
theorem even_pow' (h : n ≠ 0) : Even (m ^ n) ↔ Even m :=
  even_pow.trans <| and_iff_left h
#align nat.even_pow' Nat.even_pow'
-/

#print Nat.even_div /-
theorem even_div : Even (m / n) ↔ m % (2 * n) / n = 0 := by
  rw [even_iff_two_dvd, dvd_iff_mod_eq_zero, Nat.div_mod_eq_mod_mul_div, mul_comm]
#align nat.even_div Nat.even_div
-/

#print Nat.odd_add /-
@[parity_simps]
theorem odd_add : Odd (m + n) ↔ (Odd m ↔ Even n) := by
  rw [odd_iff_not_even, even_add, not_iff, odd_iff_not_even]
#align nat.odd_add Nat.odd_add
-/

#print Nat.odd_add' /-
theorem odd_add' : Odd (m + n) ↔ (Odd n ↔ Even m) := by rw [add_comm, odd_add]
#align nat.odd_add' Nat.odd_add'
-/

#print Nat.ne_of_odd_add /-
theorem ne_of_odd_add (h : Odd (m + n)) : m ≠ n := fun hnot => by simpa [hnot, parity_simps] using h
#align nat.ne_of_odd_add Nat.ne_of_odd_add
-/

#print Nat.odd_sub /-
@[parity_simps]
theorem odd_sub (h : n ≤ m) : Odd (m - n) ↔ (Odd m ↔ Even n) := by
  rw [odd_iff_not_even, even_sub h, not_iff, odd_iff_not_even]
#align nat.odd_sub Nat.odd_sub
-/

#print Nat.Odd.sub_even /-
theorem Odd.sub_even (h : n ≤ m) (hm : Odd m) (hn : Even n) : Odd (m - n) :=
  (odd_sub h).mpr <| iff_of_true hm hn
#align nat.odd.sub_even Nat.Odd.sub_even
-/

#print Nat.odd_sub' /-
theorem odd_sub' (h : n ≤ m) : Odd (m - n) ↔ (Odd n ↔ Even m) := by
  rw [odd_iff_not_even, even_sub h, not_iff, not_iff_comm, odd_iff_not_even]
#align nat.odd_sub' Nat.odd_sub'
-/

#print Nat.Even.sub_odd /-
theorem Even.sub_odd (h : n ≤ m) (hm : Even m) (hn : Odd n) : Odd (m - n) :=
  (odd_sub' h).mpr <| iff_of_true hn hm
#align nat.even.sub_odd Nat.Even.sub_odd
-/

#print Nat.even_mul_succ_self /-
theorem even_mul_succ_self (n : ℕ) : Even (n * (n + 1)) :=
  by
  rw [even_mul]
  convert n.even_or_odd
  simp [parity_simps]
#align nat.even_mul_succ_self Nat.even_mul_succ_self
-/

#print Nat.even_mul_self_pred /-
theorem even_mul_self_pred (n : ℕ) : Even (n * (n - 1)) :=
  by
  cases n
  · exact even_zero
  · rw [mul_comm]
    apply even_mul_succ_self
#align nat.even_mul_self_pred Nat.even_mul_self_pred
-/

#print Nat.two_mul_div_two_of_even /-
theorem two_mul_div_two_of_even : Even n → 2 * (n / 2) = n := fun h =>
  Nat.mul_div_cancel_left' (even_iff_two_dvd.mp h)
#align nat.two_mul_div_two_of_even Nat.two_mul_div_two_of_even
-/

#print Nat.div_two_mul_two_of_even /-
theorem div_two_mul_two_of_even : Even n → n / 2 * 2 = n := fun h =>
  Nat.div_mul_cancel (even_iff_two_dvd.mp h)
#align nat.div_two_mul_two_of_even Nat.div_two_mul_two_of_even
-/

#print Nat.two_mul_div_two_add_one_of_odd /-
theorem two_mul_div_two_add_one_of_odd (h : Odd n) : 2 * (n / 2) + 1 = n :=
  by
  rw [mul_comm]
  convert Nat.div_add_mod' n 2
  rw [odd_iff.mp h]
#align nat.two_mul_div_two_add_one_of_odd Nat.two_mul_div_two_add_one_of_odd
-/

#print Nat.div_two_mul_two_add_one_of_odd /-
theorem div_two_mul_two_add_one_of_odd (h : Odd n) : n / 2 * 2 + 1 = n :=
  by
  convert Nat.div_add_mod' n 2
  rw [odd_iff.mp h]
#align nat.div_two_mul_two_add_one_of_odd Nat.div_two_mul_two_add_one_of_odd
-/

#print Nat.one_add_div_two_mul_two_of_odd /-
theorem one_add_div_two_mul_two_of_odd (h : Odd n) : 1 + n / 2 * 2 = n :=
  by
  rw [add_comm]
  convert Nat.div_add_mod' n 2
  rw [odd_iff.mp h]
#align nat.one_add_div_two_mul_two_of_odd Nat.one_add_div_two_mul_two_of_odd
-/

#print Nat.bit0_div_two /-
theorem bit0_div_two : bit0 n / 2 = n := by
  rw [← Nat.bit0_eq_bit0, bit0_eq_two_mul, two_mul_div_two_of_even (even_bit0 n)]
#align nat.bit0_div_two Nat.bit0_div_two
-/

#print Nat.bit1_div_two /-
theorem bit1_div_two : bit1 n / 2 = n := by
  rw [← Nat.bit1_eq_bit1, bit1, bit0_eq_two_mul, Nat.two_mul_div_two_add_one_of_odd (odd_bit1 n)]
#align nat.bit1_div_two Nat.bit1_div_two
-/

#print Nat.bit0_div_bit0 /-
@[simp]
theorem bit0_div_bit0 : bit0 n / bit0 m = n / m := by
  rw [bit0_eq_two_mul m, ← Nat.div_div_eq_div_mul, bit0_div_two]
#align nat.bit0_div_bit0 Nat.bit0_div_bit0
-/

#print Nat.bit1_div_bit0 /-
@[simp]
theorem bit1_div_bit0 : bit1 n / bit0 m = n / m := by
  rw [bit0_eq_two_mul, ← Nat.div_div_eq_div_mul, bit1_div_two]
#align nat.bit1_div_bit0 Nat.bit1_div_bit0
-/

#print Nat.bit0_mod_bit0 /-
@[simp]
theorem bit0_mod_bit0 : bit0 n % bit0 m = bit0 (n % m) := by
  rw [bit0_eq_two_mul n, bit0_eq_two_mul m, bit0_eq_two_mul (n % m), Nat.mul_mod_mul_left]
#align nat.bit0_mod_bit0 Nat.bit0_mod_bit0
-/

#print Nat.bit1_mod_bit0 /-
@[simp]
theorem bit1_mod_bit0 : bit1 n % bit0 m = bit1 (n % m) :=
  by
  have h₁ := congr_arg bit1 (Nat.div_add_mod n m)
  -- `∀ m n : ℕ, bit0 m * n = bit0 (m * n)` seems to be missing...
  rw [bit1_add, bit0_eq_two_mul, ← mul_assoc, ← bit0_eq_two_mul] at h₁
  have h₂ := Nat.div_add_mod (bit1 n) (bit0 m)
  rw [bit1_div_bit0] at h₂
  exact add_left_cancel (h₂.trans h₁.symm)
#align nat.bit1_mod_bit0 Nat.bit1_mod_bit0
-/

-- Here are examples of how `parity_simps` can be used with `nat`.
example (m n : ℕ) (h : Even m) : ¬Even (n + 3) ↔ Even (m ^ 2 + m + n) := by
  simp [*, (by decide : ¬2 = 0), parity_simps]

example : ¬Even 25394535 := by simp

end Nat

open Nat

namespace Function

namespace Involutive

variable {α : Type _} {f : α → α} {n : ℕ}

#print Function.Involutive.iterate_bit0 /-
theorem iterate_bit0 (hf : Involutive f) (n : ℕ) : f^[bit0 n] = id := by
  rw [bit0, ← two_mul, iterate_mul, involutive_iff_iter_2_eq_id.1 hf, iterate_id]
#align function.involutive.iterate_bit0 Function.Involutive.iterate_bit0
-/

#print Function.Involutive.iterate_bit1 /-
theorem iterate_bit1 (hf : Involutive f) (n : ℕ) : f^[bit1 n] = f := by
  rw [bit1, iterate_succ, hf.iterate_bit0, comp.left_id]
#align function.involutive.iterate_bit1 Function.Involutive.iterate_bit1
-/

#print Function.Involutive.iterate_even /-
theorem iterate_even (hf : Involutive f) (hn : Even n) : f^[n] = id :=
  let ⟨m, hm⟩ := hn
  hm.symm ▸ hf.iterate_bit0 m
#align function.involutive.iterate_even Function.Involutive.iterate_even
-/

#print Function.Involutive.iterate_odd /-
theorem iterate_odd (hf : Involutive f) (hn : Odd n) : f^[n] = f :=
  let ⟨m, hm⟩ := odd_iff_exists_bit1.mp hn
  hm.symm ▸ hf.iterate_bit1 m
#align function.involutive.iterate_odd Function.Involutive.iterate_odd
-/

#print Function.Involutive.iterate_eq_self /-
theorem iterate_eq_self (hf : Involutive f) (hne : f ≠ id) : f^[n] = f ↔ Odd n :=
  ⟨fun H => odd_iff_not_even.2 fun hn => hne <| by rwa [hf.iterate_even hn, eq_comm] at H,
    hf.iterate_odd⟩
#align function.involutive.iterate_eq_self Function.Involutive.iterate_eq_self
-/

#print Function.Involutive.iterate_eq_id /-
theorem iterate_eq_id (hf : Involutive f) (hne : f ≠ id) : f^[n] = id ↔ Even n :=
  ⟨fun H => even_iff_not_odd.2 fun hn => hne <| by rwa [hf.iterate_odd hn] at H, hf.iterate_even⟩
#align function.involutive.iterate_eq_id Function.Involutive.iterate_eq_id
-/

end Involutive

end Function

variable {R : Type _} [Monoid R] [HasDistribNeg R] {n : ℕ}

/- warning: neg_one_pow_eq_one_iff_even -> neg_one_pow_eq_one_iff_even is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Monoid.{u1} R] [_inst_2 : HasDistribNeg.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1))] {n : Nat}, (Ne.{succ u1} R (Neg.neg.{u1} R (InvolutiveNeg.toHasNeg.{u1} R (HasDistribNeg.toHasInvolutiveNeg.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) _inst_2)) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (MulOneClass.toHasOne.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)))))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (MulOneClass.toHasOne.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)))))) -> (Iff (Eq.{succ u1} R (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R _inst_1)) (Neg.neg.{u1} R (InvolutiveNeg.toHasNeg.{u1} R (HasDistribNeg.toHasInvolutiveNeg.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) _inst_2)) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (MulOneClass.toHasOne.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)))))) n) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (MulOneClass.toHasOne.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)))))) (Even.{0} Nat Nat.hasAdd n))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Monoid.{u1} R] [_inst_2 : HasDistribNeg.{u1} R (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1))] {n : Nat}, (Ne.{succ u1} R (Neg.neg.{u1} R (InvolutiveNeg.toNeg.{u1} R (HasDistribNeg.toInvolutiveNeg.{u1} R (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) _inst_2)) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Monoid.toOne.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Monoid.toOne.{u1} R _inst_1)))) -> (Iff (Eq.{succ u1} R (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R _inst_1)) (Neg.neg.{u1} R (InvolutiveNeg.toNeg.{u1} R (HasDistribNeg.toInvolutiveNeg.{u1} R (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) _inst_2)) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Monoid.toOne.{u1} R _inst_1)))) n) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Monoid.toOne.{u1} R _inst_1)))) (Even.{0} Nat instAddNat n))
Case conversion may be inaccurate. Consider using '#align neg_one_pow_eq_one_iff_even neg_one_pow_eq_one_iff_evenₓ'. -/
theorem neg_one_pow_eq_one_iff_even (h : (-1 : R) ≠ 1) : (-1 : R) ^ n = 1 ↔ Even n :=
  ⟨fun h' => of_not_not fun hn => h <| (Odd.neg_one_pow <| odd_iff_not_even.mpr hn).symm.trans h',
    Even.neg_one_pow⟩
#align neg_one_pow_eq_one_iff_even neg_one_pow_eq_one_iff_even

#print Odd.mod_even_iff /-
/-- If `a` is even, then `n` is odd iff `n % a` is odd. -/
theorem Odd.mod_even_iff {n a : ℕ} (ha : Even a) : Odd (n % a) ↔ Odd n :=
  ((even_sub' <| mod_le n a).mp <|
      even_iff_two_dvd.mpr <| (even_iff_two_dvd.mp ha).trans <| dvd_sub_mod n).symm
#align odd.mod_even_iff Odd.mod_even_iff
-/

#print Even.mod_even_iff /-
/-- If `a` is even, then `n` is even iff `n % a` is even. -/
theorem Even.mod_even_iff {n a : ℕ} (ha : Even a) : Even (n % a) ↔ Even n :=
  ((even_sub <| mod_le n a).mp <|
      even_iff_two_dvd.mpr <| (even_iff_two_dvd.mp ha).trans <| dvd_sub_mod n).symm
#align even.mod_even_iff Even.mod_even_iff
-/

#print Odd.mod_even /-
/-- If `n` is odd and `a` is even, then `n % a` is odd. -/
theorem Odd.mod_even {n a : ℕ} (hn : Odd n) (ha : Even a) : Odd (n % a) :=
  (Odd.mod_even_iff ha).mpr hn
#align odd.mod_even Odd.mod_even
-/

#print Even.mod_even /-
/-- If `n` is even and `a` is even, then `n % a` is even. -/
theorem Even.mod_even {n a : ℕ} (hn : Even n) (ha : Even a) : Even (n % a) :=
  (Even.mod_even_iff ha).mpr hn
#align even.mod_even Even.mod_even
-/

#print Odd.of_dvd_nat /-
theorem Odd.of_dvd_nat {m n : ℕ} (hn : Odd n) (hm : m ∣ n) : Odd m :=
  odd_iff_not_even.2 <| mt hm.Even (odd_iff_not_even.1 hn)
#align odd.of_dvd_nat Odd.of_dvd_nat
-/

#print Odd.ne_two_of_dvd_nat /-
/-- `2` is not a factor of an odd natural number. -/
theorem Odd.ne_two_of_dvd_nat {m n : ℕ} (hn : Odd n) (hm : m ∣ n) : m ≠ 2 :=
  by
  rintro rfl
  exact absurd (hn.of_dvd_nat hm) (by decide)
#align odd.ne_two_of_dvd_nat Odd.ne_two_of_dvd_nat
-/

