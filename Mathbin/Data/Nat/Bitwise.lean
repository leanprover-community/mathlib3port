/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module data.nat.bitwise
! leanprover-community/mathlib commit e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Basic
import Mathbin.Data.Nat.Bits
import Mathbin.Tactic.Linarith.Default

/-!
# Bitwise operations on natural numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In the first half of this file, we provide theorems for reasoning about natural numbers from their
bitwise properties. In the second half of this file, we show properties of the bitwise operations
`lor`, `land` and `lxor`, which are defined in core.

## Main results
* `eq_of_test_bit_eq`: two natural numbers are equal if they have equal bits at every position.
* `exists_most_significant_bit`: if `n ≠ 0`, then there is some position `i` that contains the most
  significant `1`-bit of `n`.
* `lt_of_test_bit`: if `n` and `m` are numbers and `i` is a position such that the `i`-th bit of
  of `n` is zero, the `i`-th bit of `m` is one, and all more significant bits are equal, then
  `n < m`.

## Future work

There is another way to express bitwise properties of natural number: `digits 2`. The two ways
should be connected.

## Keywords

bitwise, and, or, xor
-/


open Function

namespace Nat

#print Nat.bit_false /-
@[simp]
theorem bit_false : bit false = bit0 :=
  rfl
#align nat.bit_ff Nat.bit_false
-/

#print Nat.bit_true /-
@[simp]
theorem bit_true : bit true = bit1 :=
  rfl
#align nat.bit_tt Nat.bit_true
-/

#print Nat.bit_eq_zero /-
@[simp]
theorem bit_eq_zero {n : ℕ} {b : Bool} : n.bit b = 0 ↔ n = 0 ∧ b = false := by
  cases b <;> simp [Nat.bit0_eq_zero, Nat.bit1_ne_zero]
#align nat.bit_eq_zero Nat.bit_eq_zero
-/

#print Nat.zero_of_testBit_eq_false /-
theorem zero_of_testBit_eq_false {n : ℕ} (h : ∀ i, testBit n i = false) : n = 0 :=
  by
  induction' n using Nat.binaryRec with b n hn
  · rfl
  · have : b = ff := by simpa using h 0
    rw [this, bit_ff, bit0_val, hn fun i => by rw [← h (i + 1), test_bit_succ], mul_zero]
#align nat.zero_of_test_bit_eq_ff Nat.zero_of_testBit_eq_false
-/

#print Nat.zero_testBit /-
@[simp]
theorem zero_testBit (i : ℕ) : testBit 0 i = false := by simp [test_bit]
#align nat.zero_test_bit Nat.zero_testBit
-/

#print Nat.testBit_eq_inth /-
/-- The ith bit is the ith element of `n.bits`. -/
theorem testBit_eq_inth (n i : ℕ) : n.testBit i = n.bits.getI i :=
  by
  induction' i with i ih generalizing n
  · simp [test_bit, shiftr, bodd_eq_bits_head, List.getI_zero_eq_headI]
  conv_lhs => rw [← bit_decomp n]
  rw [test_bit_succ, ih n.div2, div2_bits_eq_tail]
  cases n.bits <;> simp
#align nat.test_bit_eq_inth Nat.testBit_eq_inth
-/

#print Nat.eq_of_testBit_eq /-
/-- Bitwise extensionality: Two numbers agree if they agree at every bit position. -/
theorem eq_of_testBit_eq {n m : ℕ} (h : ∀ i, testBit n i = testBit m i) : n = m :=
  by
  induction' n using Nat.binaryRec with b n hn generalizing m
  · simp only [zero_test_bit] at h
    exact (zero_of_test_bit_eq_ff fun i => (h i).symm).symm
  induction' m using Nat.binaryRec with b' m hm
  · simp only [zero_test_bit] at h
    exact zero_of_test_bit_eq_ff h
  suffices h' : n = m
  · rw [h', show b = b' by simpa using h 0]
  exact hn fun i => by convert h (i + 1) using 1 <;> rw [test_bit_succ]
#align nat.eq_of_test_bit_eq Nat.eq_of_testBit_eq
-/

#print Nat.exists_most_significant_bit /-
theorem exists_most_significant_bit {n : ℕ} (h : n ≠ 0) :
    ∃ i, testBit n i = true ∧ ∀ j, i < j → testBit n j = false :=
  by
  induction' n using Nat.binaryRec with b n hn
  · exact False.elim (h rfl)
  by_cases h' : n = 0
  · subst h'
    rw [show b = tt by
        revert h
        cases b <;> simp]
    refine' ⟨0, ⟨by rw [test_bit_zero], fun j hj => _⟩⟩
    obtain ⟨j', rfl⟩ := exists_eq_succ_of_ne_zero (ne_of_gt hj)
    rw [test_bit_succ, zero_test_bit]
  · obtain ⟨k, ⟨hk, hk'⟩⟩ := hn h'
    refine' ⟨k + 1, ⟨by rw [test_bit_succ, hk], fun j hj => _⟩⟩
    obtain ⟨j', rfl⟩ := exists_eq_succ_of_ne_zero (show j ≠ 0 by linarith)
    exact (test_bit_succ _ _ _).trans (hk' _ (lt_of_succ_lt_succ hj))
#align nat.exists_most_significant_bit Nat.exists_most_significant_bit
-/

#print Nat.lt_of_testBit /-
theorem lt_of_testBit {n m : ℕ} (i : ℕ) (hn : testBit n i = false) (hm : testBit m i = true)
    (hnm : ∀ j, i < j → testBit n j = testBit m j) : n < m :=
  by
  induction' n using Nat.binaryRec with b n hn' generalizing i m
  · contrapose! hm
    rw [le_zero_iff] at hm
    simp [hm]
  induction' m using Nat.binaryRec with b' m hm' generalizing i
  · exact False.elim (Bool.false_ne_true ((zero_test_bit i).symm.trans hm))
  by_cases hi : i = 0
  · subst hi
    simp only [test_bit_zero] at hn hm
    have : n = m :=
      eq_of_test_bit_eq fun i => by convert hnm (i + 1) (by decide) using 1 <;> rw [test_bit_succ]
    rw [hn, hm, this, bit_ff, bit_tt, bit0_val, bit1_val]
    exact lt_add_one _
  · obtain ⟨i', rfl⟩ := exists_eq_succ_of_ne_zero hi
    simp only [test_bit_succ] at hn hm
    have :=
      hn' _ hn hm fun j hj => by convert hnm j.succ (succ_lt_succ hj) using 1 <;> rw [test_bit_succ]
    cases b <;> cases b' <;>
        simp only [bit_ff, bit_tt, bit0_val n, bit1_val n, bit0_val m, bit1_val m] <;>
      linarith
#align nat.lt_of_test_bit Nat.lt_of_testBit
-/

#print Nat.testBit_two_pow_self /-
@[simp]
theorem testBit_two_pow_self (n : ℕ) : testBit (2 ^ n) n = true := by
  rw [test_bit, shiftr_eq_div_pow, Nat.div_self (pow_pos zero_lt_two n), bodd_one]
#align nat.test_bit_two_pow_self Nat.testBit_two_pow_self
-/

#print Nat.testBit_two_pow_of_ne /-
theorem testBit_two_pow_of_ne {n m : ℕ} (hm : n ≠ m) : testBit (2 ^ n) m = false :=
  by
  rw [test_bit, shiftr_eq_div_pow]
  cases' hm.lt_or_lt with hm hm
  · rw [Nat.div_eq_zero, bodd_zero]
    exact Nat.pow_lt_pow_of_lt_right one_lt_two hm
  · rw [pow_div hm.le zero_lt_two, ← tsub_add_cancel_of_le (succ_le_of_lt <| tsub_pos_of_lt hm)]
    simp [pow_succ]
#align nat.test_bit_two_pow_of_ne Nat.testBit_two_pow_of_ne
-/

/- warning: nat.test_bit_two_pow -> Nat.testBit_two_pow is a dubious translation:
lean 3 declaration is
  forall (n : Nat) (m : Nat), Eq.{1} Bool (Nat.testBit (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) n) m) (Decidable.decide (Eq.{1} Nat n m) (Nat.decidableEq n m))
but is expected to have type
  forall (n : Nat) (m : Nat), Eq.{1} Prop (Eq.{1} Bool (Nat.testBit (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) n) m) Bool.true) (Eq.{1} Nat n m)
Case conversion may be inaccurate. Consider using '#align nat.test_bit_two_pow Nat.testBit_two_powₓ'. -/
theorem testBit_two_pow (n m : ℕ) : testBit (2 ^ n) m = (n = m) :=
  by
  by_cases n = m
  · cases h
    simp
  · rw [test_bit_two_pow_of_ne h]
    simp [h]
#align nat.test_bit_two_pow Nat.testBit_two_pow

/- warning: nat.bitwise_comm -> Nat.bitwise'_comm is a dubious translation:
lean 3 declaration is
  forall {f : Bool -> Bool -> Bool}, (forall (b : Bool) (b' : Bool), Eq.{1} Bool (f b b') (f b' b)) -> (Eq.{1} Bool (f Bool.false Bool.false) Bool.false) -> (forall (n : Nat) (m : Nat), Eq.{1} Nat (Nat.bitwise f n m) (Nat.bitwise f m n))
but is expected to have type
  forall {f : Bool -> Bool -> Bool}, (forall (b : Bool) (b' : Bool), Eq.{1} Bool (f b b') (f b' b)) -> (Eq.{1} Bool (f Bool.false Bool.false) Bool.false) -> (forall (n : Nat) (m : Nat), Eq.{1} Nat (Nat.bitwise' f n m) (Nat.bitwise' f m n))
Case conversion may be inaccurate. Consider using '#align nat.bitwise_comm Nat.bitwise'_commₓ'. -/
/-- If `f` is a commutative operation on bools such that `f ff ff = ff`, then `bitwise f` is also
    commutative. -/
theorem bitwise'_comm {f : Bool → Bool → Bool} (hf : ∀ b b', f b b' = f b' b)
    (hf' : f false false = false) (n m : ℕ) : bitwise f n m = bitwise f m n :=
  suffices bitwise f = swap (bitwise f) by conv_lhs => rw [this]
  calc
    bitwise f = bitwise (swap f) := congr_arg _ <| funext fun _ => funext <| hf _
    _ = swap (bitwise f) := bitwise'_swap hf'
    
#align nat.bitwise_comm Nat.bitwise'_comm

/- warning: nat.lor_comm -> Nat.lor'_comm is a dubious translation:
lean 3 declaration is
  forall (n : Nat) (m : Nat), Eq.{1} Nat (Nat.lor n m) (Nat.lor m n)
but is expected to have type
  forall (n : Nat) (m : Nat), Eq.{1} Nat (Nat.lor' n m) (Nat.lor' m n)
Case conversion may be inaccurate. Consider using '#align nat.lor_comm Nat.lor'_commₓ'. -/
theorem lor'_comm (n m : ℕ) : lor n m = lor m n :=
  bitwise'_comm Bool.or_comm rfl n m
#align nat.lor_comm Nat.lor'_comm

/- warning: nat.land_comm -> Nat.land'_comm is a dubious translation:
lean 3 declaration is
  forall (n : Nat) (m : Nat), Eq.{1} Nat (Nat.land n m) (Nat.land m n)
but is expected to have type
  forall (n : Nat) (m : Nat), Eq.{1} Nat (Nat.land' n m) (Nat.land' m n)
Case conversion may be inaccurate. Consider using '#align nat.land_comm Nat.land'_commₓ'. -/
theorem land'_comm (n m : ℕ) : land n m = land m n :=
  bitwise'_comm Bool.and_comm rfl n m
#align nat.land_comm Nat.land'_comm

#print Nat.lxor'_comm /-
theorem lxor'_comm (n m : ℕ) : lxor' n m = lxor' m n :=
  bitwise'_comm Bool.xor_comm rfl n m
#align nat.lxor_comm Nat.lxor'_comm
-/

#print Nat.zero_lxor' /-
@[simp]
theorem zero_lxor' (n : ℕ) : lxor' 0 n = n := by simp [lxor]
#align nat.zero_lxor Nat.zero_lxor'
-/

#print Nat.lxor'_zero /-
@[simp]
theorem lxor'_zero (n : ℕ) : lxor' n 0 = n := by simp [lxor]
#align nat.lxor_zero Nat.lxor'_zero
-/

#print Nat.zero_land' /-
@[simp]
theorem zero_land' (n : ℕ) : land 0 n = 0 := by simp [land]
#align nat.zero_land Nat.zero_land'
-/

/- warning: nat.land_zero -> Nat.land'_zero is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{1} Nat (Nat.land n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))
but is expected to have type
  forall (n : Nat), Eq.{1} Nat (Nat.land' n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))
Case conversion may be inaccurate. Consider using '#align nat.land_zero Nat.land'_zeroₓ'. -/
@[simp]
theorem land'_zero (n : ℕ) : land n 0 = 0 := by simp [land]
#align nat.land_zero Nat.land'_zero

#print Nat.zero_lor' /-
@[simp]
theorem zero_lor' (n : ℕ) : lor 0 n = n := by simp [lor]
#align nat.zero_lor Nat.zero_lor'
-/

/- warning: nat.lor_zero -> Nat.lor'_zero is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{1} Nat (Nat.lor n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) n
but is expected to have type
  forall (n : Nat), Eq.{1} Nat (Nat.lor' n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) n
Case conversion may be inaccurate. Consider using '#align nat.lor_zero Nat.lor'_zeroₓ'. -/
@[simp]
theorem lor'_zero (n : ℕ) : lor n 0 = n := by simp [lor]
#align nat.lor_zero Nat.lor'_zero

/- ./././Mathport/Syntax/Translate/Expr.lean:334:4: warning: unsupported (TODO): `[tacs] -/
/-- Proving associativity of bitwise operations in general essentially boils down to a huge case
    distinction, so it is shorter to use this tactic instead of proving it in the general case. -/
unsafe def bitwise_assoc_tac : tactic Unit :=
  sorry
#align nat.bitwise_assoc_tac nat.bitwise_assoc_tac

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic nat.bitwise_assoc_tac -/
#print Nat.lxor'_assoc /-
theorem lxor'_assoc (n m k : ℕ) : lxor' (lxor' n m) k = lxor' n (lxor' m k) := by
  run_tac
    bitwise_assoc_tac
#align nat.lxor_assoc Nat.lxor'_assoc
-/

/- warning: nat.land_assoc -> Nat.land'_assoc is a dubious translation:
lean 3 declaration is
  forall (n : Nat) (m : Nat) (k : Nat), Eq.{1} Nat (Nat.land (Nat.land n m) k) (Nat.land n (Nat.land m k))
but is expected to have type
  forall (n : Nat) (m : Nat) (k : Nat), Eq.{1} Nat (Nat.land' (Nat.land' n m) k) (Nat.land' n (Nat.land' m k))
Case conversion may be inaccurate. Consider using '#align nat.land_assoc Nat.land'_assocₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic nat.bitwise_assoc_tac -/
theorem land'_assoc (n m k : ℕ) : land (land n m) k = land n (land m k) := by
  run_tac
    bitwise_assoc_tac
#align nat.land_assoc Nat.land'_assoc

/- warning: nat.lor_assoc -> Nat.lor'_assoc is a dubious translation:
lean 3 declaration is
  forall (n : Nat) (m : Nat) (k : Nat), Eq.{1} Nat (Nat.lor (Nat.lor n m) k) (Nat.lor n (Nat.lor m k))
but is expected to have type
  forall (n : Nat) (m : Nat) (k : Nat), Eq.{1} Nat (Nat.lor' (Nat.lor' n m) k) (Nat.lor' n (Nat.lor' m k))
Case conversion may be inaccurate. Consider using '#align nat.lor_assoc Nat.lor'_assocₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic nat.bitwise_assoc_tac -/
theorem lor'_assoc (n m k : ℕ) : lor (lor n m) k = lor n (lor m k) := by
  run_tac
    bitwise_assoc_tac
#align nat.lor_assoc Nat.lor'_assoc

#print Nat.lxor'_self /-
@[simp]
theorem lxor'_self (n : ℕ) : lxor' n n = 0 :=
  zero_of_testBit_eq_false fun i => by simp
#align nat.lxor_self Nat.lxor'_self
-/

#print Nat.lxor_cancel_right /-
-- These lemmas match `mul_inv_cancel_right` and `mul_inv_cancel_left`.
theorem lxor_cancel_right (n m : ℕ) : lxor' (lxor' m n) n = m := by
  rw [lxor_assoc, lxor_self, lxor_zero]
#align nat.lxor_cancel_right Nat.lxor_cancel_right
-/

#print Nat.lxor'_cancel_left /-
theorem lxor'_cancel_left (n m : ℕ) : lxor' n (lxor' n m) = m := by
  rw [← lxor_assoc, lxor_self, zero_lxor]
#align nat.lxor_cancel_left Nat.lxor'_cancel_left
-/

#print Nat.lxor'_right_injective /-
theorem lxor'_right_injective {n : ℕ} : Function.Injective (lxor' n) := fun m m' h => by
  rw [← lxor_cancel_left n m, ← lxor_cancel_left n m', h]
#align nat.lxor_right_injective Nat.lxor'_right_injective
-/

#print Nat.lxor'_left_injective /-
theorem lxor'_left_injective {n : ℕ} : Function.Injective fun m => lxor' m n :=
  fun m m' (h : lxor' m n = lxor' m' n) => by
  rw [← lxor_cancel_right n m, ← lxor_cancel_right n m', h]
#align nat.lxor_left_injective Nat.lxor'_left_injective
-/

#print Nat.lxor'_right_inj /-
@[simp]
theorem lxor'_right_inj {n m m' : ℕ} : lxor' n m = lxor' n m' ↔ m = m' :=
  lxor'_right_injective.eq_iff
#align nat.lxor_right_inj Nat.lxor'_right_inj
-/

#print Nat.lxor'_left_inj /-
@[simp]
theorem lxor'_left_inj {n m m' : ℕ} : lxor' m n = lxor' m' n ↔ m = m' :=
  lxor'_left_injective.eq_iff
#align nat.lxor_left_inj Nat.lxor'_left_inj
-/

#print Nat.lxor'_eq_zero /-
@[simp]
theorem lxor'_eq_zero {n m : ℕ} : lxor' n m = 0 ↔ n = m := by
  rw [← lxor_self n, lxor_right_inj, eq_comm]
#align nat.lxor_eq_zero Nat.lxor'_eq_zero
-/

#print Nat.lxor'_ne_zero /-
theorem lxor'_ne_zero {n m : ℕ} : lxor' n m ≠ 0 ↔ n ≠ m :=
  lxor'_eq_zero.Not
#align nat.lxor_ne_zero Nat.lxor'_ne_zero
-/

#print Nat.lxor'_trichotomy /-
theorem lxor'_trichotomy {a b c : ℕ} (h : a ≠ lxor' b c) :
    lxor' b c < a ∨ lxor' a c < b ∨ lxor' a b < c :=
  by
  set v := lxor a (lxor b c) with hv
  -- The xor of any two of `a`, `b`, `c` is the xor of `v` and the third.
  have hab : lxor a b = lxor c v := by
    rw [hv]
    conv_rhs =>
      rw [lxor_comm]
      simp [lxor_assoc]
  have hac : lxor a c = lxor b v := by
    rw [hv]
    conv_rhs =>
      congr
      skip
      rw [lxor_comm]
    rw [← lxor_assoc, ← lxor_assoc, lxor_self, zero_lxor, lxor_comm]
  have hbc : lxor b c = lxor a v := by simp [hv, ← lxor_assoc]
  -- If `i` is the position of the most significant bit of `v`, then at least one of `a`, `b`, `c`
  -- has a one bit at position `i`.
  obtain ⟨i, ⟨hi, hi'⟩⟩ := exists_most_significant_bit (lxor_ne_zero.2 h)
  have : test_bit a i = tt ∨ test_bit b i = tt ∨ test_bit c i = tt :=
    by
    contrapose! hi
    simp only [Bool.eq_false_eq_not_eq_true, Ne, test_bit_lxor] at hi⊢
    rw [hi.1, hi.2.1, hi.2.2, Bool.xor_false, Bool.xor_false]
  -- If, say, `a` has a one bit at position `i`, then `a xor v` has a zero bit at position `i`, but
      -- the same bits as `a` in positions greater than `j`, so `a xor v < a`.
      rcases this with (h | h | h) <;>
      [·
        left
        rw [hbc],
      · right
        left
        rw [hac],
      · right
        right
        rw [hab]] <;>
    exact lt_of_test_bit i (by simp [h, hi]) h fun j hj => by simp [hi' _ hj]
#align nat.lxor_trichotomy Nat.lxor'_trichotomy
-/

#print Nat.lt_lxor'_cases /-
theorem lt_lxor'_cases {a b c : ℕ} (h : a < lxor' b c) : lxor' a c < b ∨ lxor' a b < c :=
  (or_iff_right fun h' => (h.asymm h').elim).1 <| lxor'_trichotomy h.Ne
#align nat.lt_lxor_cases Nat.lt_lxor'_cases
-/

end Nat

