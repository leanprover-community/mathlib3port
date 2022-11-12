/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import Mathbin.Tactic.GeneralizeProofs
import Mathbin.Tactic.NormNum

/-!
# Additional properties of binary recursion on `nat`

This file documents additional properties of binary recursion,
which allows us to more easily work with operations which do depend
on the number of leading zeros in the binary representation of `n`.
For example, we can more easily work with `nat.bits` and `nat.size`.

See also: `nat.bitwise`, `nat.pow` (for various lemmas about `size` and `shiftl`/`shiftr`),
and `nat.digits`.
-/


namespace Nat

theorem bit_eq_zero_iff {n : ℕ} {b : Bool} : bit b n = 0 ↔ n = 0 ∧ b = ff := by
  constructor
  · cases b <;> simp [Nat.bit]
    
  rintro ⟨rfl, rfl⟩
  rfl
#align nat.bit_eq_zero_iff Nat.bit_eq_zero_iff

/-- The same as binary_rec_eq, but that one unfortunately requires `f` to be the identity when
  appending `ff` to `0`. Here, we allow you to explicitly say that that case is not happening, i.e.
  supplying `n = 0 → b = tt`. -/
theorem binary_rec_eq' {C : ℕ → Sort _} {z : C 0} {f : ∀ b n, C n → C (bit b n)} (b n)
    (h : f false 0 z = z ∨ (n = 0 → b = tt)) : binaryRec z f (bit b n) = f b n (binaryRec z f n) := by
  rw [binary_rec]
  split_ifs with h'
  · rcases bit_eq_zero_iff.mp h' with ⟨rfl, rfl⟩
    rw [binary_rec_zero]
    simp only [imp_false, or_false_iff, eq_self_iff_true, not_true] at h
    exact h.symm
    
  · generalize_proofs e
    revert e
    rw [bodd_bit, div2_bit]
    intros
    rfl
    
#align nat.binary_rec_eq' Nat.binary_rec_eq'

/-- The same as `binary_rec`, but the induction step can assume that if `n=0`,
  the bit being appended is `tt`-/
@[elab_as_elim]
def binaryRec' {C : ℕ → Sort _} (z : C 0) (f : ∀ b n, (n = 0 → b = tt) → C n → C (bit b n)) : ∀ n, C n :=
  binaryRec z fun b n ih =>
    if h : n = 0 → b = tt then f b n h ih
    else by
      convert z
      rw [bit_eq_zero_iff]
      simpa using h
#align nat.binary_rec' Nat.binaryRec'

/-- The same as `binary_rec`, but special casing both 0 and 1 as base cases -/
@[elab_as_elim]
def binaryRecFromOne {C : ℕ → Sort _} (z₀ : C 0) (z₁ : C 1) (f : ∀ b n, n ≠ 0 → C n → C (bit b n)) : ∀ n, C n :=
  binaryRec' z₀ fun b n h ih =>
    if h' : n = 0 then by
      rw [h', h h']
      exact z₁
    else f b n h' ih
#align nat.binary_rec_from_one Nat.binaryRecFromOne

@[simp]
theorem zero_bits : bits 0 = [] := by simp [Nat.bits]
#align nat.zero_bits Nat.zero_bits

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem bits_append_bit (n : ℕ) (b : Bool) (hn : n = 0 → b = tt) : (bit b n).bits = b::n.bits := by
  rw [Nat.bits, binary_rec_eq']
  simpa
#align nat.bits_append_bit Nat.bits_append_bit

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem bit0_bits (n : ℕ) (hn : n ≠ 0) : (bit0 n).bits = ff::n.bits :=
  bits_append_bit n false fun hn' => absurd hn' hn
#align nat.bit0_bits Nat.bit0_bits

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem bit1_bits (n : ℕ) : (bit1 n).bits = tt::n.bits :=
  bits_append_bit n true fun _ => rfl
#align nat.bit1_bits Nat.bit1_bits

@[simp]
theorem one_bits : Nat.bits 1 = [true] := by
  convert bit1_bits 0
  simp
#align nat.one_bits Nat.one_bits

example : bits 3423 = [true, true, true, true, true, false, true, false, true, false, true, true] := by norm_num

theorem bodd_eq_bits_head (n : ℕ) : n.bodd = n.bits.head := by
  induction' n using Nat.binaryRec' with b n h ih
  · simp
    
  simp [bodd_bit, bits_append_bit _ _ h]
#align nat.bodd_eq_bits_head Nat.bodd_eq_bits_head

theorem div2_bits_eq_tail (n : ℕ) : n.div2.bits = n.bits.tail := by
  induction' n using Nat.binaryRec' with b n h ih
  · simp
    
  simp [div2_bit, bits_append_bit _ _ h]
#align nat.div2_bits_eq_tail Nat.div2_bits_eq_tail

theorem size_eq_bits_len (n : ℕ) : n.bits.length = n.size := by
  induction' n using Nat.binaryRec' with b n h ih
  · simp
    
  rw [size_bit, bits_append_bit _ _ h]
  · simp [ih]
    
  · simpa [bit_eq_zero_iff]
    
#align nat.size_eq_bits_len Nat.size_eq_bits_len

end Nat

