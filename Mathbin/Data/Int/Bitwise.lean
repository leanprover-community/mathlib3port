/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathbin.Data.Int.Basic
import Mathbin.Data.Nat.Pow

/-!
# Bitwise operations on integers


## Recursors
* `int.bit_cases_on`: Parity disjunction. Something is true/defined on `ℤ` if it's true/defined for
  even and for odd values.

-/


namespace Int

/-! ### bitwise ops -/


@[simp]
theorem bodd_zero : bodd 0 = ff :=
  rfl

@[simp]
theorem bodd_one : bodd 1 = tt :=
  rfl

theorem bodd_two : bodd 2 = ff :=
  rfl

@[simp, norm_cast]
theorem bodd_coe (n : ℕ) : Int.bodd n = Nat.bodd n :=
  rfl

@[simp]
theorem bodd_sub_nat_nat (m n : ℕ) : bodd (subNatNat m n) = xor m.bodd n.bodd := by
  apply sub_nat_nat_elim m n fun m n i => bodd i = xor m.bodd n.bodd <;> intros <;> simp <;> cases i.bodd <;> simp

@[simp]
theorem bodd_neg_of_nat (n : ℕ) : bodd (negOfNat n) = n.bodd := by cases n <;> simp <;> rfl

@[simp]
theorem bodd_neg (n : ℤ) : bodd (-n) = bodd n := by
  cases n <;> simp [Neg.neg, Int.coe_nat_eq, Int.neg, bodd, -of_nat_eq_coe]

@[simp]
theorem bodd_add (m n : ℤ) : bodd (m + n) = xor (bodd m) (bodd n) := by
  cases' m with m m <;> cases' n with n n <;> unfold Add.add <;> simp [Int.add, -of_nat_eq_coe, Bool.bxor_comm]

@[simp]
theorem bodd_mul (m n : ℤ) : bodd (m * n) = (bodd m && bodd n) := by
  cases' m with m m <;> cases' n with n n <;> simp [← Int.mul_def, Int.mul, -of_nat_eq_coe, Bool.bxor_comm]

theorem bodd_add_div2 : ∀ n, cond (bodd n) 1 0 + 2 * div2 n = n
  | (n : ℕ) => by
    rw [show (cond (bodd n) 1 0 : ℤ) = (cond (bodd n) 1 0 : ℕ) by cases bodd n <;> rfl] <;>
      exact congr_arg of_nat n.bodd_add_div2
  | -[n+1] => by
    refine' Eq.trans _ (congr_arg neg_succ_of_nat n.bodd_add_div2)
    dsimp [bodd]
    cases Nat.bodd n <;> dsimp [cond, not, div2, Int.mul]
    · change -[2 * Nat.div2 n+1] = _
      rw [zero_add]
      
    · rw [zero_add, add_comm]
      rfl
      

theorem div2_val : ∀ n, div2 n = n / 2
  | (n : ℕ) => congr_arg ofNat n.div2_val
  | -[n+1] => congr_arg negSucc n.div2_val

theorem bit0_val (n : ℤ) : bit0 n = 2 * n :=
  (two_mul _).symm

theorem bit1_val (n : ℤ) : bit1 n = 2 * n + 1 :=
  congr_arg (· + (1 : ℤ)) (bit0_val _)

theorem bit_val (b n) : bit b n = 2 * n + cond b 1 0 := by
  cases b
  apply (bit0_val n).trans (add_zero _).symm
  apply bit1_val

theorem bit_decomp (n : ℤ) : bit (bodd n) (div2 n) = n :=
  (bit_val _ _).trans <| (add_comm _ _).trans <| bodd_add_div2 _

/-- Defines a function from `ℤ` conditionally, if it is defined for odd and even integers separately
  using `bit`. -/
def bitCasesOn.{u} {C : ℤ → Sort u} (n) (h : ∀ b n, C (bit b n)) : C n := by rw [← bit_decomp n] <;> apply h

@[simp]
theorem bit_zero : bit false 0 = 0 :=
  rfl

@[simp]
theorem bit_coe_nat (b) (n : ℕ) : bit b n = Nat.bit b n := by rw [bit_val, Nat.bit_val] <;> cases b <;> rfl

@[simp]
theorem bit_neg_succ (b) (n : ℕ) : bit b -[n+1] = -[Nat.bit (not b) n+1] := by
  rw [bit_val, Nat.bit_val] <;> cases b <;> rfl

@[simp]
theorem bodd_bit (b n) : bodd (bit b n) = b := by rw [bit_val] <;> simp <;> cases b <;> cases bodd n <;> rfl

@[simp]
theorem bodd_bit0 (n : ℤ) : bodd (bit0 n) = ff :=
  bodd_bit false n

@[simp]
theorem bodd_bit1 (n : ℤ) : bodd (bit1 n) = tt :=
  bodd_bit true n

theorem bit0_ne_bit1 (m n : ℤ) : bit0 m ≠ bit1 n :=
  mt (congr_arg bodd) <| by simp

theorem bit1_ne_bit0 (m n : ℤ) : bit1 m ≠ bit0 n :=
  (bit0_ne_bit1 _ _).symm

theorem bit1_ne_zero (m : ℤ) : bit1 m ≠ 0 := by simpa only [bit0_zero] using bit1_ne_bit0 m 0

@[simp]
theorem test_bit_zero (b) : ∀ n, testBit (bit b n) 0 = b
  | (n : ℕ) => by rw [bit_coe_nat] <;> apply Nat.test_bit_zero
  | -[n+1] => by
    rw [bit_neg_succ] <;> dsimp [test_bit] <;> rw [Nat.test_bit_zero] <;> clear test_bit_zero <;> cases b <;> rfl

@[simp]
theorem test_bit_succ (m b) : ∀ n, testBit (bit b n) (Nat.succ m) = testBit n m
  | (n : ℕ) => by rw [bit_coe_nat] <;> apply Nat.test_bit_succ
  | -[n+1] => by rw [bit_neg_succ] <;> dsimp [test_bit] <;> rw [Nat.test_bit_succ]

/- ./././Mathport/Syntax/Translate/Expr.lean:332:4: warning: unsupported (TODO): `[tacs] -/
private unsafe def bitwise_tac : tactic Unit :=
  sorry

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic _private.918271365.bitwise_tac -/
theorem bitwise_or : bitwise or = lor := by
  run_tac
    bitwise_tac

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic _private.918271365.bitwise_tac -/
theorem bitwise_and : bitwise and = land := by
  run_tac
    bitwise_tac

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic _private.918271365.bitwise_tac -/
theorem bitwise_diff : (bitwise fun a b => a && not b) = ldiff := by
  run_tac
    bitwise_tac

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic _private.918271365.bitwise_tac -/
theorem bitwise_xor : bitwise xor = lxor := by
  run_tac
    bitwise_tac

/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:489:27: warning: unsupported: unfold config -/
@[simp]
theorem bitwise_bit (f : Bool → Bool → Bool) (a m b n) : bitwise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n) :=
  by
  cases' m with m m <;>
    cases' n with n n <;>
      repeat' first |rw [← Int.coe_nat_eq]|rw [bit_coe_nat]|rw [bit_neg_succ] <;>
        unfold bitwise nat_bitwise not <;> [induction' h : f ff ff with , induction' h : f ff tt with ,
          induction' h : f tt ff with , induction' h : f tt tt with ]
  all_goals
  unfold cond
  rw [Nat.bitwise_bit]
  repeat' first |rw [bit_coe_nat]|rw [bit_neg_succ]|rw [Bool.not_not]
  all_goals unfold not <;> rw [h] <;> rfl

@[simp]
theorem lor_bit (a m b n) : lor (bit a m) (bit b n) = bit (a || b) (lor m n) := by rw [← bitwise_or, bitwise_bit]

@[simp]
theorem land_bit (a m b n) : land (bit a m) (bit b n) = bit (a && b) (land m n) := by rw [← bitwise_and, bitwise_bit]

@[simp]
theorem ldiff_bit (a m b n) : ldiff (bit a m) (bit b n) = bit (a && not b) (ldiff m n) := by
  rw [← bitwise_diff, bitwise_bit]

@[simp]
theorem lxor_bit (a m b n) : lxor (bit a m) (bit b n) = bit (xor a b) (lxor m n) := by rw [← bitwise_xor, bitwise_bit]

@[simp]
theorem lnot_bit (b) : ∀ n, lnot (bit b n) = bit (not b) (lnot n)
  | (n : ℕ) => by simp [lnot]
  | -[n+1] => by simp [lnot]

@[simp]
theorem test_bit_bitwise (f : Bool → Bool → Bool) (m n k) : testBit (bitwise f m n) k = f (testBit m k) (testBit n k) :=
  by
  induction' k with k IH generalizing m n <;>
    apply bit_cases_on m <;> intro a m' <;> apply bit_cases_on n <;> intro b n' <;> rw [bitwise_bit]
  · simp [test_bit_zero]
    
  · simp [test_bit_succ, IH]
    

@[simp]
theorem test_bit_lor (m n k) : testBit (lor m n) k = (testBit m k || testBit n k) := by
  rw [← bitwise_or, test_bit_bitwise]

@[simp]
theorem test_bit_land (m n k) : testBit (land m n) k = (testBit m k && testBit n k) := by
  rw [← bitwise_and, test_bit_bitwise]

@[simp]
theorem test_bit_ldiff (m n k) : testBit (ldiff m n) k = (testBit m k && not (testBit n k)) := by
  rw [← bitwise_diff, test_bit_bitwise]

@[simp]
theorem test_bit_lxor (m n k) : testBit (lxor m n) k = xor (testBit m k) (testBit n k) := by
  rw [← bitwise_xor, test_bit_bitwise]

@[simp]
theorem test_bit_lnot : ∀ n k, testBit (lnot n) k = not (testBit n k)
  | (n : ℕ), k => by simp [lnot, test_bit]
  | -[n+1], k => by simp [lnot, test_bit]

@[simp]
theorem shiftl_neg (m n : ℤ) : shiftl m (-n) = shiftr m n :=
  rfl

@[simp]
theorem shiftr_neg (m n : ℤ) : shiftr m (-n) = shiftl m n := by rw [← shiftl_neg, neg_neg]

@[simp]
theorem shiftl_coe_nat (m n : ℕ) : shiftl m n = Nat.shiftl m n :=
  rfl

@[simp]
theorem shiftr_coe_nat (m n : ℕ) : shiftr m n = Nat.shiftr m n := by cases n <;> rfl

@[simp]
theorem shiftl_neg_succ (m n : ℕ) : shiftl -[m+1] n = -[Nat.shiftl' true m n+1] :=
  rfl

@[simp]
theorem shiftr_neg_succ (m n : ℕ) : shiftr -[m+1] n = -[Nat.shiftr m n+1] := by cases n <;> rfl

theorem shiftr_add : ∀ (m : ℤ) (n k : ℕ), shiftr m (n + k) = shiftr (shiftr m n) k
  | (m : ℕ), n, k => by rw [shiftr_coe_nat, shiftr_coe_nat, ← Int.coe_nat_add, shiftr_coe_nat, Nat.shiftr_add]
  | -[m+1], n, k => by rw [shiftr_neg_succ, shiftr_neg_succ, ← Int.coe_nat_add, shiftr_neg_succ, Nat.shiftr_add]

/-! ### bitwise ops -/


attribute [local simp] Int.zero_div

theorem shiftl_add : ∀ (m : ℤ) (n : ℕ) (k : ℤ), shiftl m (n + k) = shiftl (shiftl m n) k
  | (m : ℕ), n, (k : ℕ) => congr_arg ofNat (Nat.shiftl_add _ _ _)
  | -[m+1], n, (k : ℕ) => congr_arg negSucc (Nat.shiftl'_add _ _ _ _)
  | (m : ℕ), n, -[k+1] =>
    sub_nat_nat_elim n k.succ (fun n k i => shiftl (↑m) i = Nat.shiftr (Nat.shiftl m n) k)
      (fun i n => congr_arg coe <| by rw [← Nat.shiftl_sub, add_tsub_cancel_left] <;> apply Nat.le_add_right) fun i n =>
      congr_arg coe <| by rw [add_assoc, Nat.shiftr_add, ← Nat.shiftl_sub, tsub_self] <;> rfl
  | -[m+1], n, -[k+1] =>
    sub_nat_nat_elim n k.succ (fun n k i => shiftl -[m+1] i = -[Nat.shiftr (Nat.shiftl' true m n) k+1])
      (fun i n => congr_arg negSucc <| by rw [← Nat.shiftl'_sub, add_tsub_cancel_left] <;> apply Nat.le_add_right)
      fun i n => congr_arg negSucc <| by rw [add_assoc, Nat.shiftr_add, ← Nat.shiftl'_sub, tsub_self] <;> rfl

theorem shiftl_sub (m : ℤ) (n : ℕ) (k : ℤ) : shiftl m (n - k) = shiftr (shiftl m n) k :=
  shiftl_add _ _ _

theorem shiftl_eq_mul_pow : ∀ (m : ℤ) (n : ℕ), shiftl m n = m * ↑(2 ^ n)
  | (m : ℕ), n => congr_arg coe (Nat.shiftl_eq_mul_pow _ _)
  | -[m+1], n => @congr_arg ℕ ℤ _ _ (fun i => -i) (Nat.shiftl'_tt_eq_mul_pow _ _)

theorem shiftr_eq_div_pow : ∀ (m : ℤ) (n : ℕ), shiftr m n = m / ↑(2 ^ n)
  | (m : ℕ), n => by rw [shiftr_coe_nat] <;> exact congr_arg coe (Nat.shiftr_eq_div_pow _ _)
  | -[m+1], n => by
    rw [shiftr_neg_succ, neg_succ_of_nat_div, Nat.shiftr_eq_div_pow]
    rfl
    exact coe_nat_lt_coe_nat_of_lt (pow_pos (by decide) _)

theorem one_shiftl (n : ℕ) : shiftl 1 n = (2 ^ n : ℕ) :=
  congr_arg coe (Nat.one_shiftl _)

@[simp]
theorem zero_shiftl : ∀ n : ℤ, shiftl 0 n = 0
  | (n : ℕ) => congr_arg coe (Nat.zero_shiftl _)
  | -[n+1] => congr_arg coe (Nat.zero_shiftr _)

@[simp]
theorem zero_shiftr (n) : shiftr 0 n = 0 :=
  zero_shiftl _

end Int

