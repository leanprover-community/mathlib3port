/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Data.Int.Basic
import Data.Nat.Pow
import Data.Nat.Size

#align_import data.int.bitwise from "leanprover-community/mathlib"@"c3291da49cfa65f0d43b094750541c0731edc932"

/-!
# Bitwise operations on integers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.


## Recursors
* `int.bit_cases_on`: Parity disjunction. Something is true/defined on `ℤ` if it's true/defined for
  even and for odd values.

-/


namespace Int

/-! ### bitwise ops -/


#print Int.bodd_zero /-
@[simp]
theorem bodd_zero : bodd 0 = false :=
  rfl
#align int.bodd_zero Int.bodd_zero
-/

#print Int.bodd_one /-
@[simp]
theorem bodd_one : bodd 1 = true :=
  rfl
#align int.bodd_one Int.bodd_one
-/

#print Int.bodd_two /-
theorem bodd_two : bodd 2 = false :=
  rfl
#align int.bodd_two Int.bodd_two
-/

#print Int.bodd_coe /-
@[simp, norm_cast]
theorem bodd_coe (n : ℕ) : Int.bodd n = Nat.bodd n :=
  rfl
#align int.bodd_coe Int.bodd_coe
-/

#print Int.bodd_subNatNat /-
@[simp]
theorem bodd_subNatNat (m n : ℕ) : bodd (subNatNat m n) = xor m.bodd n.bodd := by
  apply sub_nat_nat_elim m n fun m n i => bodd i = xor m.bodd n.bodd <;> intros <;> simp <;>
      cases i.bodd <;>
    simp
#align int.bodd_sub_nat_nat Int.bodd_subNatNat
-/

#print Int.bodd_negOfNat /-
@[simp]
theorem bodd_negOfNat (n : ℕ) : bodd (negOfNat n) = n.bodd := by cases n <;> simp <;> rfl
#align int.bodd_neg_of_nat Int.bodd_negOfNat
-/

#print Int.bodd_neg /-
@[simp]
theorem bodd_neg (n : ℤ) : bodd (-n) = bodd n := by
  cases n <;> simp [Neg.neg, Int.coe_nat_eq, Int.neg, bodd, -of_nat_eq_coe]
#align int.bodd_neg Int.bodd_neg
-/

#print Int.bodd_add /-
@[simp]
theorem bodd_add (m n : ℤ) : bodd (m + n) = xor (bodd m) (bodd n) := by
  cases' m with m m <;> cases' n with n n <;> unfold Add.add <;>
    simp [Int.add, -of_nat_eq_coe, Bool.xor_comm]
#align int.bodd_add Int.bodd_add
-/

#print Int.bodd_mul /-
@[simp]
theorem bodd_mul (m n : ℤ) : bodd (m * n) = (bodd m && bodd n) := by
  cases' m with m m <;> cases' n with n n <;>
    simp [← Int.mul_def, Int.mul, -of_nat_eq_coe, Bool.xor_comm]
#align int.bodd_mul Int.bodd_mul
-/

#print Int.bodd_add_div2 /-
theorem bodd_add_div2 : ∀ n, cond (bodd n) 1 0 + 2 * div2 n = n
  | (n : ℕ) => by
    rw [show (cond (bodd n) 1 0 : ℤ) = (cond (bodd n) 1 0 : ℕ) by cases bodd n <;> rfl] <;>
      exact congr_arg of_nat n.bodd_add_div2
  | -[n+1] => by
    refine' Eq.trans _ (congr_arg neg_succ_of_nat n.bodd_add_div2)
    dsimp [bodd]; cases Nat.bodd n <;> dsimp [cond, not, div2, Int.mul]
    · change -[2 * Nat.div2 n+1] = _; rw [zero_add]
    · rw [zero_add, add_comm]; rfl
#align int.bodd_add_div2 Int.bodd_add_div2
-/

#print Int.div2_val /-
theorem div2_val : ∀ n, div2 n = n / 2
  | (n : ℕ) => congr_arg ofNat n.div2_val
  | -[n+1] => congr_arg negSucc n.div2_val
#align int.div2_val Int.div2_val
-/

#print Int.bit0_val /-
theorem bit0_val (n : ℤ) : bit0 n = 2 * n :=
  (two_mul _).symm
#align int.bit0_val Int.bit0_val
-/

#print Int.bit1_val /-
theorem bit1_val (n : ℤ) : bit1 n = 2 * n + 1 :=
  congr_arg (· + (1 : ℤ)) (bit0_val _)
#align int.bit1_val Int.bit1_val
-/

#print Int.bit_val /-
theorem bit_val (b n) : bit b n = 2 * n + cond b 1 0 := by cases b;
  apply (bit0_val n).trans (add_zero _).symm; apply bit1_val
#align int.bit_val Int.bit_val
-/

#print Int.bit_decomp /-
theorem bit_decomp (n : ℤ) : bit (bodd n) (div2 n) = n :=
  (bit_val _ _).trans <| (add_comm _ _).trans <| bodd_add_div2 _
#align int.bit_decomp Int.bit_decomp
-/

#print Int.bitCasesOn /-
/-- Defines a function from `ℤ` conditionally, if it is defined for odd and even integers separately
  using `bit`. -/
def bitCasesOn.{u} {C : ℤ → Sort u} (n) (h : ∀ b n, C (bit b n)) : C n := by
  rw [← bit_decomp n] <;> apply h
#align int.bit_cases_on Int.bitCasesOn
-/

#print Int.bit_zero /-
@[simp]
theorem bit_zero : bit false 0 = 0 :=
  rfl
#align int.bit_zero Int.bit_zero
-/

#print Int.bit_coe_nat /-
@[simp]
theorem bit_coe_nat (b) (n : ℕ) : bit b n = Nat.bit b n := by
  rw [bit_val, Nat.bit_val] <;> cases b <;> rfl
#align int.bit_coe_nat Int.bit_coe_nat
-/

#print Int.bit_negSucc /-
@[simp]
theorem bit_negSucc (b) (n : ℕ) : bit b -[n+1] = -[Nat.bit (not b) n+1] := by
  rw [bit_val, Nat.bit_val] <;> cases b <;> rfl
#align int.bit_neg_succ Int.bit_negSucc
-/

#print Int.bodd_bit /-
@[simp]
theorem bodd_bit (b n) : bodd (bit b n) = b := by
  rw [bit_val] <;> simp <;> cases b <;> cases bodd n <;> rfl
#align int.bodd_bit Int.bodd_bit
-/

#print Int.bodd_bit0 /-
@[simp]
theorem bodd_bit0 (n : ℤ) : bodd (bit0 n) = false :=
  bodd_bit false n
#align int.bodd_bit0 Int.bodd_bit0
-/

#print Int.bodd_bit1 /-
@[simp]
theorem bodd_bit1 (n : ℤ) : bodd (bit1 n) = true :=
  bodd_bit true n
#align int.bodd_bit1 Int.bodd_bit1
-/

#print Int.bit0_ne_bit1 /-
theorem bit0_ne_bit1 (m n : ℤ) : bit0 m ≠ bit1 n :=
  mt (congr_arg bodd) <| by simp
#align int.bit0_ne_bit1 Int.bit0_ne_bit1
-/

#print Int.bit1_ne_bit0 /-
theorem bit1_ne_bit0 (m n : ℤ) : bit1 m ≠ bit0 n :=
  (bit0_ne_bit1 _ _).symm
#align int.bit1_ne_bit0 Int.bit1_ne_bit0
-/

#print Int.bit1_ne_zero /-
theorem bit1_ne_zero (m : ℤ) : bit1 m ≠ 0 := by simpa only [bit0_zero] using bit1_ne_bit0 m 0
#align int.bit1_ne_zero Int.bit1_ne_zero
-/

#print Int.testBit_zero /-
@[simp]
theorem testBit_zero (b) : ∀ n, testBit (bit b n) 0 = b
  | (n : ℕ) => by rw [bit_coe_nat] <;> apply Nat.testBit_zero
  | -[n+1] => by
    rw [bit_neg_succ] <;> dsimp [test_bit] <;> rw [Nat.testBit_zero] <;> clear test_bit_zero <;>
        cases b <;>
      rfl
#align int.test_bit_zero Int.testBit_zero
-/

#print Int.testBit_succ /-
@[simp]
theorem testBit_succ (m b) : ∀ n, testBit (bit b n) (Nat.succ m) = testBit n m
  | (n : ℕ) => by rw [bit_coe_nat] <;> apply Nat.testBit_succ
  | -[n+1] => by rw [bit_neg_succ] <;> dsimp [test_bit] <;> rw [Nat.testBit_succ]
#align int.test_bit_succ Int.testBit_succ
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:337:4: warning: unsupported (TODO): `[tacs] -/
private unsafe def bitwise_tac : tactic Unit :=
  sorry

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.1792841685.bitwise_tac -/
#print Int.bitwise_or /-
theorem bitwise_or : bitwise or = lor := by
  run_tac
    bitwise_tac
#align int.bitwise_or Int.bitwise_or
-/

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.1792841685.bitwise_tac -/
#print Int.bitwise_and /-
theorem bitwise_and : bitwise and = land := by
  run_tac
    bitwise_tac
#align int.bitwise_and Int.bitwise_and
-/

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.1792841685.bitwise_tac -/
#print Int.bitwise_diff /-
theorem bitwise_diff : (bitwise fun a b => a && not b) = ldiff' := by
  run_tac
    bitwise_tac
#align int.bitwise_diff Int.bitwise_diff
-/

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.1792841685.bitwise_tac -/
#print Int.bitwise_xor /-
theorem bitwise_xor : bitwise xor = lxor' := by
  run_tac
    bitwise_tac
#align int.bitwise_xor Int.bitwise_xor
-/

/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:508:27: warning: unsupported: unfold config -/
#print Int.bitwise_bit /-
@[simp]
theorem bitwise_bit (f : Bool → Bool → Bool) (a m b n) :
    bitwise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n) :=
  by
  cases' m with m m <;> cases' n with n n <;>
        repeat'
          first
          | rw [← Int.coe_nat_eq]
          | rw [bit_coe_nat]
          | rw [bit_neg_succ] <;>
      unfold bitwise nat_bitwise not <;>
    [induction' h : f ff ff with; induction' h : f ff tt with; induction' h : f tt ff with;
    induction' h : f tt tt with]
  all_goals
    unfold cond; rw [Nat.bitwise'_bit]
    repeat'
      first
      | rw [bit_coe_nat]
      | rw [bit_neg_succ]
      | rw [Bool.not_not]
  all_goals unfold not <;> rw [h] <;> rfl
#align int.bitwise_bit Int.bitwise_bit
-/

#print Int.lor_bit /-
@[simp]
theorem lor_bit (a m b n) : lor (bit a m) (bit b n) = bit (a || b) (lor m n) := by
  rw [← bitwise_or, bitwise_bit]
#align int.lor_bit Int.lor_bit
-/

#print Int.land_bit /-
@[simp]
theorem land_bit (a m b n) : land (bit a m) (bit b n) = bit (a && b) (land m n) := by
  rw [← bitwise_and, bitwise_bit]
#align int.land_bit Int.land_bit
-/

#print Int.ldiff_bit /-
@[simp]
theorem ldiff_bit (a m b n) : ldiff' (bit a m) (bit b n) = bit (a && not b) (ldiff' m n) := by
  rw [← bitwise_diff, bitwise_bit]
#align int.ldiff_bit Int.ldiff_bit
-/

#print Int.lxor_bit /-
@[simp]
theorem lxor_bit (a m b n) : lxor' (bit a m) (bit b n) = bit (xor a b) (lxor' m n) := by
  rw [← bitwise_xor, bitwise_bit]
#align int.lxor_bit Int.lxor_bit
-/

#print Int.lnot_bit /-
@[simp]
theorem lnot_bit (b) : ∀ n, lnot (bit b n) = bit (not b) (lnot n)
  | (n : ℕ) => by simp [lnot]
  | -[n+1] => by simp [lnot]
#align int.lnot_bit Int.lnot_bit
-/

#print Int.testBit_bitwise /-
@[simp]
theorem testBit_bitwise (f : Bool → Bool → Bool) (m n k) :
    testBit (bitwise f m n) k = f (testBit m k) (testBit n k) :=
  by
  induction' k with k IH generalizing m n <;> apply bit_cases_on m <;> intro a m' <;>
        apply bit_cases_on n <;>
      intro b n' <;>
    rw [bitwise_bit]
  · simp [test_bit_zero]
  · simp [test_bit_succ, IH]
#align int.test_bit_bitwise Int.testBit_bitwise
-/

#print Int.testBit_lor /-
@[simp]
theorem testBit_lor (m n k) : testBit (lor m n) k = (testBit m k || testBit n k) := by
  rw [← bitwise_or, test_bit_bitwise]
#align int.test_bit_lor Int.testBit_lor
-/

#print Int.testBit_land /-
@[simp]
theorem testBit_land (m n k) : testBit (land m n) k = (testBit m k && testBit n k) := by
  rw [← bitwise_and, test_bit_bitwise]
#align int.test_bit_land Int.testBit_land
-/

#print Int.testBit_ldiff /-
@[simp]
theorem testBit_ldiff (m n k) : testBit (ldiff' m n) k = (testBit m k && not (testBit n k)) := by
  rw [← bitwise_diff, test_bit_bitwise]
#align int.test_bit_ldiff Int.testBit_ldiff
-/

#print Int.testBit_lxor /-
@[simp]
theorem testBit_lxor (m n k) : testBit (lxor' m n) k = xor (testBit m k) (testBit n k) := by
  rw [← bitwise_xor, test_bit_bitwise]
#align int.test_bit_lxor Int.testBit_lxor
-/

#print Int.testBit_lnot /-
@[simp]
theorem testBit_lnot : ∀ n k, testBit (lnot n) k = not (testBit n k)
  | (n : ℕ), k => by simp [lnot, test_bit]
  | -[n+1], k => by simp [lnot, test_bit]
#align int.test_bit_lnot Int.testBit_lnot
-/

#print Int.shiftLeft_neg /-
@[simp]
theorem shiftLeft_neg (m n : ℤ) : shiftLeft m (-n) = shiftRight m n :=
  rfl
#align int.shiftl_neg Int.shiftLeft_neg
-/

#print Int.shiftRight_neg /-
@[simp]
theorem shiftRight_neg (m n : ℤ) : shiftRight m (-n) = shiftLeft m n := by
  rw [← shiftl_neg, neg_neg]
#align int.shiftr_neg Int.shiftRight_neg
-/

#print Int.shiftLeft_coe_nat /-
@[simp]
theorem shiftLeft_coe_nat (m n : ℕ) : shiftLeft m n = Nat.shiftl m n :=
  rfl
#align int.shiftl_coe_nat Int.shiftLeft_coe_nat
-/

#print Int.shiftRight_coe_nat /-
@[simp]
theorem shiftRight_coe_nat (m n : ℕ) : shiftRight m n = Nat.shiftr m n := by cases n <;> rfl
#align int.shiftr_coe_nat Int.shiftRight_coe_nat
-/

#print Int.shiftLeft_negSucc /-
@[simp]
theorem shiftLeft_negSucc (m n : ℕ) : shiftLeft -[m+1] n = -[Nat.shiftLeft' true m n+1] :=
  rfl
#align int.shiftl_neg_succ Int.shiftLeft_negSucc
-/

#print Int.shiftRight_negSucc /-
@[simp]
theorem shiftRight_negSucc (m n : ℕ) : shiftRight -[m+1] n = -[Nat.shiftr m n+1] := by
  cases n <;> rfl
#align int.shiftr_neg_succ Int.shiftRight_negSucc
-/

#print Int.shiftRight_add /-
theorem shiftRight_add : ∀ (m : ℤ) (n k : ℕ), shiftRight m (n + k) = shiftRight (shiftRight m n) k
  | (m : ℕ), n, k => by
    rw [shiftr_coe_nat, shiftr_coe_nat, ← Int.ofNat_add, shiftr_coe_nat, Nat.shiftr_add]
  | -[m+1], n, k => by
    rw [shiftr_neg_succ, shiftr_neg_succ, ← Int.ofNat_add, shiftr_neg_succ, Nat.shiftr_add]
#align int.shiftr_add Int.shiftRight_add
-/

/-! ### bitwise ops -/


attribute [local simp] Int.zero_div

#print Int.shiftLeft_add /-
theorem shiftLeft_add : ∀ (m : ℤ) (n : ℕ) (k : ℤ), shiftLeft m (n + k) = shiftLeft (shiftLeft m n) k
  | (m : ℕ), n, (k : ℕ) => congr_arg ofNat (Nat.shiftl_add _ _ _)
  | -[m+1], n, (k : ℕ) => congr_arg negSucc (Nat.shiftLeft'_add _ _ _ _)
  | (m : ℕ), n, -[k+1] =>
    subNatNat_elim n k.succ (fun n k i => shiftLeft (↑m) i = Nat.shiftr (Nat.shiftl m n) k)
      (fun i n =>
        congr_arg coe <| by rw [← Nat.shiftl_sub, add_tsub_cancel_left] <;> apply Nat.le_add_right)
      fun i n =>
      congr_arg coe <| by rw [add_assoc, Nat.shiftr_add, ← Nat.shiftl_sub, tsub_self] <;> rfl
  | -[m+1], n, -[k+1] =>
    subNatNat_elim n k.succ
      (fun n k i => shiftLeft -[m+1] i = -[Nat.shiftr (Nat.shiftLeft' true m n) k+1])
      (fun i n =>
        congr_arg negSucc <| by
          rw [← Nat.shiftLeft'_sub, add_tsub_cancel_left] <;> apply Nat.le_add_right)
      fun i n =>
      congr_arg negSucc <| by
        rw [add_assoc, Nat.shiftr_add, ← Nat.shiftLeft'_sub, tsub_self] <;> rfl
#align int.shiftl_add Int.shiftLeft_add
-/

#print Int.shiftLeft_sub /-
theorem shiftLeft_sub (m : ℤ) (n : ℕ) (k : ℤ) :
    shiftLeft m (n - k) = shiftRight (shiftLeft m n) k :=
  shiftLeft_add _ _ _
#align int.shiftl_sub Int.shiftLeft_sub
-/

#print Int.shiftLeft_eq_mul_pow /-
theorem shiftLeft_eq_mul_pow : ∀ (m : ℤ) (n : ℕ), shiftLeft m n = m * ↑(2 ^ n)
  | (m : ℕ), n => congr_arg coe (Nat.shiftLeft_eq_mul_pow _ _)
  | -[m+1], n => @congr_arg ℕ ℤ _ _ (fun i => -i) (Nat.shiftLeft'_tt_eq_mul_pow _ _)
#align int.shiftl_eq_mul_pow Int.shiftLeft_eq_mul_pow
-/

#print Int.shiftRight_eq_div_pow /-
theorem shiftRight_eq_div_pow : ∀ (m : ℤ) (n : ℕ), shiftRight m n = m / ↑(2 ^ n)
  | (m : ℕ), n => by rw [shiftr_coe_nat] <;> exact congr_arg coe (Nat.shiftRight_eq_div_pow _ _)
  | -[m+1], n =>
    by
    rw [shiftr_neg_succ, neg_succ_of_nat_div, Nat.shiftRight_eq_div_pow]; rfl
    exact coe_nat_lt_coe_nat_of_lt (pow_pos (by decide) _)
#align int.shiftr_eq_div_pow Int.shiftRight_eq_div_pow
-/

#print Int.one_shiftLeft /-
theorem one_shiftLeft (n : ℕ) : shiftLeft 1 n = (2 ^ n : ℕ) :=
  congr_arg coe (Nat.one_shiftLeft _)
#align int.one_shiftl Int.one_shiftLeft
-/

#print Int.zero_shiftLeft /-
@[simp]
theorem zero_shiftLeft : ∀ n : ℤ, shiftLeft 0 n = 0
  | (n : ℕ) => congr_arg coe (Nat.zero_shiftLeft _)
  | -[n+1] => congr_arg coe (Nat.zero_shiftr _)
#align int.zero_shiftl Int.zero_shiftLeft
-/

#print Int.zero_shiftRight /-
@[simp]
theorem zero_shiftRight (n) : shiftRight 0 n = 0 :=
  zero_shiftLeft _
#align int.zero_shiftr Int.zero_shiftRight
-/

end Int

