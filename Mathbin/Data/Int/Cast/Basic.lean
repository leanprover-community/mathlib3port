/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner

! This file was ported from Lean 3 source module data.int.cast.basic
! leanprover-community/mathlib commit 448144f7ae193a8990cb7473c9e9a01990f64ac7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Int.Cast.Defs
import Mathbin.Algebra.Group.Basic

/-!
# Cast of integers (additional theorems)

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves additional properties about the *canonical* homomorphism from
the integers into an additive group with a one (`int.cast`).

There is also `data.int.cast.lemmas`,
which includes lemmas stated in terms of algebraic homomorphisms,
and results involving the order structure of `ℤ`.

By contrast, this file's only import beyond `data.int.cast.defs` is `algebra.group.basic`.
-/


universe u

namespace Nat

variable {R : Type u} [AddGroupWithOne R]

@[simp, norm_cast]
theorem cast_sub {m n} (h : m ≤ n) : ((n - m : ℕ) : R) = n - m :=
  eq_sub_of_add_eq <| by rw [← cast_add, Nat.sub_add_cancel h]
#align nat.cast_sub Nat.cast_subₓ

@[simp, norm_cast]
theorem cast_pred : ∀ {n}, 0 < n → ((n - 1 : ℕ) : R) = n - 1
  | 0, h => by cases h
  | n + 1, h => by rw [cast_succ, add_sub_cancel] <;> rfl
#align nat.cast_pred Nat.cast_pred

end Nat

open Nat

namespace Int

variable {R : Type u} [AddGroupWithOne R]

@[simp]
theorem cast_negSucc (n : ℕ) : (-[n+1] : R) = -(n + 1 : ℕ) :=
  AddGroupWithOne.intCast_negSucc n
#align int.cast_neg_succ_of_nat Int.cast_negSuccₓ

@[simp, norm_cast]
theorem cast_zero : ((0 : ℤ) : R) = 0 :=
  (cast_ofNat 0).trans Nat.cast_zero
#align int.cast_zero Int.cast_zeroₓ

@[simp, norm_cast]
theorem cast_ofNat (n : ℕ) : ((n : ℤ) : R) = n :=
  cast_ofNat _
#align int.cast_coe_nat Int.cast_ofNatₓ

@[simp, norm_cast]
theorem cast_one : ((1 : ℤ) : R) = 1 :=
  show (((1 : ℕ) : ℤ) : R) = 1 by simp
#align int.cast_one Int.cast_oneₓ

@[simp, norm_cast]
theorem cast_neg : ∀ n, ((-n : ℤ) : R) = -n
  | (0 : ℕ) => by erw [cast_zero, neg_zero]
  | (n + 1 : ℕ) => by erw [cast_of_nat, cast_neg_succ_of_nat] <;> rfl
  | -[n+1] => by erw [cast_of_nat, cast_neg_succ_of_nat, neg_neg]
#align int.cast_neg Int.cast_negₓ

@[simp]
theorem cast_subNatNat (m n) : ((Int.subNatNat m n : ℤ) : R) = m - n :=
  by
  unfold sub_nat_nat; cases e : n - m
  · simp only [sub_nat_nat, cast_of_nat]; simp [e, Nat.le_of_sub_eq_zero e]
  ·
    rw [sub_nat_nat, cast_neg_succ_of_nat, Nat.add_one, ← e,
      Nat.cast_sub <| _root_.le_of_lt <| Nat.lt_of_sub_eq_succ e, neg_sub]
#align int.cast_sub_nat_nat Int.cast_subNatNatₓ

#print Int.negOfNat_eq /-
theorem negOfNat_eq (n : ℕ) : negOfNat n = -(n : ℤ) := by cases n <;> rfl
#align int.neg_of_nat_eq Int.negOfNat_eq
-/

@[simp]
theorem cast_negOfNat (n : ℕ) : ((negOfNat n : ℤ) : R) = -n := by simp [neg_of_nat_eq]
#align int.cast_neg_of_nat Int.cast_negOfNat

@[simp, norm_cast]
theorem cast_add : ∀ m n, ((m + n : ℤ) : R) = m + n
  | (m : ℕ), (n : ℕ) => by simp [← Int.ofNat_add]
  | (m : ℕ), -[n+1] => by erw [cast_sub_nat_nat, cast_coe_nat, cast_neg_succ_of_nat, sub_eq_add_neg]
  | -[m+1], (n : ℕ) => by
    erw [cast_sub_nat_nat, cast_coe_nat, cast_neg_succ_of_nat, sub_eq_iff_eq_add, add_assoc,
      eq_neg_add_iff_add_eq, ← Nat.cast_add, ← Nat.cast_add, Nat.add_comm]
  | -[m+1], -[n+1] =>
    show (-[m + n + 1+1] : R) = _ by
      rw [cast_neg_succ_of_nat, cast_neg_succ_of_nat, cast_neg_succ_of_nat, ← neg_add_rev, ←
        Nat.cast_add, Nat.add_right_comm m n 1, Nat.add_assoc, Nat.add_comm]
#align int.cast_add Int.cast_addₓ

@[simp, norm_cast]
theorem cast_sub (m n) : ((m - n : ℤ) : R) = m - n := by simp [Int.sub_eq_add_neg, sub_eq_add_neg]
#align int.cast_sub Int.cast_subₓ

#print Int.ofNat_bit0 /-
@[simp, norm_cast]
theorem ofNat_bit0 (n : ℕ) : (↑(bit0 n) : ℤ) = bit0 ↑n :=
  rfl
#align int.coe_nat_bit0 Int.ofNat_bit0
-/

#print Int.ofNat_bit1 /-
@[simp, norm_cast]
theorem ofNat_bit1 (n : ℕ) : (↑(bit1 n) : ℤ) = bit1 ↑n :=
  rfl
#align int.coe_nat_bit1 Int.ofNat_bit1
-/

@[simp, norm_cast]
theorem cast_bit0 (n : ℤ) : ((bit0 n : ℤ) : R) = bit0 n :=
  cast_add _ _
#align int.cast_bit0 Int.cast_bit0

@[simp, norm_cast]
theorem cast_bit1 (n : ℤ) : ((bit1 n : ℤ) : R) = bit1 n := by
  rw [bit1, cast_add, cast_one, cast_bit0] <;> rfl
#align int.cast_bit1 Int.cast_bit1

theorem cast_two : ((2 : ℤ) : R) = 2 := by simp
#align int.cast_two Int.cast_two

theorem cast_three : ((3 : ℤ) : R) = 3 := by simp
#align int.cast_three Int.cast_three

theorem cast_four : ((4 : ℤ) : R) = 4 := by simp
#align int.cast_four Int.cast_four

end Int

