/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Data.Bitvec.Core
import Data.Fin.Basic
import Mathbin.Tactic.Monotonicity.Default
import Tactic.NormNum

#align_import data.bitvec.basic from "leanprover-community/mathlib"@"008af8bb14b3ebef7e04ec3b0d63b947dee4d26a"

namespace BitVec

instance (n : ℕ) : Preorder (BitVec n) :=
  Preorder.lift BitVec.toNat

#print BitVec.ofFin /-
/-- convert `fin` to `bitvec` -/
def ofFin {n : ℕ} (i : Fin <| 2 ^ n) : BitVec n :=
  BitVec.ofNat _ i.val
#align bitvec.of_fin BitVec.ofFin
-/

theorem ofFin_val {n : ℕ} (i : Fin <| 2 ^ n) : (ofFin i).toNat = i.val := by
  rw [of_fin, to_nat_of_nat, Nat.mod_eq_of_lt] <;> apply i.is_lt
#align bitvec.of_fin_val BitVec.ofFin_val

#print BitVec.toFin /-
/-- convert `bitvec` to `fin` -/
def toFin {n : ℕ} (i : BitVec n) : Fin <| 2 ^ n :=
  i.toNat
#align bitvec.to_fin BitVec.toFin
-/

theorem addLsb_eq_twice_add_one {x b} : addLsb x b = 2 * x + cond b 1 0 := by
  simp [add_lsb, two_mul]
#align bitvec.add_lsb_eq_twice_add_one BitVec.addLsb_eq_twice_add_one

theorem toNat_eq_foldr_reverse {n : ℕ} (v : BitVec n) :
    v.toNat = v.toList.reverse.foldr (flip addLsb) 0 := by rw [List.foldr_reverse, flip] <;> rfl
#align bitvec.to_nat_eq_foldr_reverse BitVec.toNat_eq_foldr_reverse

#print BitVec.toNat_lt /-
theorem toNat_lt {n : ℕ} (v : BitVec n) : v.toNat < 2 ^ n :=
  by
  suffices v.to_nat + 1 ≤ 2 ^ n by simpa
  rw [to_nat_eq_foldr_reverse]
  cases' v with xs h
  dsimp [BitVec.toNat, bits_to_nat]
  rw [← List.length_reverse] at h
  generalize xs.reverse = ys at h ⊢; clear xs
  induction ys generalizing n
  · simp [← h]
  · simp only [← h, pow_add, flip, List.length, List.foldr, pow_one]
    rw [add_lsb_eq_twice_add_one]
    trans 2 * List.foldr (fun (x : Bool) (y : ℕ) => add_lsb y x) 0 ys_tl + 2 * 1
    · ac_mono; rw [two_mul]; mono; cases ys_hd <;> simp
    · rw [← left_distrib]; ac_mono
      exact ys_ih rfl; norm_num
#align bitvec.to_nat_lt BitVec.toNat_lt
-/

theorem addLsb_div_two {x b} : addLsb x b / 2 = x := by
  cases b <;>
      simp only [Nat.add_mul_div_left, add_lsb, ← two_mul, add_comm, Nat.succ_pos',
        Nat.mul_div_right, gt_iff_lt, zero_add, cond] <;>
    norm_num
#align bitvec.add_lsb_div_two BitVec.addLsb_div_two

theorem decide_addLsb_mod_two {x b} : decide (addLsb x b % 2 = 1) = b := by
  cases b <;>
      simp only [Bool.decide_iff, Nat.add_mul_mod_self_left, add_lsb, ← two_mul, add_comm,
        decide_false_eq_false, Nat.mul_mod_right, zero_add, cond, zero_ne_one] <;>
    norm_num
#align bitvec.to_bool_add_lsb_mod_two BitVec.decide_addLsb_mod_two

#print BitVec.ofNat_toNat /-
theorem ofNat_toNat {n : ℕ} (v : BitVec n) : BitVec.ofNat _ v.toNat = v :=
  by
  cases' v with xs h
  ext1
  change Mathlib.Vector.toList _ = xs
  dsimp [BitVec.toNat, bits_to_nat]
  rw [← List.length_reverse] at h
  rw [← List.reverse_reverse xs, List.foldl_reverse]
  generalize xs.reverse = ys at h ⊢; clear xs
  induction ys generalizing n
  · cases h; simp [BitVec.ofNat]
  · simp only [← Nat.succ_eq_add_one, List.length] at h; subst n
    simp only [BitVec.ofNat, Mathlib.Vector.toList_cons, Mathlib.Vector.toList_nil,
      List.reverse_cons, Mathlib.Vector.toList_append, List.foldr]
    erw [add_lsb_div_two, to_bool_add_lsb_mod_two]
    congr; apply ys_ih; rfl
#align bitvec.of_nat_to_nat BitVec.ofNat_toNat
-/

theorem toFin_val {n : ℕ} (v : BitVec n) : (toFin v : ℕ) = v.toNat := by
  rw [to_fin, Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt] <;> apply to_nat_lt
#align bitvec.to_fin_val BitVec.toFin_val

theorem toFin_le_toFin_of_le {n} {v₀ v₁ : BitVec n} (h : v₀ ≤ v₁) : v₀.toFin ≤ v₁.toFin :=
  show (v₀.toFin : ℕ) ≤ v₁.toFin by rw [to_fin_val, to_fin_val] <;> exact h
#align bitvec.to_fin_le_to_fin_of_le BitVec.toFin_le_toFin_of_le

theorem ofFin_le_ofFin_of_le {n : ℕ} {i j : Fin (2 ^ n)} (h : i ≤ j) : ofFin i ≤ ofFin j :=
  show (BitVec.ofNat n i).toNat ≤ (BitVec.ofNat n j).toNat by
    simp only [to_nat_of_nat, Nat.mod_eq_of_lt, Fin.is_lt]; exact h
#align bitvec.of_fin_le_of_fin_of_le BitVec.ofFin_le_ofFin_of_le

theorem toFin_ofFin {n} (i : Fin <| 2 ^ n) : (ofFin i).toFin = i :=
  Fin.eq_of_veq (by simp [to_fin_val, of_fin, to_nat_of_nat, Nat.mod_eq_of_lt, i.is_lt])
#align bitvec.to_fin_of_fin BitVec.toFin_ofFin

theorem ofFin_toFin {n} (v : BitVec n) : ofFin (toFin v) = v := by
  dsimp [of_fin] <;> rw [to_fin_val, of_nat_to_nat]
#align bitvec.of_fin_to_fin BitVec.ofFin_toFin

end BitVec

