/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jeremy Avigad

! This file was ported from Lean 3 source module data.nat.dist
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Order.Basic

/-!
#  Distance function on ℕ

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines a simple distance function on naturals from truncated subtraction.
-/


namespace Nat

#print Nat.dist /-
/-- Distance (absolute value of difference) between natural numbers. -/
def dist (n m : ℕ) :=
  n - m + (m - n)
#align nat.dist Nat.dist
-/

#print Nat.dist.def /-
theorem dist.def (n m : ℕ) : dist n m = n - m + (m - n) :=
  rfl
#align nat.dist.def Nat.dist.def
-/

#print Nat.dist_comm /-
theorem dist_comm (n m : ℕ) : dist n m = dist m n := by simp [dist.def, add_comm]
#align nat.dist_comm Nat.dist_comm
-/

#print Nat.dist_self /-
@[simp]
theorem dist_self (n : ℕ) : dist n n = 0 := by simp [dist.def, tsub_self]
#align nat.dist_self Nat.dist_self
-/

#print Nat.eq_of_dist_eq_zero /-
theorem eq_of_dist_eq_zero {n m : ℕ} (h : dist n m = 0) : n = m :=
  have : n - m = 0 := Nat.eq_zero_of_add_eq_zero_right h
  have : n ≤ m := tsub_eq_zero_iff_le.mp this
  have : m - n = 0 := Nat.eq_zero_of_add_eq_zero_left h
  have : m ≤ n := tsub_eq_zero_iff_le.mp this
  le_antisymm ‹n ≤ m› ‹m ≤ n›
#align nat.eq_of_dist_eq_zero Nat.eq_of_dist_eq_zero
-/

#print Nat.dist_eq_zero /-
theorem dist_eq_zero {n m : ℕ} (h : n = m) : dist n m = 0 := by rw [h, dist_self]
#align nat.dist_eq_zero Nat.dist_eq_zero
-/

#print Nat.dist_eq_sub_of_le /-
theorem dist_eq_sub_of_le {n m : ℕ} (h : n ≤ m) : dist n m = m - n := by
  rw [dist.def, tsub_eq_zero_iff_le.mpr h, zero_add]
#align nat.dist_eq_sub_of_le Nat.dist_eq_sub_of_le
-/

#print Nat.dist_eq_sub_of_le_right /-
theorem dist_eq_sub_of_le_right {n m : ℕ} (h : m ≤ n) : dist n m = n - m := by rw [dist_comm];
  apply dist_eq_sub_of_le h
#align nat.dist_eq_sub_of_le_right Nat.dist_eq_sub_of_le_right
-/

#print Nat.dist_tri_left /-
theorem dist_tri_left (n m : ℕ) : m ≤ dist n m + n :=
  le_trans le_tsub_add (add_le_add_right (Nat.le_add_left _ _) _)
#align nat.dist_tri_left Nat.dist_tri_left
-/

#print Nat.dist_tri_right /-
theorem dist_tri_right (n m : ℕ) : m ≤ n + dist n m := by rw [add_comm] <;> apply dist_tri_left
#align nat.dist_tri_right Nat.dist_tri_right
-/

#print Nat.dist_tri_left' /-
theorem dist_tri_left' (n m : ℕ) : n ≤ dist n m + m := by rw [dist_comm] <;> apply dist_tri_left
#align nat.dist_tri_left' Nat.dist_tri_left'
-/

#print Nat.dist_tri_right' /-
theorem dist_tri_right' (n m : ℕ) : n ≤ m + dist n m := by rw [dist_comm] <;> apply dist_tri_right
#align nat.dist_tri_right' Nat.dist_tri_right'
-/

#print Nat.dist_zero_right /-
theorem dist_zero_right (n : ℕ) : dist n 0 = n :=
  Eq.trans (dist_eq_sub_of_le_right (zero_le n)) (tsub_zero n)
#align nat.dist_zero_right Nat.dist_zero_right
-/

#print Nat.dist_zero_left /-
theorem dist_zero_left (n : ℕ) : dist 0 n = n :=
  Eq.trans (dist_eq_sub_of_le (zero_le n)) (tsub_zero n)
#align nat.dist_zero_left Nat.dist_zero_left
-/

#print Nat.dist_add_add_right /-
theorem dist_add_add_right (n k m : ℕ) : dist (n + k) (m + k) = dist n m :=
  calc
    dist (n + k) (m + k) = n + k - (m + k) + (m + k - (n + k)) := rfl
    _ = n - m + (m + k - (n + k)) := by rw [add_tsub_add_eq_tsub_right]
    _ = n - m + (m - n) := by rw [add_tsub_add_eq_tsub_right]
    
#align nat.dist_add_add_right Nat.dist_add_add_right
-/

#print Nat.dist_add_add_left /-
theorem dist_add_add_left (k n m : ℕ) : dist (k + n) (k + m) = dist n m := by
  rw [add_comm k n, add_comm k m]; apply dist_add_add_right
#align nat.dist_add_add_left Nat.dist_add_add_left
-/

#print Nat.dist_eq_intro /-
theorem dist_eq_intro {n m k l : ℕ} (h : n + m = k + l) : dist n k = dist l m :=
  calc
    dist n k = dist (n + m) (k + m) := by rw [dist_add_add_right]
    _ = dist (k + l) (k + m) := by rw [h]
    _ = dist l m := by rw [dist_add_add_left]
    
#align nat.dist_eq_intro Nat.dist_eq_intro
-/

#print Nat.dist.triangle_inequality /-
theorem dist.triangle_inequality (n m k : ℕ) : dist n k ≤ dist n m + dist m k :=
  by
  have : dist n m + dist m k = n - m + (m - k) + (k - m + (m - n)) := by
    simp [dist.def, add_comm, add_left_comm]
  rw [this, dist.def]
  exact add_le_add tsub_le_tsub_add_tsub tsub_le_tsub_add_tsub
#align nat.dist.triangle_inequality Nat.dist.triangle_inequality
-/

#print Nat.dist_mul_right /-
theorem dist_mul_right (n k m : ℕ) : dist (n * k) (m * k) = dist n m * k := by
  rw [dist.def, dist.def, right_distrib, tsub_mul, tsub_mul]
#align nat.dist_mul_right Nat.dist_mul_right
-/

#print Nat.dist_mul_left /-
theorem dist_mul_left (k n m : ℕ) : dist (k * n) (k * m) = k * dist n m := by
  rw [mul_comm k n, mul_comm k m, dist_mul_right, mul_comm]
#align nat.dist_mul_left Nat.dist_mul_left
-/

#print Nat.dist_succ_succ /-
-- TODO(Jeremy): do when we have max and minx
--theorem dist_eq_max_sub_min {i j : nat} : dist i j = (max i j) - min i j :=
--sorry
/-
or.elim (lt_or_ge i j)
  (assume : i < j,
    by rw [max_eq_right_of_lt this, min_eq_left_of_lt this, dist_eq_sub_of_lt this])
  (assume : i ≥ j,
    by rw [max_eq_left this , min_eq_right this, dist_eq_sub_of_le_right this])
-/
theorem dist_succ_succ {i j : Nat} : dist (succ i) (succ j) = dist i j := by
  simp [dist.def, succ_sub_succ]
#align nat.dist_succ_succ Nat.dist_succ_succ
-/

#print Nat.dist_pos_of_ne /-
theorem dist_pos_of_ne {i j : Nat} : i ≠ j → 0 < dist i j := fun hne =>
  Nat.ltByCases
    (fun this : i < j => by rw [dist_eq_sub_of_le (le_of_lt this)]; apply tsub_pos_of_lt this)
    (fun this : i = j => by contradiction) fun this : i > j => by
    rw [dist_eq_sub_of_le_right (le_of_lt this)]; apply tsub_pos_of_lt this
#align nat.dist_pos_of_ne Nat.dist_pos_of_ne
-/

end Nat

