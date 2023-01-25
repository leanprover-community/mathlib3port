/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

! This file was ported from Lean 3 source module data.nat.gcd.basic
! leanprover-community/mathlib commit e3d9ab8faa9dea8f78155c6c27d62a621f4c152d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GroupPower.Basic
import Mathbin.Algebra.GroupWithZero.Divisibility
import Mathbin.Data.Nat.Order.Lemmas

/-!
# Definitions and properties of `nat.gcd`, `nat.lcm`, and `nat.coprime`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Generalizations of these are provided in a later file as `gcd_monoid.gcd` and
`gcd_monoid.lcm`.

Note that the global `is_coprime` is not a straightforward generalization of `nat.coprime`, see
`nat.is_coprime_iff_coprime` for the connection between the two.

-/


namespace Nat

/-! ### `gcd` -/


#print Nat.gcd_dvd /-
theorem gcd_dvd (m n : ℕ) : gcd m n ∣ m ∧ gcd m n ∣ n :=
  gcd.induction m n (fun n => by rw [gcd_zero_left] <;> exact ⟨dvd_zero n, dvd_refl n⟩)
    fun m n npos => by rw [← gcd_rec] <;> exact fun ⟨IH₁, IH₂⟩ => ⟨IH₂, (dvd_mod_iff IH₂).1 IH₁⟩
#align nat.gcd_dvd Nat.gcd_dvd
-/

#print Nat.gcd_dvd_left /-
theorem gcd_dvd_left (m n : ℕ) : gcd m n ∣ m :=
  (gcd_dvd m n).left
#align nat.gcd_dvd_left Nat.gcd_dvd_left
-/

#print Nat.gcd_dvd_right /-
theorem gcd_dvd_right (m n : ℕ) : gcd m n ∣ n :=
  (gcd_dvd m n).right
#align nat.gcd_dvd_right Nat.gcd_dvd_right
-/

#print Nat.gcd_le_left /-
theorem gcd_le_left {m} (n) (h : 0 < m) : gcd m n ≤ m :=
  le_of_dvd h <| gcd_dvd_left m n
#align nat.gcd_le_left Nat.gcd_le_left
-/

#print Nat.gcd_le_right /-
theorem gcd_le_right (m) {n} (h : 0 < n) : gcd m n ≤ n :=
  le_of_dvd h <| gcd_dvd_right m n
#align nat.gcd_le_right Nat.gcd_le_right
-/

/- warning: nat.dvd_gcd -> Nat.dvd_gcd is a dubious translation:
lean 3 declaration is
  forall {m : Nat} {n : Nat} {k : Nat}, (Dvd.Dvd.{0} Nat Nat.hasDvd k m) -> (Dvd.Dvd.{0} Nat Nat.hasDvd k n) -> (Dvd.Dvd.{0} Nat Nat.hasDvd k (Nat.gcd m n))
but is expected to have type
  forall {m : Nat} {n : Nat} {k : Nat}, (Dvd.dvd.{0} Nat Nat.instDvdNat m n) -> (Dvd.dvd.{0} Nat Nat.instDvdNat m k) -> (Dvd.dvd.{0} Nat Nat.instDvdNat m (Nat.gcd n k))
Case conversion may be inaccurate. Consider using '#align nat.dvd_gcd Nat.dvd_gcdₓ'. -/
theorem dvd_gcd {m n k : ℕ} : k ∣ m → k ∣ n → k ∣ gcd m n :=
  gcd.induction m n (fun n _ kn => by rw [gcd_zero_left] <;> exact kn) fun n m mpos IH H1 H2 => by
    rw [gcd_rec] <;> exact IH ((dvd_mod_iff H1).2 H2) H1
#align nat.dvd_gcd Nat.dvd_gcd

/- warning: nat.dvd_gcd_iff -> Nat.dvd_gcd_iff is a dubious translation:
lean 3 declaration is
  forall {m : Nat} {n : Nat} {k : Nat}, Iff (Dvd.Dvd.{0} Nat Nat.hasDvd k (Nat.gcd m n)) (And (Dvd.Dvd.{0} Nat Nat.hasDvd k m) (Dvd.Dvd.{0} Nat Nat.hasDvd k n))
but is expected to have type
  forall {m : Nat} {n : [mdata borrowed:1 Nat]} {k : [mdata borrowed:1 Nat]}, Iff (Dvd.dvd.{0} Nat Nat.instDvdNat m (Nat.gcd n k)) (And (Dvd.dvd.{0} Nat Nat.instDvdNat m n) (Dvd.dvd.{0} Nat Nat.instDvdNat m k))
Case conversion may be inaccurate. Consider using '#align nat.dvd_gcd_iff Nat.dvd_gcd_iffₓ'. -/
theorem dvd_gcd_iff {m n k : ℕ} : k ∣ gcd m n ↔ k ∣ m ∧ k ∣ n :=
  Iff.intro (fun h => ⟨h.trans (gcd_dvd m n).left, h.trans (gcd_dvd m n).right⟩) fun h =>
    dvd_gcd h.left h.right
#align nat.dvd_gcd_iff Nat.dvd_gcd_iff

#print Nat.gcd_comm /-
theorem gcd_comm (m n : ℕ) : gcd m n = gcd n m :=
  dvd_antisymm (dvd_gcd (gcd_dvd_right m n) (gcd_dvd_left m n))
    (dvd_gcd (gcd_dvd_right n m) (gcd_dvd_left n m))
#align nat.gcd_comm Nat.gcd_comm
-/

#print Nat.gcd_eq_left_iff_dvd /-
theorem gcd_eq_left_iff_dvd {m n : ℕ} : m ∣ n ↔ gcd m n = m :=
  ⟨fun h => by rw [gcd_rec, mod_eq_zero_of_dvd h, gcd_zero_left], fun h => h ▸ gcd_dvd_right m n⟩
#align nat.gcd_eq_left_iff_dvd Nat.gcd_eq_left_iff_dvd
-/

#print Nat.gcd_eq_right_iff_dvd /-
theorem gcd_eq_right_iff_dvd {m n : ℕ} : m ∣ n ↔ gcd n m = m := by
  rw [gcd_comm] <;> apply gcd_eq_left_iff_dvd
#align nat.gcd_eq_right_iff_dvd Nat.gcd_eq_right_iff_dvd
-/

#print Nat.gcd_assoc /-
theorem gcd_assoc (m n k : ℕ) : gcd (gcd m n) k = gcd m (gcd n k) :=
  dvd_antisymm
    (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_left m n))
      (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_right m n)) (gcd_dvd_right (gcd m n) k)))
    (dvd_gcd
      (dvd_gcd (gcd_dvd_left m (gcd n k)) ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_left n k)))
      ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_right n k)))
#align nat.gcd_assoc Nat.gcd_assoc
-/

#print Nat.gcd_one_right /-
@[simp]
theorem gcd_one_right (n : ℕ) : gcd n 1 = 1 :=
  Eq.trans (gcd_comm n 1) <| gcd_one_left n
#align nat.gcd_one_right Nat.gcd_one_right
-/

#print Nat.gcd_mul_left /-
theorem gcd_mul_left (m n k : ℕ) : gcd (m * n) (m * k) = m * gcd n k :=
  gcd.induction n k (fun k => by repeat' first |rw [mul_zero]|rw [gcd_zero_left]) fun k n H IH => by
    rwa [← mul_mod_mul_left, ← gcd_rec, ← gcd_rec] at IH
#align nat.gcd_mul_left Nat.gcd_mul_left
-/

#print Nat.gcd_mul_right /-
theorem gcd_mul_right (m n k : ℕ) : gcd (m * n) (k * n) = gcd m k * n := by
  rw [mul_comm m n, mul_comm k n, mul_comm (gcd m k) n, gcd_mul_left]
#align nat.gcd_mul_right Nat.gcd_mul_right
-/

#print Nat.gcd_pos_of_pos_left /-
theorem gcd_pos_of_pos_left {m : ℕ} (n : ℕ) (mpos : 0 < m) : 0 < gcd m n :=
  pos_of_dvd_of_pos (gcd_dvd_left m n) mpos
#align nat.gcd_pos_of_pos_left Nat.gcd_pos_of_pos_left
-/

#print Nat.gcd_pos_of_pos_right /-
theorem gcd_pos_of_pos_right (m : ℕ) {n : ℕ} (npos : 0 < n) : 0 < gcd m n :=
  pos_of_dvd_of_pos (gcd_dvd_right m n) npos
#align nat.gcd_pos_of_pos_right Nat.gcd_pos_of_pos_right
-/

#print Nat.eq_zero_of_gcd_eq_zero_left /-
theorem eq_zero_of_gcd_eq_zero_left {m n : ℕ} (H : gcd m n = 0) : m = 0 :=
  Or.elim (Nat.eq_zero_or_pos m) id fun H1 : 0 < m =>
    absurd (Eq.symm H) (ne_of_lt (gcd_pos_of_pos_left _ H1))
#align nat.eq_zero_of_gcd_eq_zero_left Nat.eq_zero_of_gcd_eq_zero_left
-/

#print Nat.eq_zero_of_gcd_eq_zero_right /-
theorem eq_zero_of_gcd_eq_zero_right {m n : ℕ} (H : gcd m n = 0) : n = 0 := by
  rw [gcd_comm] at H <;> exact eq_zero_of_gcd_eq_zero_left H
#align nat.eq_zero_of_gcd_eq_zero_right Nat.eq_zero_of_gcd_eq_zero_right
-/

#print Nat.gcd_eq_zero_iff /-
@[simp]
theorem gcd_eq_zero_iff {i j : ℕ} : gcd i j = 0 ↔ i = 0 ∧ j = 0 :=
  by
  constructor
  · intro h
    exact ⟨eq_zero_of_gcd_eq_zero_left h, eq_zero_of_gcd_eq_zero_right h⟩
  · rintro ⟨rfl, rfl⟩
    exact Nat.gcd_zero_right 0
#align nat.gcd_eq_zero_iff Nat.gcd_eq_zero_iff
-/

#print Nat.gcd_div /-
theorem gcd_div {m n k : ℕ} (H1 : k ∣ m) (H2 : k ∣ n) : gcd (m / k) (n / k) = gcd m n / k :=
  (Decidable.eq_or_ne k 0).elim
    (fun k0 => by rw [k0, Nat.div_zero, Nat.div_zero, Nat.div_zero, gcd_zero_right]) fun H3 =>
    mul_right_cancel₀ H3 <| by
      rw [Nat.div_mul_cancel (dvd_gcd H1 H2), ← gcd_mul_right, Nat.div_mul_cancel H1,
        Nat.div_mul_cancel H2]
#align nat.gcd_div Nat.gcd_div
-/

#print Nat.gcd_greatest /-
theorem gcd_greatest {a b d : ℕ} (hda : d ∣ a) (hdb : d ∣ b) (hd : ∀ e : ℕ, e ∣ a → e ∣ b → e ∣ d) :
    d = a.gcd b :=
  (dvd_antisymm (hd _ (gcd_dvd_left a b) (gcd_dvd_right a b)) (dvd_gcd hda hdb)).symm
#align nat.gcd_greatest Nat.gcd_greatest
-/

#print Nat.gcd_dvd_gcd_of_dvd_left /-
theorem gcd_dvd_gcd_of_dvd_left {m k : ℕ} (n : ℕ) (H : m ∣ k) : gcd m n ∣ gcd k n :=
  dvd_gcd ((gcd_dvd_left m n).trans H) (gcd_dvd_right m n)
#align nat.gcd_dvd_gcd_of_dvd_left Nat.gcd_dvd_gcd_of_dvd_left
-/

#print Nat.gcd_dvd_gcd_of_dvd_right /-
theorem gcd_dvd_gcd_of_dvd_right {m k : ℕ} (n : ℕ) (H : m ∣ k) : gcd n m ∣ gcd n k :=
  dvd_gcd (gcd_dvd_left n m) ((gcd_dvd_right n m).trans H)
#align nat.gcd_dvd_gcd_of_dvd_right Nat.gcd_dvd_gcd_of_dvd_right
-/

#print Nat.gcd_dvd_gcd_mul_left /-
theorem gcd_dvd_gcd_mul_left (m n k : ℕ) : gcd m n ∣ gcd (k * m) n :=
  gcd_dvd_gcd_of_dvd_left _ (dvd_mul_left _ _)
#align nat.gcd_dvd_gcd_mul_left Nat.gcd_dvd_gcd_mul_left
-/

#print Nat.gcd_dvd_gcd_mul_right /-
theorem gcd_dvd_gcd_mul_right (m n k : ℕ) : gcd m n ∣ gcd (m * k) n :=
  gcd_dvd_gcd_of_dvd_left _ (dvd_mul_right _ _)
#align nat.gcd_dvd_gcd_mul_right Nat.gcd_dvd_gcd_mul_right
-/

#print Nat.gcd_dvd_gcd_mul_left_right /-
theorem gcd_dvd_gcd_mul_left_right (m n k : ℕ) : gcd m n ∣ gcd m (k * n) :=
  gcd_dvd_gcd_of_dvd_right _ (dvd_mul_left _ _)
#align nat.gcd_dvd_gcd_mul_left_right Nat.gcd_dvd_gcd_mul_left_right
-/

#print Nat.gcd_dvd_gcd_mul_right_right /-
theorem gcd_dvd_gcd_mul_right_right (m n k : ℕ) : gcd m n ∣ gcd m (n * k) :=
  gcd_dvd_gcd_of_dvd_right _ (dvd_mul_right _ _)
#align nat.gcd_dvd_gcd_mul_right_right Nat.gcd_dvd_gcd_mul_right_right
-/

#print Nat.gcd_eq_left /-
theorem gcd_eq_left {m n : ℕ} (H : m ∣ n) : gcd m n = m :=
  dvd_antisymm (gcd_dvd_left _ _) (dvd_gcd dvd_rfl H)
#align nat.gcd_eq_left Nat.gcd_eq_left
-/

#print Nat.gcd_eq_right /-
theorem gcd_eq_right {m n : ℕ} (H : n ∣ m) : gcd m n = n := by rw [gcd_comm, gcd_eq_left H]
#align nat.gcd_eq_right Nat.gcd_eq_right
-/

#print Nat.gcd_mul_left_left /-
-- Lemmas where one argument is a multiple of the other
@[simp]
theorem gcd_mul_left_left (m n : ℕ) : gcd (m * n) n = n :=
  dvd_antisymm (gcd_dvd_right _ _) (dvd_gcd (dvd_mul_left _ _) dvd_rfl)
#align nat.gcd_mul_left_left Nat.gcd_mul_left_left
-/

#print Nat.gcd_mul_left_right /-
@[simp]
theorem gcd_mul_left_right (m n : ℕ) : gcd n (m * n) = n := by rw [gcd_comm, gcd_mul_left_left]
#align nat.gcd_mul_left_right Nat.gcd_mul_left_right
-/

#print Nat.gcd_mul_right_left /-
@[simp]
theorem gcd_mul_right_left (m n : ℕ) : gcd (n * m) n = n := by rw [mul_comm, gcd_mul_left_left]
#align nat.gcd_mul_right_left Nat.gcd_mul_right_left
-/

#print Nat.gcd_mul_right_right /-
@[simp]
theorem gcd_mul_right_right (m n : ℕ) : gcd n (n * m) = n := by rw [gcd_comm, gcd_mul_right_left]
#align nat.gcd_mul_right_right Nat.gcd_mul_right_right
-/

#print Nat.gcd_gcd_self_right_left /-
-- Lemmas for repeated application of `gcd`
@[simp]
theorem gcd_gcd_self_right_left (m n : ℕ) : gcd m (gcd m n) = gcd m n :=
  dvd_antisymm (gcd_dvd_right _ _) (dvd_gcd (gcd_dvd_left _ _) dvd_rfl)
#align nat.gcd_gcd_self_right_left Nat.gcd_gcd_self_right_left
-/

#print Nat.gcd_gcd_self_right_right /-
@[simp]
theorem gcd_gcd_self_right_right (m n : ℕ) : gcd m (gcd n m) = gcd n m := by
  rw [gcd_comm n m, gcd_gcd_self_right_left]
#align nat.gcd_gcd_self_right_right Nat.gcd_gcd_self_right_right
-/

#print Nat.gcd_gcd_self_left_right /-
@[simp]
theorem gcd_gcd_self_left_right (m n : ℕ) : gcd (gcd n m) m = gcd n m := by
  rw [gcd_comm, gcd_gcd_self_right_right]
#align nat.gcd_gcd_self_left_right Nat.gcd_gcd_self_left_right
-/

#print Nat.gcd_gcd_self_left_left /-
@[simp]
theorem gcd_gcd_self_left_left (m n : ℕ) : gcd (gcd m n) m = gcd m n := by
  rw [gcd_comm m n, gcd_gcd_self_left_right]
#align nat.gcd_gcd_self_left_left Nat.gcd_gcd_self_left_left
-/

#print Nat.gcd_add_mul_right_right /-
-- Lemmas where one argument consists of addition of a multiple of the other
@[simp]
theorem gcd_add_mul_right_right (m n k : ℕ) : gcd m (n + k * m) = gcd m n := by
  simp [gcd_rec m (n + k * m), gcd_rec m n]
#align nat.gcd_add_mul_right_right Nat.gcd_add_mul_right_right
-/

#print Nat.gcd_add_mul_left_right /-
@[simp]
theorem gcd_add_mul_left_right (m n k : ℕ) : gcd m (n + m * k) = gcd m n := by
  simp [gcd_rec m (n + m * k), gcd_rec m n]
#align nat.gcd_add_mul_left_right Nat.gcd_add_mul_left_right
-/

#print Nat.gcd_mul_right_add_right /-
@[simp]
theorem gcd_mul_right_add_right (m n k : ℕ) : gcd m (k * m + n) = gcd m n := by simp [add_comm _ n]
#align nat.gcd_mul_right_add_right Nat.gcd_mul_right_add_right
-/

#print Nat.gcd_mul_left_add_right /-
@[simp]
theorem gcd_mul_left_add_right (m n k : ℕ) : gcd m (m * k + n) = gcd m n := by simp [add_comm _ n]
#align nat.gcd_mul_left_add_right Nat.gcd_mul_left_add_right
-/

#print Nat.gcd_add_mul_right_left /-
@[simp]
theorem gcd_add_mul_right_left (m n k : ℕ) : gcd (m + k * n) n = gcd m n := by
  rw [gcd_comm, gcd_add_mul_right_right, gcd_comm]
#align nat.gcd_add_mul_right_left Nat.gcd_add_mul_right_left
-/

#print Nat.gcd_add_mul_left_left /-
@[simp]
theorem gcd_add_mul_left_left (m n k : ℕ) : gcd (m + n * k) n = gcd m n := by
  rw [gcd_comm, gcd_add_mul_left_right, gcd_comm]
#align nat.gcd_add_mul_left_left Nat.gcd_add_mul_left_left
-/

#print Nat.gcd_mul_right_add_left /-
@[simp]
theorem gcd_mul_right_add_left (m n k : ℕ) : gcd (k * n + m) n = gcd m n := by
  rw [gcd_comm, gcd_mul_right_add_right, gcd_comm]
#align nat.gcd_mul_right_add_left Nat.gcd_mul_right_add_left
-/

#print Nat.gcd_mul_left_add_left /-
@[simp]
theorem gcd_mul_left_add_left (m n k : ℕ) : gcd (n * k + m) n = gcd m n := by
  rw [gcd_comm, gcd_mul_left_add_right, gcd_comm]
#align nat.gcd_mul_left_add_left Nat.gcd_mul_left_add_left
-/

#print Nat.gcd_add_self_right /-
-- Lemmas where one argument consists of an addition of the other
@[simp]
theorem gcd_add_self_right (m n : ℕ) : gcd m (n + m) = gcd m n :=
  Eq.trans (by rw [one_mul]) (gcd_add_mul_right_right m n 1)
#align nat.gcd_add_self_right Nat.gcd_add_self_right
-/

#print Nat.gcd_add_self_left /-
@[simp]
theorem gcd_add_self_left (m n : ℕ) : gcd (m + n) n = gcd m n := by
  rw [gcd_comm, gcd_add_self_right, gcd_comm]
#align nat.gcd_add_self_left Nat.gcd_add_self_left
-/

#print Nat.gcd_self_add_left /-
@[simp]
theorem gcd_self_add_left (m n : ℕ) : gcd (m + n) m = gcd n m := by rw [add_comm, gcd_add_self_left]
#align nat.gcd_self_add_left Nat.gcd_self_add_left
-/

#print Nat.gcd_self_add_right /-
@[simp]
theorem gcd_self_add_right (m n : ℕ) : gcd m (m + n) = gcd m n := by
  rw [add_comm, gcd_add_self_right]
#align nat.gcd_self_add_right Nat.gcd_self_add_right
-/

/-! ### `lcm` -/


#print Nat.lcm_comm /-
theorem lcm_comm (m n : ℕ) : lcm m n = lcm n m := by delta lcm <;> rw [mul_comm, gcd_comm]
#align nat.lcm_comm Nat.lcm_comm
-/

#print Nat.lcm_zero_left /-
@[simp]
theorem lcm_zero_left (m : ℕ) : lcm 0 m = 0 := by delta lcm <;> rw [zero_mul, Nat.zero_div]
#align nat.lcm_zero_left Nat.lcm_zero_left
-/

#print Nat.lcm_zero_right /-
@[simp]
theorem lcm_zero_right (m : ℕ) : lcm m 0 = 0 :=
  lcm_comm 0 m ▸ lcm_zero_left m
#align nat.lcm_zero_right Nat.lcm_zero_right
-/

#print Nat.lcm_one_left /-
@[simp]
theorem lcm_one_left (m : ℕ) : lcm 1 m = m := by
  delta lcm <;> rw [one_mul, gcd_one_left, Nat.div_one]
#align nat.lcm_one_left Nat.lcm_one_left
-/

#print Nat.lcm_one_right /-
@[simp]
theorem lcm_one_right (m : ℕ) : lcm m 1 = m :=
  lcm_comm 1 m ▸ lcm_one_left m
#align nat.lcm_one_right Nat.lcm_one_right
-/

#print Nat.lcm_self /-
@[simp]
theorem lcm_self (m : ℕ) : lcm m m = m :=
  Or.elim (Nat.eq_zero_or_pos m) (fun h => by rw [h, lcm_zero_left]) fun h => by
    delta lcm <;> rw [gcd_self, Nat.mul_div_cancel _ h]
#align nat.lcm_self Nat.lcm_self
-/

#print Nat.dvd_lcm_left /-
theorem dvd_lcm_left (m n : ℕ) : m ∣ lcm m n :=
  Dvd.intro (n / gcd m n) (Nat.mul_div_assoc _ <| gcd_dvd_right m n).symm
#align nat.dvd_lcm_left Nat.dvd_lcm_left
-/

#print Nat.dvd_lcm_right /-
theorem dvd_lcm_right (m n : ℕ) : n ∣ lcm m n :=
  lcm_comm n m ▸ dvd_lcm_left n m
#align nat.dvd_lcm_right Nat.dvd_lcm_right
-/

#print Nat.gcd_mul_lcm /-
theorem gcd_mul_lcm (m n : ℕ) : gcd m n * lcm m n = m * n := by
  delta lcm <;> rw [Nat.mul_div_cancel' ((gcd_dvd_left m n).trans (dvd_mul_right m n))]
#align nat.gcd_mul_lcm Nat.gcd_mul_lcm
-/

#print Nat.lcm_dvd /-
theorem lcm_dvd {m n k : ℕ} (H1 : m ∣ k) (H2 : n ∣ k) : lcm m n ∣ k :=
  Or.elim (Nat.eq_zero_or_pos k) (fun h => by rw [h] <;> exact dvd_zero _) fun kpos =>
    dvd_of_mul_dvd_mul_left (gcd_pos_of_pos_left n (pos_of_dvd_of_pos H1 kpos)) <| by
      rw [gcd_mul_lcm, ← gcd_mul_right, mul_comm n k] <;>
        exact dvd_gcd (mul_dvd_mul_left _ H2) (mul_dvd_mul_right H1 _)
#align nat.lcm_dvd Nat.lcm_dvd
-/

#print Nat.lcm_dvd_mul /-
theorem lcm_dvd_mul (m n : ℕ) : lcm m n ∣ m * n :=
  lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _)
#align nat.lcm_dvd_mul Nat.lcm_dvd_mul
-/

#print Nat.lcm_dvd_iff /-
theorem lcm_dvd_iff {m n k : ℕ} : lcm m n ∣ k ↔ m ∣ k ∧ n ∣ k :=
  ⟨fun h => ⟨(dvd_lcm_left _ _).trans h, (dvd_lcm_right _ _).trans h⟩, and_imp.2 lcm_dvd⟩
#align nat.lcm_dvd_iff Nat.lcm_dvd_iff
-/

#print Nat.lcm_assoc /-
theorem lcm_assoc (m n k : ℕ) : lcm (lcm m n) k = lcm m (lcm n k) :=
  dvd_antisymm
    (lcm_dvd
      (lcm_dvd (dvd_lcm_left m (lcm n k)) ((dvd_lcm_left n k).trans (dvd_lcm_right m (lcm n k))))
      ((dvd_lcm_right n k).trans (dvd_lcm_right m (lcm n k))))
    (lcm_dvd ((dvd_lcm_left m n).trans (dvd_lcm_left (lcm m n) k))
      (lcm_dvd ((dvd_lcm_right m n).trans (dvd_lcm_left (lcm m n) k)) (dvd_lcm_right (lcm m n) k)))
#align nat.lcm_assoc Nat.lcm_assoc
-/

#print Nat.lcm_ne_zero /-
theorem lcm_ne_zero {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : lcm m n ≠ 0 :=
  by
  intro h
  simpa [h, hm, hn] using gcd_mul_lcm m n
#align nat.lcm_ne_zero Nat.lcm_ne_zero
-/

/-!
### `coprime`

See also `nat.coprime_of_dvd` and `nat.coprime_of_dvd'` to prove `nat.coprime m n`.
-/


instance (m n : ℕ) : Decidable (coprime m n) := by unfold coprime <;> infer_instance

#print Nat.coprime_iff_gcd_eq_one /-
theorem coprime_iff_gcd_eq_one {m n : ℕ} : coprime m n ↔ gcd m n = 1 :=
  Iff.rfl
#align nat.coprime_iff_gcd_eq_one Nat.coprime_iff_gcd_eq_one
-/

#print Nat.coprime.gcd_eq_one /-
theorem coprime.gcd_eq_one {m n : ℕ} (h : coprime m n) : gcd m n = 1 :=
  h
#align nat.coprime.gcd_eq_one Nat.coprime.gcd_eq_one
-/

#print Nat.coprime.lcm_eq_mul /-
theorem coprime.lcm_eq_mul {m n : ℕ} (h : coprime m n) : lcm m n = m * n := by
  rw [← one_mul (lcm m n), ← h.gcd_eq_one, gcd_mul_lcm]
#align nat.coprime.lcm_eq_mul Nat.coprime.lcm_eq_mul
-/

/- warning: nat.coprime.symm -> Nat.coprime.symm is a dubious translation:
lean 3 declaration is
  forall {m : Nat} {n : Nat}, (Nat.coprime n m) -> (Nat.coprime m n)
but is expected to have type
  forall {m : Nat} {n : Nat}, (Nat.coprime m n) -> (Nat.coprime n m)
Case conversion may be inaccurate. Consider using '#align nat.coprime.symm Nat.coprime.symmₓ'. -/
theorem coprime.symm {m n : ℕ} : coprime n m → coprime m n :=
  (gcd_comm m n).trans
#align nat.coprime.symm Nat.coprime.symm

/- warning: nat.coprime_comm -> Nat.coprime_comm is a dubious translation:
lean 3 declaration is
  forall {m : Nat} {n : Nat}, Iff (Nat.coprime n m) (Nat.coprime m n)
but is expected to have type
  forall {m : Nat} {n : Nat}, Iff (Nat.coprime m n) (Nat.coprime n m)
Case conversion may be inaccurate. Consider using '#align nat.coprime_comm Nat.coprime_commₓ'. -/
theorem coprime_comm {m n : ℕ} : coprime n m ↔ coprime m n :=
  ⟨coprime.symm, coprime.symm⟩
#align nat.coprime_comm Nat.coprime_comm

#print Nat.coprime.symmetric /-
theorem coprime.symmetric : Symmetric coprime := fun m n => coprime.symm
#align nat.coprime.symmetric Nat.coprime.symmetric
-/

/- warning: nat.coprime.dvd_of_dvd_mul_right -> Nat.coprime.dvd_of_dvd_mul_right is a dubious translation:
lean 3 declaration is
  forall {m : Nat} {n : Nat} {k : Nat}, (Nat.coprime k n) -> (Dvd.Dvd.{0} Nat Nat.hasDvd k (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) m n)) -> (Dvd.Dvd.{0} Nat Nat.hasDvd k m)
but is expected to have type
  forall {m : Nat} {n : Nat} {k : Nat}, (Nat.coprime m n) -> (Dvd.dvd.{0} Nat Nat.instDvdNat m (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) k n)) -> (Dvd.dvd.{0} Nat Nat.instDvdNat m k)
Case conversion may be inaccurate. Consider using '#align nat.coprime.dvd_of_dvd_mul_right Nat.coprime.dvd_of_dvd_mul_rightₓ'. -/
theorem coprime.dvd_of_dvd_mul_right {m n k : ℕ} (H1 : coprime k n) (H2 : k ∣ m * n) : k ∣ m :=
  by
  let t := dvd_gcd (dvd_mul_left k m) H2
  rwa [gcd_mul_left, H1.gcd_eq_one, mul_one] at t
#align nat.coprime.dvd_of_dvd_mul_right Nat.coprime.dvd_of_dvd_mul_right

/- warning: nat.coprime.dvd_of_dvd_mul_left -> Nat.coprime.dvd_of_dvd_mul_left is a dubious translation:
lean 3 declaration is
  forall {m : Nat} {n : Nat} {k : Nat}, (Nat.coprime k m) -> (Dvd.Dvd.{0} Nat Nat.hasDvd k (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) m n)) -> (Dvd.Dvd.{0} Nat Nat.hasDvd k n)
but is expected to have type
  forall {m : Nat} {n : Nat} {k : Nat}, (Nat.coprime m n) -> (Dvd.dvd.{0} Nat Nat.instDvdNat m (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) n k)) -> (Dvd.dvd.{0} Nat Nat.instDvdNat m k)
Case conversion may be inaccurate. Consider using '#align nat.coprime.dvd_of_dvd_mul_left Nat.coprime.dvd_of_dvd_mul_leftₓ'. -/
theorem coprime.dvd_of_dvd_mul_left {m n k : ℕ} (H1 : coprime k m) (H2 : k ∣ m * n) : k ∣ n := by
  rw [mul_comm] at H2 <;> exact H1.dvd_of_dvd_mul_right H2
#align nat.coprime.dvd_of_dvd_mul_left Nat.coprime.dvd_of_dvd_mul_left

#print Nat.coprime.dvd_mul_right /-
theorem coprime.dvd_mul_right {m n k : ℕ} (H : coprime k n) : k ∣ m * n ↔ k ∣ m :=
  ⟨H.dvd_of_dvd_mul_right, fun h => dvd_mul_of_dvd_left h n⟩
#align nat.coprime.dvd_mul_right Nat.coprime.dvd_mul_right
-/

#print Nat.coprime.dvd_mul_left /-
theorem coprime.dvd_mul_left {m n k : ℕ} (H : coprime k m) : k ∣ m * n ↔ k ∣ n :=
  ⟨H.dvd_of_dvd_mul_left, fun h => dvd_mul_of_dvd_right h m⟩
#align nat.coprime.dvd_mul_left Nat.coprime.dvd_mul_left
-/

/- warning: nat.coprime.gcd_mul_left_cancel -> Nat.coprime.gcd_mul_left_cancel is a dubious translation:
lean 3 declaration is
  forall {k : Nat} (m : Nat) {n : Nat}, (Nat.coprime k n) -> (Eq.{1} Nat (Nat.gcd (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) k m) n) (Nat.gcd m n))
but is expected to have type
  forall {k : Nat} {m : Nat} (n : Nat), (Nat.coprime k m) -> (Eq.{1} Nat (Nat.gcd (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) k n) m) (Nat.gcd n m))
Case conversion may be inaccurate. Consider using '#align nat.coprime.gcd_mul_left_cancel Nat.coprime.gcd_mul_left_cancelₓ'. -/
theorem coprime.gcd_mul_left_cancel {k : ℕ} (m : ℕ) {n : ℕ} (H : coprime k n) :
    gcd (k * m) n = gcd m n :=
  have H1 : coprime (gcd (k * m) n) k := by
    rw [coprime, gcd_assoc, H.symm.gcd_eq_one, gcd_one_right]
  dvd_antisymm (dvd_gcd (H1.dvd_of_dvd_mul_left (gcd_dvd_left _ _)) (gcd_dvd_right _ _))
    (gcd_dvd_gcd_mul_left _ _ _)
#align nat.coprime.gcd_mul_left_cancel Nat.coprime.gcd_mul_left_cancel

/- warning: nat.coprime.gcd_mul_right_cancel -> Nat.coprime.gcd_mul_right_cancel is a dubious translation:
lean 3 declaration is
  forall (m : Nat) {k : Nat} {n : Nat}, (Nat.coprime k n) -> (Eq.{1} Nat (Nat.gcd (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) m k) n) (Nat.gcd m n))
but is expected to have type
  forall {m : Nat} {k : Nat} (n : Nat), (Nat.coprime m k) -> (Eq.{1} Nat (Nat.gcd (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) n m) k) (Nat.gcd n k))
Case conversion may be inaccurate. Consider using '#align nat.coprime.gcd_mul_right_cancel Nat.coprime.gcd_mul_right_cancelₓ'. -/
theorem coprime.gcd_mul_right_cancel (m : ℕ) {k n : ℕ} (H : coprime k n) :
    gcd (m * k) n = gcd m n := by rw [mul_comm m k, H.gcd_mul_left_cancel m]
#align nat.coprime.gcd_mul_right_cancel Nat.coprime.gcd_mul_right_cancel

#print Nat.coprime.gcd_mul_left_cancel_right /-
theorem coprime.gcd_mul_left_cancel_right {k m : ℕ} (n : ℕ) (H : coprime k m) :
    gcd m (k * n) = gcd m n := by rw [gcd_comm m n, gcd_comm m (k * n), H.gcd_mul_left_cancel n]
#align nat.coprime.gcd_mul_left_cancel_right Nat.coprime.gcd_mul_left_cancel_right
-/

#print Nat.coprime.gcd_mul_right_cancel_right /-
theorem coprime.gcd_mul_right_cancel_right {k m : ℕ} (n : ℕ) (H : coprime k m) :
    gcd m (n * k) = gcd m n := by rw [mul_comm n k, H.gcd_mul_left_cancel_right n]
#align nat.coprime.gcd_mul_right_cancel_right Nat.coprime.gcd_mul_right_cancel_right
-/

#print Nat.coprime_div_gcd_div_gcd /-
theorem coprime_div_gcd_div_gcd {m n : ℕ} (H : 0 < gcd m n) : coprime (m / gcd m n) (n / gcd m n) :=
  by rw [coprime_iff_gcd_eq_one, gcd_div (gcd_dvd_left m n) (gcd_dvd_right m n), Nat.div_self H]
#align nat.coprime_div_gcd_div_gcd Nat.coprime_div_gcd_div_gcd
-/

/- warning: nat.not_coprime_of_dvd_of_dvd -> Nat.not_coprime_of_dvd_of_dvd is a dubious translation:
lean 3 declaration is
  forall {m : Nat} {n : Nat} {d : Nat}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) d) -> (Dvd.Dvd.{0} Nat Nat.hasDvd d m) -> (Dvd.Dvd.{0} Nat Nat.hasDvd d n) -> (Not (Nat.coprime m n))
but is expected to have type
  forall {m : Nat} {n : Nat} {d : Nat}, (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) m) -> (Dvd.dvd.{0} Nat Nat.instDvdNat m n) -> (Dvd.dvd.{0} Nat Nat.instDvdNat m d) -> (Not (Nat.coprime n d))
Case conversion may be inaccurate. Consider using '#align nat.not_coprime_of_dvd_of_dvd Nat.not_coprime_of_dvd_of_dvdₓ'. -/
theorem not_coprime_of_dvd_of_dvd {m n d : ℕ} (dgt1 : 1 < d) (Hm : d ∣ m) (Hn : d ∣ n) :
    ¬coprime m n := fun co =>
  not_lt_of_ge (le_of_dvd zero_lt_one <| by rw [← co.gcd_eq_one] <;> exact dvd_gcd Hm Hn) dgt1
#align nat.not_coprime_of_dvd_of_dvd Nat.not_coprime_of_dvd_of_dvd

#print Nat.exists_coprime /-
theorem exists_coprime {m n : ℕ} (H : 0 < gcd m n) :
    ∃ m' n', coprime m' n' ∧ m = m' * gcd m n ∧ n = n' * gcd m n :=
  ⟨_, _, coprime_div_gcd_div_gcd H, (Nat.div_mul_cancel (gcd_dvd_left m n)).symm,
    (Nat.div_mul_cancel (gcd_dvd_right m n)).symm⟩
#align nat.exists_coprime Nat.exists_coprime
-/

#print Nat.exists_coprime' /-
theorem exists_coprime' {m n : ℕ} (H : 0 < gcd m n) :
    ∃ g m' n', 0 < g ∧ coprime m' n' ∧ m = m' * g ∧ n = n' * g :=
  let ⟨m', n', h⟩ := exists_coprime H
  ⟨_, m', n', H, h⟩
#align nat.exists_coprime' Nat.exists_coprime'
-/

#print Nat.coprime_add_self_right /-
@[simp]
theorem coprime_add_self_right {m n : ℕ} : coprime m (n + m) ↔ coprime m n := by
  rw [coprime, coprime, gcd_add_self_right]
#align nat.coprime_add_self_right Nat.coprime_add_self_right
-/

#print Nat.coprime_self_add_right /-
@[simp]
theorem coprime_self_add_right {m n : ℕ} : coprime m (m + n) ↔ coprime m n := by
  rw [add_comm, coprime_add_self_right]
#align nat.coprime_self_add_right Nat.coprime_self_add_right
-/

#print Nat.coprime_add_self_left /-
@[simp]
theorem coprime_add_self_left {m n : ℕ} : coprime (m + n) n ↔ coprime m n := by
  rw [coprime, coprime, gcd_add_self_left]
#align nat.coprime_add_self_left Nat.coprime_add_self_left
-/

#print Nat.coprime_self_add_left /-
@[simp]
theorem coprime_self_add_left {m n : ℕ} : coprime (m + n) m ↔ coprime n m := by
  rw [coprime, coprime, gcd_self_add_left]
#align nat.coprime_self_add_left Nat.coprime_self_add_left
-/

#print Nat.coprime_add_mul_right_right /-
@[simp]
theorem coprime_add_mul_right_right (m n k : ℕ) : coprime m (n + k * m) ↔ coprime m n := by
  rw [coprime, coprime, gcd_add_mul_right_right]
#align nat.coprime_add_mul_right_right Nat.coprime_add_mul_right_right
-/

#print Nat.coprime_add_mul_left_right /-
@[simp]
theorem coprime_add_mul_left_right (m n k : ℕ) : coprime m (n + m * k) ↔ coprime m n := by
  rw [coprime, coprime, gcd_add_mul_left_right]
#align nat.coprime_add_mul_left_right Nat.coprime_add_mul_left_right
-/

#print Nat.coprime_mul_right_add_right /-
@[simp]
theorem coprime_mul_right_add_right (m n k : ℕ) : coprime m (k * m + n) ↔ coprime m n := by
  rw [coprime, coprime, gcd_mul_right_add_right]
#align nat.coprime_mul_right_add_right Nat.coprime_mul_right_add_right
-/

#print Nat.coprime_mul_left_add_right /-
@[simp]
theorem coprime_mul_left_add_right (m n k : ℕ) : coprime m (m * k + n) ↔ coprime m n := by
  rw [coprime, coprime, gcd_mul_left_add_right]
#align nat.coprime_mul_left_add_right Nat.coprime_mul_left_add_right
-/

#print Nat.coprime_add_mul_right_left /-
@[simp]
theorem coprime_add_mul_right_left (m n k : ℕ) : coprime (m + k * n) n ↔ coprime m n := by
  rw [coprime, coprime, gcd_add_mul_right_left]
#align nat.coprime_add_mul_right_left Nat.coprime_add_mul_right_left
-/

#print Nat.coprime_add_mul_left_left /-
@[simp]
theorem coprime_add_mul_left_left (m n k : ℕ) : coprime (m + n * k) n ↔ coprime m n := by
  rw [coprime, coprime, gcd_add_mul_left_left]
#align nat.coprime_add_mul_left_left Nat.coprime_add_mul_left_left
-/

#print Nat.coprime_mul_right_add_left /-
@[simp]
theorem coprime_mul_right_add_left (m n k : ℕ) : coprime (k * n + m) n ↔ coprime m n := by
  rw [coprime, coprime, gcd_mul_right_add_left]
#align nat.coprime_mul_right_add_left Nat.coprime_mul_right_add_left
-/

#print Nat.coprime_mul_left_add_left /-
@[simp]
theorem coprime_mul_left_add_left (m n k : ℕ) : coprime (n * k + m) n ↔ coprime m n := by
  rw [coprime, coprime, gcd_mul_left_add_left]
#align nat.coprime_mul_left_add_left Nat.coprime_mul_left_add_left
-/

/- warning: nat.coprime.mul -> Nat.coprime.mul is a dubious translation:
lean 3 declaration is
  forall {m : Nat} {n : Nat} {k : Nat}, (Nat.coprime m k) -> (Nat.coprime n k) -> (Nat.coprime (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) m n) k)
but is expected to have type
  forall {m : Nat} {n : Nat} {k : Nat}, (Nat.coprime m n) -> (Nat.coprime k n) -> (Nat.coprime (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) m k) n)
Case conversion may be inaccurate. Consider using '#align nat.coprime.mul Nat.coprime.mulₓ'. -/
theorem coprime.mul {m n k : ℕ} (H1 : coprime m k) (H2 : coprime n k) : coprime (m * n) k :=
  (H1.gcd_mul_left_cancel n).trans H2
#align nat.coprime.mul Nat.coprime.mul

#print Nat.coprime.mul_right /-
theorem coprime.mul_right {k m n : ℕ} (H1 : coprime k m) (H2 : coprime k n) : coprime k (m * n) :=
  (H1.symm.mul H2.symm).symm
#align nat.coprime.mul_right Nat.coprime.mul_right
-/

#print Nat.coprime.coprime_dvd_left /-
theorem coprime.coprime_dvd_left {m k n : ℕ} (H1 : m ∣ k) (H2 : coprime k n) : coprime m n :=
  eq_one_of_dvd_one (by delta coprime at H2 <;> rw [← H2] <;> exact gcd_dvd_gcd_of_dvd_left _ H1)
#align nat.coprime.coprime_dvd_left Nat.coprime.coprime_dvd_left
-/

/- warning: nat.coprime.coprime_dvd_right -> Nat.coprime.coprime_dvd_right is a dubious translation:
lean 3 declaration is
  forall {m : Nat} {k : Nat} {n : Nat}, (Dvd.Dvd.{0} Nat Nat.hasDvd n m) -> (Nat.coprime k m) -> (Nat.coprime k n)
but is expected to have type
  forall {m : Nat} {k : Nat} {n : Nat}, (Dvd.dvd.{0} Nat Nat.instDvdNat m k) -> (Nat.coprime n k) -> (Nat.coprime n m)
Case conversion may be inaccurate. Consider using '#align nat.coprime.coprime_dvd_right Nat.coprime.coprime_dvd_rightₓ'. -/
theorem coprime.coprime_dvd_right {m k n : ℕ} (H1 : n ∣ m) (H2 : coprime k m) : coprime k n :=
  (H2.symm.coprime_dvd_left H1).symm
#align nat.coprime.coprime_dvd_right Nat.coprime.coprime_dvd_right

#print Nat.coprime.coprime_mul_left /-
theorem coprime.coprime_mul_left {k m n : ℕ} (H : coprime (k * m) n) : coprime m n :=
  H.coprime_dvd_left (dvd_mul_left _ _)
#align nat.coprime.coprime_mul_left Nat.coprime.coprime_mul_left
-/

/- warning: nat.coprime.coprime_mul_right -> Nat.coprime.coprime_mul_right is a dubious translation:
lean 3 declaration is
  forall {k : Nat} {m : Nat} {n : Nat}, (Nat.coprime (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) m k) n) -> (Nat.coprime m n)
but is expected to have type
  forall {k : Nat} {m : Nat} {n : Nat}, (Nat.coprime (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) k m) n) -> (Nat.coprime k n)
Case conversion may be inaccurate. Consider using '#align nat.coprime.coprime_mul_right Nat.coprime.coprime_mul_rightₓ'. -/
theorem coprime.coprime_mul_right {k m n : ℕ} (H : coprime (m * k) n) : coprime m n :=
  H.coprime_dvd_left (dvd_mul_right _ _)
#align nat.coprime.coprime_mul_right Nat.coprime.coprime_mul_right

/- warning: nat.coprime.coprime_mul_left_right -> Nat.coprime.coprime_mul_left_right is a dubious translation:
lean 3 declaration is
  forall {k : Nat} {m : Nat} {n : Nat}, (Nat.coprime m (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) k n)) -> (Nat.coprime m n)
but is expected to have type
  forall {k : Nat} {m : Nat} {n : Nat}, (Nat.coprime k (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) m n)) -> (Nat.coprime k n)
Case conversion may be inaccurate. Consider using '#align nat.coprime.coprime_mul_left_right Nat.coprime.coprime_mul_left_rightₓ'. -/
theorem coprime.coprime_mul_left_right {k m n : ℕ} (H : coprime m (k * n)) : coprime m n :=
  H.coprime_dvd_right (dvd_mul_left _ _)
#align nat.coprime.coprime_mul_left_right Nat.coprime.coprime_mul_left_right

/- warning: nat.coprime.coprime_mul_right_right -> Nat.coprime.coprime_mul_right_right is a dubious translation:
lean 3 declaration is
  forall {k : Nat} {m : Nat} {n : Nat}, (Nat.coprime m (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) n k)) -> (Nat.coprime m n)
but is expected to have type
  forall {k : Nat} {m : Nat} {n : Nat}, (Nat.coprime k (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) m n)) -> (Nat.coprime k m)
Case conversion may be inaccurate. Consider using '#align nat.coprime.coprime_mul_right_right Nat.coprime.coprime_mul_right_rightₓ'. -/
theorem coprime.coprime_mul_right_right {k m n : ℕ} (H : coprime m (n * k)) : coprime m n :=
  H.coprime_dvd_right (dvd_mul_right _ _)
#align nat.coprime.coprime_mul_right_right Nat.coprime.coprime_mul_right_right

#print Nat.coprime.coprime_div_left /-
theorem coprime.coprime_div_left {m n a : ℕ} (cmn : coprime m n) (dvd : a ∣ m) :
    coprime (m / a) n := by
  by_cases a_split : a = 0
  · subst a_split
    rw [zero_dvd_iff] at dvd
    simpa [dvd] using cmn
  · rcases dvd with ⟨k, rfl⟩
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero a_split)]
    exact coprime.coprime_mul_left cmn
#align nat.coprime.coprime_div_left Nat.coprime.coprime_div_left
-/

#print Nat.coprime.coprime_div_right /-
theorem coprime.coprime_div_right {m n a : ℕ} (cmn : coprime m n) (dvd : a ∣ n) :
    coprime m (n / a) :=
  (coprime.coprime_div_left cmn.symm dvd).symm
#align nat.coprime.coprime_div_right Nat.coprime.coprime_div_right
-/

/- warning: nat.coprime_mul_iff_left -> Nat.coprime_mul_iff_left is a dubious translation:
lean 3 declaration is
  forall {k : Nat} {m : Nat} {n : Nat}, Iff (Nat.coprime (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) m n) k) (And (Nat.coprime m k) (Nat.coprime n k))
but is expected to have type
  forall {k : Nat} {m : Nat} {n : Nat}, Iff (Nat.coprime (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) k m) n) (And (Nat.coprime k n) (Nat.coprime m n))
Case conversion may be inaccurate. Consider using '#align nat.coprime_mul_iff_left Nat.coprime_mul_iff_leftₓ'. -/
theorem coprime_mul_iff_left {k m n : ℕ} : coprime (m * n) k ↔ coprime m k ∧ coprime n k :=
  ⟨fun h => ⟨coprime.coprime_mul_right h, coprime.coprime_mul_left h⟩, fun ⟨h, _⟩ => by
    rwa [coprime_iff_gcd_eq_one, coprime.gcd_mul_left_cancel n h]⟩
#align nat.coprime_mul_iff_left Nat.coprime_mul_iff_left

#print Nat.coprime_mul_iff_right /-
theorem coprime_mul_iff_right {k m n : ℕ} : coprime k (m * n) ↔ coprime k m ∧ coprime k n := by
  simpa only [coprime_comm] using coprime_mul_iff_left
#align nat.coprime_mul_iff_right Nat.coprime_mul_iff_right
-/

/- warning: nat.coprime.gcd_left -> Nat.coprime.gcd_left is a dubious translation:
lean 3 declaration is
  forall (k : Nat) {m : Nat} {n : Nat}, (Nat.coprime m n) -> (Nat.coprime (Nat.gcd k m) n)
but is expected to have type
  forall {k : Nat} {m : Nat} (n : Nat), (Nat.coprime k m) -> (Nat.coprime (Nat.gcd n k) m)
Case conversion may be inaccurate. Consider using '#align nat.coprime.gcd_left Nat.coprime.gcd_leftₓ'. -/
theorem coprime.gcd_left (k : ℕ) {m n : ℕ} (hmn : coprime m n) : coprime (gcd k m) n :=
  hmn.coprime_dvd_left <| gcd_dvd_right k m
#align nat.coprime.gcd_left Nat.coprime.gcd_left

/- warning: nat.coprime.gcd_right -> Nat.coprime.gcd_right is a dubious translation:
lean 3 declaration is
  forall (k : Nat) {m : Nat} {n : Nat}, (Nat.coprime m n) -> (Nat.coprime m (Nat.gcd k n))
but is expected to have type
  forall {k : Nat} {m : Nat} (n : Nat), (Nat.coprime k m) -> (Nat.coprime k (Nat.gcd n m))
Case conversion may be inaccurate. Consider using '#align nat.coprime.gcd_right Nat.coprime.gcd_rightₓ'. -/
theorem coprime.gcd_right (k : ℕ) {m n : ℕ} (hmn : coprime m n) : coprime m (gcd k n) :=
  hmn.coprime_dvd_right <| gcd_dvd_right k n
#align nat.coprime.gcd_right Nat.coprime.gcd_right

/- warning: nat.coprime.gcd_both -> Nat.coprime.gcd_both is a dubious translation:
lean 3 declaration is
  forall (k : Nat) (l : Nat) {m : Nat} {n : Nat}, (Nat.coprime m n) -> (Nat.coprime (Nat.gcd k m) (Nat.gcd l n))
but is expected to have type
  forall {k : Nat} {l : Nat} (m : Nat) (n : Nat), (Nat.coprime k l) -> (Nat.coprime (Nat.gcd m k) (Nat.gcd n l))
Case conversion may be inaccurate. Consider using '#align nat.coprime.gcd_both Nat.coprime.gcd_bothₓ'. -/
theorem coprime.gcd_both (k l : ℕ) {m n : ℕ} (hmn : coprime m n) : coprime (gcd k m) (gcd l n) :=
  (hmn.gcd_left k).gcd_right l
#align nat.coprime.gcd_both Nat.coprime.gcd_both

/- warning: nat.coprime.mul_dvd_of_dvd_of_dvd -> Nat.coprime.mul_dvd_of_dvd_of_dvd is a dubious translation:
lean 3 declaration is
  forall {a : Nat} {n : Nat} {m : Nat}, (Nat.coprime m n) -> (Dvd.Dvd.{0} Nat Nat.hasDvd m a) -> (Dvd.Dvd.{0} Nat Nat.hasDvd n a) -> (Dvd.Dvd.{0} Nat Nat.hasDvd (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) m n) a)
but is expected to have type
  forall {a : Nat} {n : Nat} {m : Nat}, (Nat.coprime a n) -> (Dvd.dvd.{0} Nat Nat.instDvdNat a m) -> (Dvd.dvd.{0} Nat Nat.instDvdNat n m) -> (Dvd.dvd.{0} Nat Nat.instDvdNat (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) a n) m)
Case conversion may be inaccurate. Consider using '#align nat.coprime.mul_dvd_of_dvd_of_dvd Nat.coprime.mul_dvd_of_dvd_of_dvdₓ'. -/
theorem coprime.mul_dvd_of_dvd_of_dvd {a n m : ℕ} (hmn : coprime m n) (hm : m ∣ a) (hn : n ∣ a) :
    m * n ∣ a :=
  let ⟨k, hk⟩ := hm
  hk.symm ▸ mul_dvd_mul_left _ (hmn.symm.dvd_of_dvd_mul_left (hk ▸ hn))
#align nat.coprime.mul_dvd_of_dvd_of_dvd Nat.coprime.mul_dvd_of_dvd_of_dvd

#print Nat.coprime_one_left /-
theorem coprime_one_left : ∀ n, coprime 1 n :=
  gcd_one_left
#align nat.coprime_one_left Nat.coprime_one_left
-/

#print Nat.coprime_one_right /-
theorem coprime_one_right : ∀ n, coprime n 1 :=
  gcd_one_right
#align nat.coprime_one_right Nat.coprime_one_right
-/

#print Nat.coprime.pow_left /-
theorem coprime.pow_left {m k : ℕ} (n : ℕ) (H1 : coprime m k) : coprime (m ^ n) k :=
  Nat.recOn n (coprime_one_left _) fun n IH => H1.mul IH
#align nat.coprime.pow_left Nat.coprime.pow_left
-/

/- warning: nat.coprime.pow_right -> Nat.coprime.pow_right is a dubious translation:
lean 3 declaration is
  forall {m : Nat} {k : Nat} (n : Nat), (Nat.coprime k m) -> (Nat.coprime k (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) m n))
but is expected to have type
  forall {m : Nat} {k : Nat} (n : Nat), (Nat.coprime m k) -> (Nat.coprime m (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) k n))
Case conversion may be inaccurate. Consider using '#align nat.coprime.pow_right Nat.coprime.pow_rightₓ'. -/
theorem coprime.pow_right {m k : ℕ} (n : ℕ) (H1 : coprime k m) : coprime k (m ^ n) :=
  (H1.symm.pow_left n).symm
#align nat.coprime.pow_right Nat.coprime.pow_right

#print Nat.coprime.pow /-
theorem coprime.pow {k l : ℕ} (m n : ℕ) (H1 : coprime k l) : coprime (k ^ m) (l ^ n) :=
  (H1.pow_left _).pow_right _
#align nat.coprime.pow Nat.coprime.pow
-/

#print Nat.coprime_pow_left_iff /-
@[simp]
theorem coprime_pow_left_iff {n : ℕ} (hn : 0 < n) (a b : ℕ) :
    Nat.coprime (a ^ n) b ↔ Nat.coprime a b :=
  by
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero hn.ne'
  rw [pow_succ, Nat.coprime_mul_iff_left]
  exact ⟨And.left, fun hab => ⟨hab, hab.pow_left _⟩⟩
#align nat.coprime_pow_left_iff Nat.coprime_pow_left_iff
-/

#print Nat.coprime_pow_right_iff /-
@[simp]
theorem coprime_pow_right_iff {n : ℕ} (hn : 0 < n) (a b : ℕ) :
    Nat.coprime a (b ^ n) ↔ Nat.coprime a b := by
  rw [Nat.coprime_comm, coprime_pow_left_iff hn, Nat.coprime_comm]
#align nat.coprime_pow_right_iff Nat.coprime_pow_right_iff
-/

#print Nat.coprime.eq_one_of_dvd /-
theorem coprime.eq_one_of_dvd {k m : ℕ} (H : coprime k m) (d : k ∣ m) : k = 1 := by
  rw [← H.gcd_eq_one, gcd_eq_left d]
#align nat.coprime.eq_one_of_dvd Nat.coprime.eq_one_of_dvd
-/

#print Nat.coprime_zero_left /-
@[simp]
theorem coprime_zero_left (n : ℕ) : coprime 0 n ↔ n = 1 := by simp [coprime]
#align nat.coprime_zero_left Nat.coprime_zero_left
-/

#print Nat.coprime_zero_right /-
@[simp]
theorem coprime_zero_right (n : ℕ) : coprime n 0 ↔ n = 1 := by simp [coprime]
#align nat.coprime_zero_right Nat.coprime_zero_right
-/

#print Nat.not_coprime_zero_zero /-
theorem not_coprime_zero_zero : ¬coprime 0 0 := by simp
#align nat.not_coprime_zero_zero Nat.not_coprime_zero_zero
-/

#print Nat.coprime_one_left_iff /-
@[simp]
theorem coprime_one_left_iff (n : ℕ) : coprime 1 n ↔ True := by simp [coprime]
#align nat.coprime_one_left_iff Nat.coprime_one_left_iff
-/

#print Nat.coprime_one_right_iff /-
@[simp]
theorem coprime_one_right_iff (n : ℕ) : coprime n 1 ↔ True := by simp [coprime]
#align nat.coprime_one_right_iff Nat.coprime_one_right_iff
-/

#print Nat.coprime_self /-
@[simp]
theorem coprime_self (n : ℕ) : coprime n n ↔ n = 1 := by simp [coprime]
#align nat.coprime_self Nat.coprime_self
-/

#print Nat.gcd_mul_of_coprime_of_dvd /-
theorem gcd_mul_of_coprime_of_dvd {a b c : ℕ} (hac : coprime a c) (b_dvd_c : b ∣ c) :
    gcd (a * b) c = b :=
  by
  rcases exists_eq_mul_left_of_dvd b_dvd_c with ⟨d, rfl⟩
  rw [gcd_mul_right]
  convert one_mul b
  exact coprime.coprime_mul_right_right hac
#align nat.gcd_mul_of_coprime_of_dvd Nat.gcd_mul_of_coprime_of_dvd
-/

#print Nat.coprime.eq_of_mul_eq_zero /-
theorem coprime.eq_of_mul_eq_zero {m n : ℕ} (h : m.coprime n) (hmn : m * n = 0) :
    m = 0 ∧ n = 1 ∨ m = 1 ∧ n = 0 :=
  (Nat.eq_zero_of_mul_eq_zero hmn).imp (fun hm => ⟨hm, n.coprime_zero_left.mp <| hm ▸ h⟩) fun hn =>
    ⟨m.coprime_zero_left.mp <| hn ▸ h.symm, hn⟩
#align nat.coprime.eq_of_mul_eq_zero Nat.coprime.eq_of_mul_eq_zero
-/

#print Nat.prodDvdAndDvdOfDvdProd /-
/-- Represent a divisor of `m * n` as a product of a divisor of `m` and a divisor of `n`.

See `exists_dvd_and_dvd_of_dvd_mul` for the more general but less constructive version for other
`gcd_monoid`s. -/
def prodDvdAndDvdOfDvdProd {m n k : ℕ} (H : k ∣ m * n) :
    { d : { m' // m' ∣ m } × { n' // n' ∣ n } // k = d.1 * d.2 } :=
  by
  cases h0 : gcd k m
  case zero =>
    obtain rfl : k = 0 := eq_zero_of_gcd_eq_zero_left h0
    obtain rfl : m = 0 := eq_zero_of_gcd_eq_zero_right h0
    exact ⟨⟨⟨0, dvd_refl 0⟩, ⟨n, dvd_refl n⟩⟩, (zero_mul n).symm⟩
  case
    succ tmp =>
    have hpos : 0 < gcd k m := h0.symm ▸ Nat.zero_lt_succ _ <;> clear h0 tmp
    have hd : gcd k m * (k / gcd k m) = k := Nat.mul_div_cancel' (gcd_dvd_left k m)
    refine' ⟨⟨⟨gcd k m, gcd_dvd_right k m⟩, ⟨k / gcd k m, _⟩⟩, hd.symm⟩
    apply dvd_of_mul_dvd_mul_left hpos
    rw [hd, ← gcd_mul_right]
    exact dvd_gcd (dvd_mul_right _ _) H
#align nat.prod_dvd_and_dvd_of_dvd_prod Nat.prodDvdAndDvdOfDvdProd
-/

#print Nat.dvd_mul /-
theorem dvd_mul {x m n : ℕ} : x ∣ m * n ↔ ∃ y z, y ∣ m ∧ z ∣ n ∧ y * z = x :=
  by
  constructor
  · intro h
    obtain ⟨⟨⟨y, hy⟩, ⟨z, hz⟩⟩, rfl⟩ := prod_dvd_and_dvd_of_dvd_prod h
    exact ⟨y, z, hy, hz, rfl⟩
  · rintro ⟨y, z, hy, hz, rfl⟩
    exact mul_dvd_mul hy hz
#align nat.dvd_mul Nat.dvd_mul
-/

#print Nat.gcd_mul_dvd_mul_gcd /-
theorem gcd_mul_dvd_mul_gcd (k m n : ℕ) : gcd k (m * n) ∣ gcd k m * gcd k n :=
  by
  rcases prod_dvd_and_dvd_of_dvd_prod <| gcd_dvd_right k (m * n) with ⟨⟨⟨m', hm'⟩, ⟨n', hn'⟩⟩, h⟩
  replace h : gcd k (m * n) = m' * n' := h
  rw [h]
  have hm'n' : m' * n' ∣ k := h ▸ gcd_dvd_left _ _
  apply mul_dvd_mul
  · have hm'k : m' ∣ k := (dvd_mul_right m' n').trans hm'n'
    exact dvd_gcd hm'k hm'
  · have hn'k : n' ∣ k := (dvd_mul_left n' m').trans hm'n'
    exact dvd_gcd hn'k hn'
#align nat.gcd_mul_dvd_mul_gcd Nat.gcd_mul_dvd_mul_gcd
-/

/- warning: nat.coprime.gcd_mul -> Nat.coprime.gcd_mul is a dubious translation:
lean 3 declaration is
  forall (k : Nat) {m : Nat} {n : Nat}, (Nat.coprime m n) -> (Eq.{1} Nat (Nat.gcd k (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) m n)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (Nat.gcd k m) (Nat.gcd k n)))
but is expected to have type
  forall {k : Nat} {m : Nat} (n : Nat), (Nat.coprime k m) -> (Eq.{1} Nat (Nat.gcd n (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) k m)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Nat.gcd n k) (Nat.gcd n m)))
Case conversion may be inaccurate. Consider using '#align nat.coprime.gcd_mul Nat.coprime.gcd_mulₓ'. -/
theorem coprime.gcd_mul (k : ℕ) {m n : ℕ} (h : coprime m n) : gcd k (m * n) = gcd k m * gcd k n :=
  dvd_antisymm (gcd_mul_dvd_mul_gcd k m n)
    ((h.gcd_both k k).mul_dvd_of_dvd_of_dvd (gcd_dvd_gcd_mul_right_right _ _ _)
      (gcd_dvd_gcd_mul_left_right _ _ _))
#align nat.coprime.gcd_mul Nat.coprime.gcd_mul

#print Nat.pow_dvd_pow_iff /-
theorem pow_dvd_pow_iff {a b n : ℕ} (n0 : 0 < n) : a ^ n ∣ b ^ n ↔ a ∣ b :=
  by
  refine' ⟨fun h => _, fun h => pow_dvd_pow_of_dvd h _⟩
  cases' Nat.eq_zero_or_pos (gcd a b) with g0 g0
  · simp [eq_zero_of_gcd_eq_zero_right g0]
  rcases exists_coprime' g0 with ⟨g, a', b', g0', co, rfl, rfl⟩
  rw [mul_pow, mul_pow] at h
  replace h := dvd_of_mul_dvd_mul_right (pow_pos g0' _) h
  have := pow_dvd_pow a' n0
  rw [pow_one, (co.pow n n).eq_one_of_dvd h] at this
  simp [eq_one_of_dvd_one this]
#align nat.pow_dvd_pow_iff Nat.pow_dvd_pow_iff
-/

/- warning: nat.gcd_mul_gcd_of_coprime_of_mul_eq_mul -> Nat.gcd_mul_gcd_of_coprime_of_mul_eq_mul is a dubious translation:
lean 3 declaration is
  forall {a : Nat} {b : Nat} {c : Nat} {d : Nat}, (Nat.coprime c d) -> (Eq.{1} Nat (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) a b) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) c d)) -> (Eq.{1} Nat (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (Nat.gcd a c) (Nat.gcd b c)) c)
but is expected to have type
  forall {a : Nat} {b : Nat} {c : Nat} {d : Nat}, (Nat.coprime a b) -> (Eq.{1} Nat (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) c d) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) a b)) -> (Eq.{1} Nat (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Nat.gcd c a) (Nat.gcd d a)) a)
Case conversion may be inaccurate. Consider using '#align nat.gcd_mul_gcd_of_coprime_of_mul_eq_mul Nat.gcd_mul_gcd_of_coprime_of_mul_eq_mulₓ'. -/
theorem gcd_mul_gcd_of_coprime_of_mul_eq_mul {a b c d : ℕ} (cop : c.coprime d) (h : a * b = c * d) :
    a.gcd c * b.gcd c = c := by
  apply dvd_antisymm
  · apply Nat.coprime.dvd_of_dvd_mul_right (Nat.coprime.mul (cop.gcd_left _) (cop.gcd_left _))
    rw [← h]
    apply mul_dvd_mul (gcd_dvd _ _).1 (gcd_dvd _ _).1
  · rw [gcd_comm a _, gcd_comm b _]
    trans c.gcd (a * b)
    rw [h, gcd_mul_right_right d c]
    apply gcd_mul_dvd_mul_gcd
#align nat.gcd_mul_gcd_of_coprime_of_mul_eq_mul Nat.gcd_mul_gcd_of_coprime_of_mul_eq_mul

#print Nat.eq_one_of_dvd_coprimes /-
/-- If `k:ℕ` divides coprime `a` and `b` then `k = 1` -/
theorem eq_one_of_dvd_coprimes {a b k : ℕ} (h_ab_coprime : coprime a b) (hka : k ∣ a)
    (hkb : k ∣ b) : k = 1 :=
  by
  rw [coprime_iff_gcd_eq_one] at h_ab_coprime
  have h1 := dvd_gcd hka hkb
  rw [h_ab_coprime] at h1
  exact nat.dvd_one.mp h1
#align nat.eq_one_of_dvd_coprimes Nat.eq_one_of_dvd_coprimes
-/

#print Nat.coprime.mul_add_mul_ne_mul /-
theorem coprime.mul_add_mul_ne_mul {m n a b : ℕ} (cop : coprime m n) (ha : a ≠ 0) (hb : b ≠ 0) :
    a * m + b * n ≠ m * n := by
  intro h
  obtain ⟨x, rfl⟩ : n ∣ a :=
    cop.symm.dvd_of_dvd_mul_right
      ((Nat.dvd_add_iff_left (dvd_mul_left n b)).mpr ((congr_arg _ h).mpr (dvd_mul_left n m)))
  obtain ⟨y, rfl⟩ : m ∣ b :=
    cop.dvd_of_dvd_mul_right
      ((Nat.dvd_add_iff_right (dvd_mul_left m (n * x))).mpr
        ((congr_arg _ h).mpr (dvd_mul_right m n)))
  rw [mul_comm, mul_ne_zero_iff, ← one_le_iff_ne_zero] at ha hb
  refine' mul_ne_zero hb.2 ha.2 (eq_zero_of_mul_eq_self_left (ne_of_gt (add_le_add ha.1 hb.1)) _)
  rw [← mul_assoc, ← h, add_mul, add_mul, mul_comm _ n, ← mul_assoc, mul_comm y]
#align nat.coprime.mul_add_mul_ne_mul Nat.coprime.mul_add_mul_ne_mul
-/

end Nat

