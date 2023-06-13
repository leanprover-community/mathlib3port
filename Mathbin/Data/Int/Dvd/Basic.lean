/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

! This file was ported from Lean 3 source module data.int.dvd.basic
! leanprover-community/mathlib commit e8638a0fcaf73e4500469f368ef9494e495099b3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Int.Order.Basic
import Mathbin.Data.Nat.Cast.Basic

/-!
# Basic lemmas about the divisibility relation in `ℤ`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open Nat

namespace Int

#print Int.coe_nat_dvd /-
@[norm_cast]
theorem coe_nat_dvd {m n : ℕ} : (↑m : ℤ) ∣ ↑n ↔ m ∣ n :=
  ⟨fun ⟨a, ae⟩ =>
    m.eq_zero_or_pos.elim (fun m0 => by simp [m0] at ae  <;> simp [ae, m0]) fun m0l =>
      by
      cases'
        eq_coe_of_zero_le
          (@nonneg_of_mul_nonneg_right ℤ _ m a (by simp [ae.symm]) (by simpa using m0l)) with
        k e
      subst a; exact ⟨k, Int.ofNat.inj ae⟩,
    fun ⟨k, e⟩ => Dvd.intro k <| by rw [e, Int.ofNat_mul]⟩
#align int.coe_nat_dvd Int.coe_nat_dvd
-/

#print Int.coe_nat_dvd_left /-
theorem coe_nat_dvd_left {n : ℕ} {z : ℤ} : (↑n : ℤ) ∣ z ↔ n ∣ z.natAbs := by
  rcases nat_abs_eq z with (eq | eq) <;> rw [Eq] <;> simp [← coe_nat_dvd]
#align int.coe_nat_dvd_left Int.coe_nat_dvd_left
-/

#print Int.coe_nat_dvd_right /-
theorem coe_nat_dvd_right {n : ℕ} {z : ℤ} : z ∣ (↑n : ℤ) ↔ z.natAbs ∣ n := by
  rcases nat_abs_eq z with (eq | eq) <;> rw [Eq] <;> simp [← coe_nat_dvd]
#align int.coe_nat_dvd_right Int.coe_nat_dvd_right
-/

#print Int.le_of_dvd /-
theorem le_of_dvd {a b : ℤ} (bpos : 0 < b) (H : a ∣ b) : a ≤ b :=
  match a, b, eq_succ_of_zero_lt bpos, H with
  | (m : ℕ), _, ⟨n, rfl⟩, H => ofNat_le_ofNat_of_le <| Nat.le_of_dvd n.succ_pos <| coe_nat_dvd.1 H
  | -[m+1], _, ⟨n, rfl⟩, _ => le_trans (le_of_lt <| negSucc_lt_zero _) (ofNat_zero_le _)
#align int.le_of_dvd Int.le_of_dvd
-/

#print Int.eq_one_of_dvd_one /-
theorem eq_one_of_dvd_one {a : ℤ} (H : 0 ≤ a) (H' : a ∣ 1) : a = 1 :=
  match a, eq_ofNat_of_zero_le H, H' with
  | _, ⟨n, rfl⟩, H' => congr_arg coe <| Nat.eq_one_of_dvd_one <| coe_nat_dvd.1 H'
#align int.eq_one_of_dvd_one Int.eq_one_of_dvd_one
-/

#print Int.eq_one_of_mul_eq_one_right /-
theorem eq_one_of_mul_eq_one_right {a b : ℤ} (H : 0 ≤ a) (H' : a * b = 1) : a = 1 :=
  eq_one_of_dvd_one H ⟨b, H'.symm⟩
#align int.eq_one_of_mul_eq_one_right Int.eq_one_of_mul_eq_one_right
-/

#print Int.eq_one_of_mul_eq_one_left /-
theorem eq_one_of_mul_eq_one_left {a b : ℤ} (H : 0 ≤ b) (H' : a * b = 1) : b = 1 :=
  eq_one_of_mul_eq_one_right H (by rw [mul_comm, H'])
#align int.eq_one_of_mul_eq_one_left Int.eq_one_of_mul_eq_one_left
-/

#print Int.dvd_antisymm /-
theorem dvd_antisymm {a b : ℤ} (H1 : 0 ≤ a) (H2 : 0 ≤ b) : a ∣ b → b ∣ a → a = b :=
  by
  rw [← abs_of_nonneg H1, ← abs_of_nonneg H2, abs_eq_nat_abs, abs_eq_nat_abs]
  rw [coe_nat_dvd, coe_nat_dvd, coe_nat_inj']
  apply Nat.dvd_antisymm
#align int.dvd_antisymm Int.dvd_antisymm
-/

end Int

