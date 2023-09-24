/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import SetTheory.Cardinal.Ordinal

#align_import set_theory.cardinal.continuum from "leanprover-community/mathlib"@"e08a42b2dd544cf11eba72e5fc7bf199d4349925"

/-!
# Cardinality of continuum

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `cardinal.continuum` (notation: `𝔠`, localized in `cardinal`) to be `2 ^ ℵ₀`.
We also prove some `simp` lemmas about cardinal arithmetic involving `𝔠`.

## Notation

- `𝔠` : notation for `cardinal.continuum` in locale `cardinal`.
-/


namespace Cardinal

universe u v

open scoped Cardinal

#print Cardinal.continuum /-
/-- Cardinality of continuum. -/
def continuum : Cardinal.{u} :=
  2 ^ aleph0.{u}
#align cardinal.continuum Cardinal.continuum
-/

scoped notation "𝔠" => Cardinal.continuum

#print Cardinal.two_power_aleph0 /-
@[simp]
theorem two_power_aleph0 : 2 ^ aleph0.{u} = continuum.{u} :=
  rfl
#align cardinal.two_power_aleph_0 Cardinal.two_power_aleph0
-/

#print Cardinal.lift_continuum /-
@[simp]
theorem lift_continuum : lift.{v} 𝔠 = 𝔠 := by
  rw [← two_power_aleph_0, lift_two_power, lift_aleph_0, two_power_aleph_0]
#align cardinal.lift_continuum Cardinal.lift_continuum
-/

/-!
### Inequalities
-/


#print Cardinal.continuum_le_lift /-
@[simp]
theorem continuum_le_lift {c : Cardinal.{u}} : 𝔠 ≤ lift.{v} c ↔ 𝔠 ≤ c := by
  rw [← lift_continuum, lift_le]
#align cardinal.continuum_le_lift Cardinal.continuum_le_lift
-/

#print Cardinal.lift_le_continuum /-
@[simp]
theorem lift_le_continuum {c : Cardinal.{u}} : lift.{v} c ≤ 𝔠 ↔ c ≤ 𝔠 := by
  rw [← lift_continuum, lift_le]
#align cardinal.lift_le_continuum Cardinal.lift_le_continuum
-/

#print Cardinal.continuum_lt_lift /-
@[simp]
theorem continuum_lt_lift {c : Cardinal.{u}} : 𝔠 < lift.{v} c ↔ 𝔠 < c := by
  rw [← lift_continuum, lift_lt]
#align cardinal.continuum_lt_lift Cardinal.continuum_lt_lift
-/

#print Cardinal.lift_lt_continuum /-
@[simp]
theorem lift_lt_continuum {c : Cardinal.{u}} : lift.{v} c < 𝔠 ↔ c < 𝔠 := by
  rw [← lift_continuum, lift_lt]
#align cardinal.lift_lt_continuum Cardinal.lift_lt_continuum
-/

#print Cardinal.aleph0_lt_continuum /-
theorem aleph0_lt_continuum : ℵ₀ < 𝔠 :=
  cantor ℵ₀
#align cardinal.aleph_0_lt_continuum Cardinal.aleph0_lt_continuum
-/

#print Cardinal.aleph0_le_continuum /-
theorem aleph0_le_continuum : ℵ₀ ≤ 𝔠 :=
  aleph0_lt_continuum.le
#align cardinal.aleph_0_le_continuum Cardinal.aleph0_le_continuum
-/

#print Cardinal.beth_one /-
@[simp]
theorem beth_one : beth 1 = 𝔠 := by simpa using beth_succ 0
#align cardinal.beth_one Cardinal.beth_one
-/

#print Cardinal.nat_lt_continuum /-
theorem nat_lt_continuum (n : ℕ) : ↑n < 𝔠 :=
  (nat_lt_aleph0 n).trans aleph0_lt_continuum
#align cardinal.nat_lt_continuum Cardinal.nat_lt_continuum
-/

#print Cardinal.mk_set_nat /-
theorem mk_set_nat : (#Set ℕ) = 𝔠 := by simp
#align cardinal.mk_set_nat Cardinal.mk_set_nat
-/

#print Cardinal.continuum_pos /-
theorem continuum_pos : 0 < 𝔠 :=
  nat_lt_continuum 0
#align cardinal.continuum_pos Cardinal.continuum_pos
-/

#print Cardinal.continuum_ne_zero /-
theorem continuum_ne_zero : 𝔠 ≠ 0 :=
  continuum_pos.ne'
#align cardinal.continuum_ne_zero Cardinal.continuum_ne_zero
-/

#print Cardinal.aleph_one_le_continuum /-
theorem aleph_one_le_continuum : aleph 1 ≤ 𝔠 := by rw [← succ_aleph_0];
  exact Order.succ_le_of_lt aleph_0_lt_continuum
#align cardinal.aleph_one_le_continuum Cardinal.aleph_one_le_continuum
-/

#print Cardinal.continuum_toNat /-
@[simp]
theorem continuum_toNat : continuum.toNat = 0 :=
  toNat_apply_of_aleph0_le aleph0_le_continuum
#align cardinal.continuum_to_nat Cardinal.continuum_toNat
-/

#print Cardinal.continuum_toPartENat /-
@[simp]
theorem continuum_toPartENat : continuum.toPartENat = ⊤ :=
  toPartENat_apply_of_aleph0_le aleph0_le_continuum
#align cardinal.continuum_to_part_enat Cardinal.continuum_toPartENat
-/

/-!
### Addition
-/


#print Cardinal.aleph0_add_continuum /-
@[simp]
theorem aleph0_add_continuum : ℵ₀ + 𝔠 = 𝔠 :=
  add_eq_right aleph0_le_continuum aleph0_le_continuum
#align cardinal.aleph_0_add_continuum Cardinal.aleph0_add_continuum
-/

#print Cardinal.continuum_add_aleph0 /-
@[simp]
theorem continuum_add_aleph0 : 𝔠 + ℵ₀ = 𝔠 :=
  (add_comm _ _).trans aleph0_add_continuum
#align cardinal.continuum_add_aleph_0 Cardinal.continuum_add_aleph0
-/

#print Cardinal.continuum_add_self /-
@[simp]
theorem continuum_add_self : 𝔠 + 𝔠 = 𝔠 :=
  add_eq_right aleph0_le_continuum le_rfl
#align cardinal.continuum_add_self Cardinal.continuum_add_self
-/

#print Cardinal.nat_add_continuum /-
@[simp]
theorem nat_add_continuum (n : ℕ) : ↑n + 𝔠 = 𝔠 :=
  add_eq_right aleph0_le_continuum (nat_lt_continuum n).le
#align cardinal.nat_add_continuum Cardinal.nat_add_continuum
-/

#print Cardinal.continuum_add_nat /-
@[simp]
theorem continuum_add_nat (n : ℕ) : 𝔠 + n = 𝔠 :=
  (add_comm _ _).trans (nat_add_continuum n)
#align cardinal.continuum_add_nat Cardinal.continuum_add_nat
-/

/-!
### Multiplication
-/


#print Cardinal.continuum_mul_self /-
@[simp]
theorem continuum_mul_self : 𝔠 * 𝔠 = 𝔠 :=
  mul_eq_left aleph0_le_continuum le_rfl continuum_ne_zero
#align cardinal.continuum_mul_self Cardinal.continuum_mul_self
-/

#print Cardinal.continuum_mul_aleph0 /-
@[simp]
theorem continuum_mul_aleph0 : 𝔠 * ℵ₀ = 𝔠 :=
  mul_eq_left aleph0_le_continuum aleph0_le_continuum aleph0_ne_zero
#align cardinal.continuum_mul_aleph_0 Cardinal.continuum_mul_aleph0
-/

#print Cardinal.aleph0_mul_continuum /-
@[simp]
theorem aleph0_mul_continuum : ℵ₀ * 𝔠 = 𝔠 :=
  (mul_comm _ _).trans continuum_mul_aleph0
#align cardinal.aleph_0_mul_continuum Cardinal.aleph0_mul_continuum
-/

#print Cardinal.nat_mul_continuum /-
@[simp]
theorem nat_mul_continuum {n : ℕ} (hn : n ≠ 0) : ↑n * 𝔠 = 𝔠 :=
  mul_eq_right aleph0_le_continuum (nat_lt_continuum n).le (Nat.cast_ne_zero.2 hn)
#align cardinal.nat_mul_continuum Cardinal.nat_mul_continuum
-/

#print Cardinal.continuum_mul_nat /-
@[simp]
theorem continuum_mul_nat {n : ℕ} (hn : n ≠ 0) : 𝔠 * n = 𝔠 :=
  (mul_comm _ _).trans (nat_mul_continuum hn)
#align cardinal.continuum_mul_nat Cardinal.continuum_mul_nat
-/

/-!
### Power
-/


#print Cardinal.aleph0_power_aleph0 /-
@[simp]
theorem aleph0_power_aleph0 : aleph0.{u} ^ aleph0.{u} = 𝔠 :=
  power_self_eq le_rfl
#align cardinal.aleph_0_power_aleph_0 Cardinal.aleph0_power_aleph0
-/

#print Cardinal.nat_power_aleph0 /-
@[simp]
theorem nat_power_aleph0 {n : ℕ} (hn : 2 ≤ n) : (n ^ aleph0.{u} : Cardinal.{u}) = 𝔠 :=
  nat_power_eq le_rfl hn
#align cardinal.nat_power_aleph_0 Cardinal.nat_power_aleph0
-/

#print Cardinal.continuum_power_aleph0 /-
@[simp]
theorem continuum_power_aleph0 : continuum.{u} ^ aleph0.{u} = 𝔠 := by
  rw [← two_power_aleph_0, ← power_mul, mul_eq_left le_rfl le_rfl aleph_0_ne_zero]
#align cardinal.continuum_power_aleph_0 Cardinal.continuum_power_aleph0
-/

end Cardinal

