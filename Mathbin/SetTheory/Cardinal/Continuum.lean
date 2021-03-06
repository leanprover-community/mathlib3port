/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.SetTheory.Cardinal.Ordinal

/-!
# Cardinality of continuum

In this file we define `cardinal.continuum` (notation: `๐ `, localized in `cardinal`) to be `2 ^ โตโ`.
We also prove some `simp` lemmas about cardinal arithmetic involving `๐ `.

## Notation

- `๐ ` : notation for `cardinal.continuum` in locale `cardinal`.
-/


namespace Cardinal

universe u v

open Cardinal

/-- Cardinality of continuum. -/
def continuum : Cardinal.{u} :=
  2 ^ aleph_0.{u}

-- mathport name: ยซexpr๐ ยป
localized [Cardinal] notation "๐ " => Cardinal.continuum

@[simp]
theorem two_power_aleph_0 : 2 ^ aleph_0.{u} = continuum.{u} :=
  rfl

@[simp]
theorem lift_continuum : lift.{v} ๐  = ๐  := by
  rw [โ two_power_aleph_0, lift_two_power, lift_aleph_0, two_power_aleph_0]

/-!
### Inequalities
-/


theorem aleph_0_lt_continuum : โตโ < ๐  :=
  cantor โตโ

theorem aleph_0_le_continuum : โตโ โค ๐  :=
  aleph_0_lt_continuum.le

theorem nat_lt_continuum (n : โ) : โn < ๐  :=
  (nat_lt_aleph_0 n).trans aleph_0_lt_continuum

theorem mk_set_nat : # (Set โ) = ๐  := by
  simp

theorem continuum_pos : 0 < ๐  :=
  nat_lt_continuum 0

theorem continuum_ne_zero : ๐  โ  0 :=
  continuum_pos.ne'

theorem aleph_one_le_continuum : aleph 1 โค ๐  := by
  rw [โ succ_aleph_0]
  exact Order.succ_le_of_lt aleph_0_lt_continuum

@[simp]
theorem continuum_to_nat : continuum.toNat = 0 :=
  to_nat_apply_of_aleph_0_le aleph_0_le_continuum

@[simp]
theorem continuum_to_part_enat : continuum.toPartEnat = โค :=
  to_part_enat_apply_of_aleph_0_le aleph_0_le_continuum

/-!
### Addition
-/


@[simp]
theorem aleph_0_add_continuum : โตโ + ๐  = ๐  :=
  add_eq_right aleph_0_le_continuum aleph_0_le_continuum

@[simp]
theorem continuum_add_aleph_0 : ๐  + โตโ = ๐  :=
  (add_commโ _ _).trans aleph_0_add_continuum

@[simp]
theorem continuum_add_self : ๐  + ๐  = ๐  :=
  add_eq_right aleph_0_le_continuum le_rfl

@[simp]
theorem nat_add_continuum (n : โ) : โn + ๐  = ๐  :=
  add_eq_right aleph_0_le_continuum (nat_lt_continuum n).le

@[simp]
theorem continuum_add_nat (n : โ) : ๐  + n = ๐  :=
  (add_commโ _ _).trans (nat_add_continuum n)

/-!
### Multiplication
-/


@[simp]
theorem continuum_mul_self : ๐  * ๐  = ๐  :=
  mul_eq_left aleph_0_le_continuum le_rfl continuum_ne_zero

@[simp]
theorem continuum_mul_aleph_0 : ๐  * โตโ = ๐  :=
  mul_eq_left aleph_0_le_continuum aleph_0_le_continuum aleph_0_ne_zero

@[simp]
theorem aleph_0_mul_continuum : โตโ * ๐  = ๐  :=
  (mul_comm _ _).trans continuum_mul_aleph_0

@[simp]
theorem nat_mul_continuum {n : โ} (hn : n โ  0) : โn * ๐  = ๐  :=
  mul_eq_right aleph_0_le_continuum (nat_lt_continuum n).le (Nat.cast_ne_zero.2 hn)

@[simp]
theorem continuum_mul_nat {n : โ} (hn : n โ  0) : ๐  * n = ๐  :=
  (mul_comm _ _).trans (nat_mul_continuum hn)

/-!
### Power
-/


@[simp]
theorem aleph_0_power_aleph_0 : aleph_0.{u} ^ aleph_0.{u} = ๐  :=
  power_self_eq le_rfl

@[simp]
theorem nat_power_aleph_0 {n : โ} (hn : 2 โค n) : (n ^ aleph_0.{u} : Cardinal.{u}) = ๐  :=
  nat_power_eq le_rfl hn

@[simp]
theorem continuum_power_aleph_0 : continuum.{u} ^ aleph_0.{u} = ๐  := by
  rw [โ two_power_aleph_0, โ power_mul, mul_eq_left le_rfl le_rfl aleph_0_ne_zero]

end Cardinal

