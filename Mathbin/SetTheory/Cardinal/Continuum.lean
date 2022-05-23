/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.SetTheory.Cardinal.Ordinal

/-!
# Cardinality of continuum

In this file we define `cardinal.continuum` (notation: `𝔠`, localized in `cardinal`) to be `2 ^ ω`.
We also prove some `simp` lemmas about cardinal arithmetic involving `𝔠`.

## Notation

- `𝔠` : notation for `cardinal.continuum` in locale `cardinal`.
-/


namespace Cardinal

universe u v

open Cardinal

/-- Cardinality of continuum. -/
def continuum : Cardinal.{u} :=
  2 ^ omega.{u}

-- mathport name: «expr𝔠»
localized [Cardinal] notation "𝔠" => Cardinal.continuum

@[simp]
theorem two_power_omega : (2 ^ omega.{u} : Cardinal.{u}) = 𝔠 :=
  rfl

@[simp]
theorem lift_continuum : lift.{v} continuum.{u} = 𝔠 := by
  rw [← two_power_omega, lift_two_power, lift_omega, two_power_omega]

/-!
### Inequalities
-/


theorem omega_lt_continuum : ω < 𝔠 :=
  cantor ω

theorem omega_le_continuum : ω ≤ 𝔠 :=
  omega_lt_continuum.le

theorem nat_lt_continuum (n : ℕ) : ↑n < 𝔠 :=
  (nat_lt_omega n).trans omega_lt_continuum

theorem mk_set_nat : # (Set ℕ) = 𝔠 := by
  simp

theorem continuum_pos : 0 < 𝔠 :=
  nat_lt_continuum 0

theorem continuum_ne_zero : 𝔠 ≠ 0 :=
  continuum_pos.ne'

theorem aleph_one_le_continuum : aleph 1 ≤ 𝔠 := by
  rw [← succ_omega]
  exact succ_le_of_lt omega_lt_continuum

/-!
### Addition
-/


@[simp]
theorem omega_add_continuum : ω + 𝔠 = 𝔠 :=
  add_eq_right omega_le_continuum omega_le_continuum

@[simp]
theorem continuum_add_omega : 𝔠 + ω = 𝔠 :=
  (add_commₓ _ _).trans omega_add_continuum

@[simp]
theorem continuum_add_self : 𝔠 + 𝔠 = 𝔠 :=
  add_eq_right omega_le_continuum le_rfl

@[simp]
theorem nat_add_continuum (n : ℕ) : ↑n + 𝔠 = 𝔠 :=
  add_eq_right omega_le_continuum (nat_lt_continuum n).le

@[simp]
theorem continuum_add_nat (n : ℕ) : 𝔠 + n = 𝔠 :=
  (add_commₓ _ _).trans (nat_add_continuum n)

/-!
### Multiplication
-/


@[simp]
theorem continuum_mul_self : 𝔠 * 𝔠 = 𝔠 :=
  mul_eq_left omega_le_continuum le_rfl continuum_ne_zero

@[simp]
theorem continuum_mul_omega : 𝔠 * ω = 𝔠 :=
  mul_eq_left omega_le_continuum omega_le_continuum omega_ne_zero

@[simp]
theorem omega_mul_continuum : ω * 𝔠 = 𝔠 :=
  (mul_comm _ _).trans continuum_mul_omega

@[simp]
theorem nat_mul_continuum {n : ℕ} (hn : n ≠ 0) : ↑n * 𝔠 = 𝔠 :=
  mul_eq_right omega_le_continuum (nat_lt_continuum n).le (Nat.cast_ne_zero.2 hn)

@[simp]
theorem continuum_mul_nat {n : ℕ} (hn : n ≠ 0) : 𝔠 * n = 𝔠 :=
  (mul_comm _ _).trans (nat_mul_continuum hn)

/-!
### Power
-/


@[simp]
theorem omega_power_omega : omega.{u} ^ omega.{u} = 𝔠 :=
  power_self_eq le_rfl

@[simp]
theorem nat_power_omega {n : ℕ} (hn : 2 ≤ n) : (n ^ omega.{u} : Cardinal.{u}) = 𝔠 :=
  nat_power_eq le_rfl hn

@[simp]
theorem continuum_power_omega : continuum.{u} ^ omega.{u} = 𝔠 := by
  rw [← two_power_omega, ← power_mul, mul_eq_left le_rfl le_rfl omega_ne_zero]

end Cardinal

