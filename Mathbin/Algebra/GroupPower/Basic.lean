/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import Mathbin.Data.Nat.Basic
import Mathbin.Tactic.Monotonicity.Basic
import Mathbin.GroupTheory.GroupAction.Defs

/-!
# Power operations on monoids and groups

The power operation on monoids and groups.
We separate this from group, because it depends on `ℕ`,
which in turn depends on other parts of algebra.

This module contains lemmas about `a ^ n` and `n • a`, where `n : ℕ` or `n : ℤ`.
Further lemmas can be found in `algebra.group_power.lemmas`.

The analogous results for groups with zero can be found in `algebra.group_with_zero.power`.

## Notation

- `a ^ n` is used as notation for `has_pow.pow a n`; in this file `n : ℕ` or `n : ℤ`.
- `n • a` is used as notation for `has_scalar.smul n a`; in this file `n : ℕ` or `n : ℤ`.

## Implementation details

We adopt the convention that `0^0 = 1`.
-/


universe u v w x y z u₁ u₂

variable {M : Type u} {N : Type v} {G : Type w} {H : Type x} {A : Type y} {B : Type z} {R : Type u₁} {S : Type u₂}

/-!
### Commutativity

First we prove some facts about `semiconj_by` and `commute`. They do not require any theory about
`pow` and/or `nsmul` and will be useful later in this file.
-/


section Pow

variable [Pow M ℕ]

@[simp]
theorem pow_ite (P : Prop) [Decidable P] (a : M) (b c : ℕ) : (a ^ if P then b else c) = if P then a ^ b else a ^ c := by
  split_ifs <;> rfl

@[simp]
theorem ite_pow (P : Prop) [Decidable P] (a b : M) (c : ℕ) : (if P then a else b) ^ c = if P then a ^ c else b ^ c := by
  split_ifs <;> rfl

end Pow

section Monoidₓ

variable [Monoidₓ M] [Monoidₓ N] [AddMonoidₓ A] [AddMonoidₓ B]

@[simp, to_additive one_nsmul]
theorem pow_oneₓ (a : M) : a ^ 1 = a := by
  rw [pow_succₓ, pow_zeroₓ, mul_oneₓ]

/-- Note that most of the lemmas about powers of two refer to it as `sq`. -/
@[to_additive two_nsmul, nolint to_additive_doc]
theorem pow_two (a : M) : a ^ 2 = a * a := by
  rw [pow_succₓ, pow_oneₓ]

alias pow_two ← sq

@[to_additive]
theorem pow_mul_comm' (a : M) (n : ℕ) : a ^ n * a = a * a ^ n :=
  Commute.pow_self a n

@[to_additive add_nsmul]
theorem pow_addₓ (a : M) (m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction' n with n ih <;> [rw [Nat.add_zero, pow_zeroₓ, mul_oneₓ],
    rw [pow_succ'ₓ, ← mul_assoc, ← ih, ← pow_succ'ₓ, Nat.add_assoc]]

@[simp]
theorem pow_boole (P : Prop) [Decidable P] (a : M) : (a ^ if P then 1 else 0) = if P then a else 1 := by
  simp

-- the attributes are intentionally out of order. `smul_zero` proves `nsmul_zero`.
@[to_additive nsmul_zero, simp]
theorem one_pow (n : ℕ) : (1 : M) ^ n = 1 := by
  induction' n with n ih <;> [exact pow_zeroₓ _, rw [pow_succₓ, ih, one_mulₓ]]

@[to_additive mul_nsmul']
theorem pow_mulₓ (a : M) (m n : ℕ) : a ^ (m * n) = (a ^ m) ^ n := by
  induction' n with n ih
  · rw [Nat.mul_zero, pow_zeroₓ, pow_zeroₓ]
    
  · rw [Nat.mul_succ, pow_addₓ, pow_succ'ₓ, ih]
    

@[to_additive nsmul_left_comm]
theorem pow_right_comm (a : M) (m n : ℕ) : (a ^ m) ^ n = (a ^ n) ^ m := by
  rw [← pow_mulₓ, Nat.mul_comm, pow_mulₓ]

@[to_additive mul_nsmul]
theorem pow_mul' (a : M) (m n : ℕ) : a ^ (m * n) = (a ^ n) ^ m := by
  rw [Nat.mul_comm, pow_mulₓ]

@[to_additive nsmul_add_sub_nsmul]
theorem pow_mul_pow_sub (a : M) {m n : ℕ} (h : m ≤ n) : a ^ m * a ^ (n - m) = a ^ n := by
  rw [← pow_addₓ, Nat.add_comm, tsub_add_cancel_of_le h]

@[to_additive sub_nsmul_nsmul_add]
theorem pow_sub_mul_pow (a : M) {m n : ℕ} (h : m ≤ n) : a ^ (n - m) * a ^ m = a ^ n := by
  rw [← pow_addₓ, tsub_add_cancel_of_le h]

@[to_additive bit0_nsmul]
theorem pow_bit0 (a : M) (n : ℕ) : a ^ bit0 n = a ^ n * a ^ n :=
  pow_addₓ _ _ _

@[to_additive bit1_nsmul]
theorem pow_bit1 (a : M) (n : ℕ) : a ^ bit1 n = a ^ n * a ^ n * a := by
  rw [bit1, pow_succ'ₓ, pow_bit0]

@[to_additive]
theorem pow_mul_commₓ (a : M) (m n : ℕ) : a ^ m * a ^ n = a ^ n * a ^ m :=
  Commute.pow_pow_self a m n

@[to_additive]
theorem Commute.mul_pow {a b : M} (h : Commute a b) (n : ℕ) : (a * b) ^ n = a ^ n * b ^ n :=
  (Nat.recOn n
      (by
        simp only [pow_zeroₓ, one_mulₓ]))
    fun n ihn => by
    simp only [pow_succₓ, ihn, ← mul_assoc, (h.pow_left n).right_comm]

@[to_additive bit0_nsmul']
theorem pow_bit0' (a : M) (n : ℕ) : a ^ bit0 n = (a * a) ^ n := by
  rw [pow_bit0, (Commute.refl a).mul_pow]

@[to_additive bit1_nsmul']
theorem pow_bit1' (a : M) (n : ℕ) : a ^ bit1 n = (a * a) ^ n * a := by
  rw [bit1, pow_succ'ₓ, pow_bit0']

theorem dvd_pow {x y : M} (hxy : x ∣ y) : ∀ {n : ℕ} hn : n ≠ 0, x ∣ y ^ n
  | 0, hn => (hn rfl).elim
  | n + 1, hn => by
    rw [pow_succₓ]
    exact hxy.mul_right _

alias dvd_pow ← Dvd.Dvd.pow

theorem dvd_pow_self (a : M) {n : ℕ} (hn : n ≠ 0) : a ∣ a ^ n :=
  dvd_rfl.pow hn

end Monoidₓ

/-!
### Commutative (additive) monoid
-/


section CommMonoidₓ

variable [CommMonoidₓ M] [AddCommMonoidₓ A]

@[to_additive nsmul_add]
theorem mul_powₓ (a b : M) (n : ℕ) : (a * b) ^ n = a ^ n * b ^ n :=
  (Commute.all a b).mul_pow n

/-- The `n`th power map on a commutative monoid for a natural `n`, considered as a morphism of
monoids. -/
@[to_additive
      "Multiplication by a natural `n` on a commutative additive\nmonoid, considered as a morphism of additive monoids.",
  simps]
def powMonoidHom (n : ℕ) : M →* M where
  toFun := (· ^ n)
  map_one' := one_pow _
  map_mul' := fun a b => mul_powₓ a b n

-- the below line causes the linter to complain :-/
-- attribute [simps] pow_monoid_hom nsmul_add_monoid_hom
end CommMonoidₓ

section DivInvMonoidₓ

variable [DivInvMonoidₓ G]

open Int

@[simp, to_additive one_zsmul]
theorem zpow_one (a : G) : a ^ (1 : ℤ) = a := by
  convert pow_oneₓ a using 1
  exact zpow_coe_nat a 1

@[to_additive two_zsmul]
theorem zpow_two (a : G) : a ^ (2 : ℤ) = a * a := by
  convert pow_two a using 1
  exact zpow_coe_nat a 2

@[to_additive neg_one_zsmul]
theorem zpow_neg_one (x : G) : x ^ (-1 : ℤ) = x⁻¹ :=
  (zpow_neg_succ_of_nat x 0).trans <| congr_argₓ Inv.inv (pow_oneₓ x)

@[to_additive]
theorem zpow_neg_coe_of_pos (a : G) : ∀ {n : ℕ}, 0 < n → a ^ -(n : ℤ) = (a ^ n)⁻¹
  | n + 1, _ => zpow_neg_succ_of_nat _ _

end DivInvMonoidₓ

section Groupₓ

variable [Groupₓ G] [Groupₓ H] [AddGroupₓ A] [AddGroupₓ B]

open Int

section Nat

@[simp, to_additive]
theorem inv_pow (a : G) (n : ℕ) : a⁻¹ ^ n = (a ^ n)⁻¹ := by
  induction' n with n ih
  · rw [pow_zeroₓ, pow_zeroₓ, inv_one]
    
  · rw [pow_succ'ₓ, pow_succₓ, ih, mul_inv_rev]
    

-- rename to sub_nsmul?
@[to_additive]
theorem pow_sub (a : G) {m n : ℕ} (h : n ≤ m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ :=
  have h1 : m - n + n = m := tsub_add_cancel_of_le h
  have h2 : a ^ (m - n) * a ^ n = a ^ m := by
    rw [← pow_addₓ, h1]
  eq_mul_inv_of_mul_eq h2

@[to_additive]
theorem pow_inv_comm (a : G) (m n : ℕ) : a⁻¹ ^ m * a ^ n = a ^ n * a⁻¹ ^ m :=
  (Commute.refl a).inv_left.pow_pow m n

@[to_additive sub_nsmul_neg]
theorem inv_pow_sub (a : G) {m n : ℕ} (h : n ≤ m) : a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n := by
  rw [pow_sub a⁻¹ h, inv_pow, inv_pow, inv_invₓ]

end Nat

-- the attributes are intentionally out of order. `smul_zero` proves `zsmul_zero`.
@[to_additive zsmul_zero, simp]
theorem one_zpow : ∀ n : ℤ, (1 : G) ^ n = 1
  | (n : ℕ) => by
    rw [zpow_coe_nat, one_pow]
  | -[1+ n] => by
    rw [zpow_neg_succ_of_nat, one_pow, inv_one]

@[simp, to_additive neg_zsmul]
theorem zpow_neg (a : G) : ∀ n : ℤ, a ^ -n = (a ^ n)⁻¹
  | (n + 1 : ℕ) => DivInvMonoidₓ.zpow_neg' _ _
  | 0 => by
    change a ^ (0 : ℤ) = (a ^ (0 : ℤ))⁻¹
    simp
  | -[1+ n] => by
    rw [zpow_neg_succ_of_nat, inv_invₓ, ← zpow_coe_nat]
    rfl

@[to_additive neg_one_zsmul_add]
theorem mul_zpow_neg_one (a b : G) : (a * b) ^ -(1 : ℤ) = b ^ -(1 : ℤ) * a ^ -(1 : ℤ) := by
  simp only [mul_inv_rev, zpow_one, zpow_neg]

@[to_additive zsmul_neg]
theorem inv_zpow (a : G) : ∀ n : ℤ, a⁻¹ ^ n = (a ^ n)⁻¹
  | (n : ℕ) => by
    rw [zpow_coe_nat, zpow_coe_nat, inv_pow]
  | -[1+ n] => by
    rw [zpow_neg_succ_of_nat, zpow_neg_succ_of_nat, inv_pow]

@[to_additive AddCommute.zsmul_add]
theorem Commute.mul_zpow {a b : G} (h : Commute a b) : ∀ n : ℤ, (a * b) ^ n = a ^ n * b ^ n
  | (n : ℕ) => by
    simp [zpow_coe_nat, h.mul_pow n]
  | -[1+ n] => by
    simp [h.mul_pow, (h.pow_pow n.succ n.succ).inv_inv.symm.Eq]

end Groupₓ

section CommGroupₓ

variable [CommGroupₓ G] [AddCommGroupₓ A]

@[to_additive zsmul_add]
theorem mul_zpow (a b : G) (n : ℤ) : (a * b) ^ n = a ^ n * b ^ n :=
  (Commute.all a b).mul_zpow n

@[to_additive zsmul_sub]
theorem div_zpow (a b : G) (n : ℤ) : (a / b) ^ n = a ^ n / b ^ n := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_zpow, inv_zpow]

/-- The `n`th power map (`n` an integer) on a commutative group, considered as a group
homomorphism. -/
@[to_additive
      "Multiplication by an integer `n` on a commutative additive group, considered as an\nadditive group homomorphism.",
  simps]
def zpowGroupHom (n : ℤ) : G →* G where
  toFun := (· ^ n)
  map_one' := one_zpow n
  map_mul' := fun a b => mul_zpow a b n

end CommGroupₓ

theorem zero_pow [MonoidWithZeroₓ R] : ∀ {n : ℕ}, 0 < n → (0 : R) ^ n = 0
  | n + 1, _ => by
    rw [pow_succₓ, zero_mul]

theorem zero_pow_eq [MonoidWithZeroₓ R] (n : ℕ) : (0 : R) ^ n = if n = 0 then 1 else 0 := by
  split_ifs with h
  · rw [h, pow_zeroₓ]
    
  · rw [zero_pow (Nat.pos_of_ne_zeroₓ h)]
    

theorem pow_eq_zero_of_le [MonoidWithZeroₓ M] {x : M} {n m : ℕ} (hn : n ≤ m) (hx : x ^ n = 0) : x ^ m = 0 := by
  rw [← tsub_add_cancel_of_le hn, pow_addₓ, hx, mul_zero]

namespace RingHom

variable [Semiringₓ R] [Semiringₓ S]

protected theorem map_pow (f : R →+* S) a : ∀ n : ℕ, f (a ^ n) = f a ^ n :=
  map_pow f a

end RingHom

theorem pow_dvd_pow [Monoidₓ R] (a : R) {m n : ℕ} (h : m ≤ n) : a ^ m ∣ a ^ n :=
  ⟨a ^ (n - m), by
    rw [← pow_addₓ, Nat.add_comm, tsub_add_cancel_of_le h]⟩

theorem pow_dvd_pow_of_dvd [CommMonoidₓ R] {a b : R} (h : a ∣ b) : ∀ n : ℕ, a ^ n ∣ b ^ n
  | 0 => by
    rw [pow_zeroₓ, pow_zeroₓ]
  | n + 1 => by
    rw [pow_succₓ, pow_succₓ]
    exact mul_dvd_mul h (pow_dvd_pow_of_dvd n)

theorem pow_eq_zero [MonoidWithZeroₓ R] [NoZeroDivisors R] {x : R} {n : ℕ} (H : x ^ n = 0) : x = 0 := by
  induction' n with n ih
  · rw [pow_zeroₓ] at H
    rw [← mul_oneₓ x, H, mul_zero]
    
  · rw [pow_succₓ] at H
    exact Or.cases_on (mul_eq_zero.1 H) id ih
    

@[simp]
theorem pow_eq_zero_iff [MonoidWithZeroₓ R] [NoZeroDivisors R] {a : R} {n : ℕ} (hn : 0 < n) : a ^ n = 0 ↔ a = 0 := by
  refine' ⟨pow_eq_zero, _⟩
  rintro rfl
  exact zero_pow hn

theorem pow_ne_zero_iff [MonoidWithZeroₓ R] [NoZeroDivisors R] {a : R} {n : ℕ} (hn : 0 < n) : a ^ n ≠ 0 ↔ a ≠ 0 :=
  (pow_eq_zero_iff hn).Not

@[field_simps]
theorem pow_ne_zero [MonoidWithZeroₓ R] [NoZeroDivisors R] {a : R} (n : ℕ) (h : a ≠ 0) : a ^ n ≠ 0 :=
  mt pow_eq_zero h

theorem sq_eq_zero_iff [MonoidWithZeroₓ R] [NoZeroDivisors R] {a : R} : a ^ 2 = 0 ↔ a = 0 :=
  pow_eq_zero_iff two_pos

theorem pow_dvd_pow_iff [CancelCommMonoidWithZero R] {x : R} {n m : ℕ} (h0 : x ≠ 0) (h1 : ¬IsUnit x) :
    x ^ n ∣ x ^ m ↔ n ≤ m := by
  constructor
  · intro h
    rw [← not_ltₓ]
    intro hmn
    apply h1
    have : x ^ m * x ∣ x ^ m * 1 := by
      rw [← pow_succ'ₓ, mul_oneₓ]
      exact (pow_dvd_pow _ (Nat.succ_le_of_ltₓ hmn)).trans h
    rwa [mul_dvd_mul_iff_left, ← is_unit_iff_dvd_one] at this
    apply pow_ne_zero m h0
    
  · apply pow_dvd_pow
    

section Semiringₓ

variable [Semiringₓ R]

theorem min_pow_dvd_add {n m : ℕ} {a b c : R} (ha : c ^ n ∣ a) (hb : c ^ m ∣ b) : c ^ min n m ∣ a + b := by
  replace ha := (pow_dvd_pow c (min_le_leftₓ n m)).trans ha
  replace hb := (pow_dvd_pow c (min_le_rightₓ n m)).trans hb
  exact dvd_add ha hb

end Semiringₓ

section CommSemiringₓ

variable [CommSemiringₓ R]

theorem add_sq (a b : R) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  simp only [sq, add_mul_self_eq]

theorem add_sq' (a b : R) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  rw [add_sq, add_assocₓ, add_commₓ _ (b ^ 2), add_assocₓ]

alias add_sq ← add_pow_two

end CommSemiringₓ

section HasDistribNeg

variable [Monoidₓ R] [HasDistribNeg R]

variable (R)

theorem neg_one_pow_eq_or : ∀ n : ℕ, (-1 : R) ^ n = 1 ∨ (-1 : R) ^ n = -1
  | 0 => Or.inl (pow_zeroₓ _)
  | n + 1 =>
    (neg_one_pow_eq_or n).swap.imp
      (fun h => by
        rw [pow_succₓ, h, neg_one_mul, neg_negₓ])
      fun h => by
      rw [pow_succₓ, h, mul_oneₓ]

variable {R}

theorem neg_pow (a : R) (n : ℕ) : -a ^ n = -1 ^ n * a ^ n :=
  neg_one_mul a ▸ (Commute.neg_one_left a).mul_pow n

@[simp]
theorem neg_pow_bit0 (a : R) (n : ℕ) : -a ^ bit0 n = a ^ bit0 n := by
  rw [pow_bit0', neg_mul_neg, pow_bit0']

@[simp]
theorem neg_pow_bit1 (a : R) (n : ℕ) : -a ^ bit1 n = -(a ^ bit1 n) := by
  simp only [bit1, pow_succₓ, neg_pow_bit0, neg_mul_eq_neg_mulₓ]

@[simp]
theorem neg_sq (a : R) : -a ^ 2 = a ^ 2 := by
  simp [sq]

@[simp]
theorem neg_one_sq : (-1 : R) ^ 2 = 1 := by
  rw [neg_sq, one_pow]

alias neg_sq ← neg_pow_two

alias neg_one_sq ← neg_one_pow_two

end HasDistribNeg

section Ringₓ

variable [Ringₓ R]

@[simp]
theorem neg_one_pow_mul_eq_zero_iff {n : ℕ} {r : R} : -1 ^ n * r = 0 ↔ r = 0 := by
  rcases neg_one_pow_eq_or R n with ⟨⟩ <;> simp [h]

@[simp]
theorem mul_neg_one_pow_eq_zero_iff {n : ℕ} {r : R} : r * -1 ^ n = 0 ↔ r = 0 := by
  rcases neg_one_pow_eq_or R n with ⟨⟩ <;> simp [h]

end Ringₓ

section CommRingₓ

variable [CommRingₓ R]

theorem sq_sub_sq (a b : R) : a ^ 2 - b ^ 2 = (a + b) * (a - b) := by
  rw [sq, sq, mul_self_sub_mul_self]

alias sq_sub_sq ← pow_two_sub_pow_two

theorem eq_or_eq_neg_of_sq_eq_sq [NoZeroDivisors R] (a b : R) (h : a ^ 2 = b ^ 2) : a = b ∨ a = -b := by
  rwa [← add_eq_zero_iff_eq_neg, ← sub_eq_zero, or_comm, ← mul_eq_zero, ← sq_sub_sq a b, sub_eq_zero]

theorem sub_sq (a b : R) : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by
  rw [sub_eq_add_neg, add_sq, neg_sq, mul_neg, ← sub_eq_add_neg]

alias sub_sq ← sub_pow_two

theorem sub_sq' (a b : R) : (a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b := by
  rw [sub_eq_add_neg, add_sq', neg_sq, mul_neg, ← sub_eq_add_neg]

-- Copies of the above comm_ring lemmas for `units R`.
namespace Units

theorem eq_or_eq_neg_of_sq_eq_sq [NoZeroDivisors R] (a b : Rˣ) (h : a ^ 2 = b ^ 2) : a = b ∨ a = -b := by
  refine' (eq_or_eq_neg_of_sq_eq_sq _ _ _).imp (fun h => Units.ext h) fun h => Units.ext h
  replace h := congr_argₓ (coe : Rˣ → R) h
  rwa [Units.coe_pow, Units.coe_pow] at h

end Units

end CommRingₓ

theorem of_add_nsmul [AddMonoidₓ A] (x : A) (n : ℕ) : Multiplicative.ofAdd (n • x) = Multiplicative.ofAdd x ^ n :=
  rfl

theorem of_add_zsmul [SubNegMonoidₓ A] (x : A) (n : ℤ) : Multiplicative.ofAdd (n • x) = Multiplicative.ofAdd x ^ n :=
  rfl

theorem of_mul_pow [Monoidₓ A] (x : A) (n : ℕ) : Additive.ofMul (x ^ n) = n • Additive.ofMul x :=
  rfl

theorem of_mul_zpow [DivInvMonoidₓ G] (x : G) (n : ℤ) : Additive.ofMul (x ^ n) = n • Additive.ofMul x :=
  rfl

@[simp, to_additive]
theorem SemiconjBy.zpow_right [Groupₓ G] {a x y : G} (h : SemiconjBy a x y) : ∀ m : ℤ, SemiconjBy a (x ^ m) (y ^ m)
  | (n : ℕ) => by
    simp [zpow_coe_nat, h.pow_right n]
  | -[1+ n] => by
    simp [(h.pow_right n.succ).inv_right]

namespace Commute

variable [Groupₓ G] {a b : G}

@[simp, to_additive]
theorem zpow_right (h : Commute a b) (m : ℤ) : Commute a (b ^ m) :=
  h.zpow_right m

@[simp, to_additive]
theorem zpow_left (h : Commute a b) (m : ℤ) : Commute (a ^ m) b :=
  (h.symm.zpow_right m).symm

@[to_additive]
theorem zpow_zpow (h : Commute a b) (m n : ℤ) : Commute (a ^ m) (b ^ n) :=
  (h.zpow_left m).zpow_right n

variable (a) (m n : ℤ)

@[simp, to_additive]
theorem self_zpow : Commute a (a ^ n) :=
  (Commute.refl a).zpow_right n

@[simp, to_additive]
theorem zpow_self : Commute (a ^ n) a :=
  (Commute.refl a).zpow_left n

@[simp, to_additive]
theorem zpow_zpow_self : Commute (a ^ m) (a ^ n) :=
  (Commute.refl a).zpow_zpow m n

end Commute

