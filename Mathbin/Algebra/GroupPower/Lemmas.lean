/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import Mathbin.Algebra.Invertible
import Mathbin.Data.Int.Cast

/-!
# Lemmas about power operations on monoids and groups

This file contains lemmas about `monoid.pow`, `group.pow`, `nsmul`, `zsmul`
which require additional imports besides those available in `algebra.group_power.basic`.
-/


universe u v w x y z u₁ u₂

variable {M : Type u} {N : Type v} {G : Type w} {H : Type x} {A : Type y} {B : Type z} {R : Type u₁} {S : Type u₂}

/-!
### (Additive) monoid
-/


section Monoidₓ

variable [Monoidₓ M] [Monoidₓ N] [AddMonoidₓ A] [AddMonoidₓ B]

@[simp]
theorem nsmul_one [One A] : ∀ n : ℕ, n • (1 : A) = n := by
  refine' eq_nat_cast' (⟨_, _, _⟩ : ℕ →+ A) _
  · simp [zero_nsmul]
    
  · simp [add_nsmul]
    
  · simp
    

instance invertiblePow (m : M) [Invertible m] (n : ℕ) : Invertible (m ^ n) where
  invOf := ⅟ m ^ n
  inv_of_mul_self := by
    rw [← (commute_inv_of m).symm.mul_pow, inv_of_mul_self, one_pow]
  mul_inv_of_self := by
    rw [← (commute_inv_of m).mul_pow, mul_inv_of_self, one_pow]

theorem inv_of_pow (m : M) [Invertible m] (n : ℕ) [Invertible (m ^ n)] : ⅟ (m ^ n) = ⅟ m ^ n :=
  @invertible_unique M _ (m ^ n) (m ^ n) rfl ‹_› (invertiblePow m n)

theorem IsUnit.pow {m : M} (n : ℕ) : IsUnit m → IsUnit (m ^ n) := fun ⟨u, hu⟩ =>
  ⟨u ^ n, by
    simp [*]⟩

@[simp]
theorem is_unit_pow_succ_iff {m : M} {n : ℕ} : IsUnit (m ^ (n + 1)) ↔ IsUnit m := by
  refine' ⟨_, fun h => h.pow _⟩
  rw [pow_succₓ, ((Commute.refl _).pow_right _).is_unit_mul_iff]
  exact And.left

theorem is_unit_pos_pow_iff {m : M} : ∀ {n : ℕ} h : 0 < n, IsUnit (m ^ n) ↔ IsUnit m
  | n + 1, _ => is_unit_pow_succ_iff

/-- If `x ^ n.succ = 1` then `x` has an inverse, `x^n`. -/
def invertibleOfPowSuccEqOne (x : M) (n : ℕ) (hx : x ^ n.succ = 1) : Invertible x :=
  ⟨x ^ n, (pow_succ'ₓ x n).symm.trans hx, (pow_succₓ x n).symm.trans hx⟩

/-- If `x ^ n = 1` then `x` has an inverse, `x^(n - 1)`. -/
def invertibleOfPowEqOne (x : M) (n : ℕ) (hx : x ^ n = 1) (hn : 0 < n) : Invertible x := by
  apply invertibleOfPowSuccEqOne x (n - 1)
  convert hx
  exact tsub_add_cancel_of_le (Nat.succ_le_of_ltₓ hn)

theorem is_unit_of_pow_eq_one (x : M) (n : ℕ) (hx : x ^ n = 1) (hn : 0 < n) : IsUnit x :=
  have := invertibleOfPowEqOne x n hx hn
  is_unit_of_invertible x

theorem smul_pow [MulAction M N] [IsScalarTower M N N] [SmulCommClass M N N] (k : M) (x : N) (p : ℕ) :
    (k • x) ^ p = k ^ p • x ^ p := by
  induction' p with p IH
  · simp
    
  · rw [pow_succ'ₓ, IH, smul_mul_smul, ← pow_succ'ₓ, ← pow_succ'ₓ]
    

@[simp]
theorem smul_pow' [MulDistribMulAction M N] (x : M) (m : N) (n : ℕ) : x • m ^ n = (x • m) ^ n := by
  induction' n with n ih
  · rw [pow_zeroₓ, pow_zeroₓ]
    exact smul_one x
    
  · rw [pow_succₓ, pow_succₓ]
    exact (smul_mul' x m (m ^ n)).trans (congr_argₓ _ ih)
    

end Monoidₓ

section Groupₓ

variable [Groupₓ G] [Groupₓ H] [AddGroupₓ A] [AddGroupₓ B]

open Int

attribute [local ematch] le_of_ltₓ

open Nat

theorem zsmul_one [One A] (n : ℤ) : n • (1 : A) = n := by
  cases n <;> simp

@[to_additive add_one_zsmul]
theorem zpow_add_one (a : G) : ∀ n : ℤ, a ^ (n + 1) = a ^ n * a
  | of_nat n => by
    simp [← Int.coe_nat_succ, pow_succ'ₓ]
  | -[1+ 0] => by
    simp [Int.neg_succ_of_nat_eq]
  | -[1+ n + 1] => by
    rw [Int.neg_succ_of_nat_eq, zpow_neg, neg_add, neg_add_cancel_right, zpow_neg, ← Int.coe_nat_succ, zpow_coe_nat,
      zpow_coe_nat, pow_succₓ _ (n + 1), mul_inv_rev, inv_mul_cancel_right]

@[to_additive zsmul_sub_one]
theorem zpow_sub_one (a : G) (n : ℤ) : a ^ (n - 1) = a ^ n * a⁻¹ :=
  calc
    a ^ (n - 1) = a ^ (n - 1) * a * a⁻¹ := (mul_inv_cancel_rightₓ _ _).symm
    _ = a ^ n * a⁻¹ := by
      rw [← zpow_add_one, sub_add_cancel]
    

@[to_additive add_zsmul]
theorem zpow_add (a : G) (m n : ℤ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction' n using Int.induction_on with n ihn n ihn
  case hz =>
    simp
  · simp only [← add_assocₓ, zpow_add_one, ihn, mul_assoc]
    
  · rw [zpow_sub_one, ← mul_assoc, ← ihn, ← zpow_sub_one, add_sub_assoc]
    

@[to_additive add_zsmul_self]
theorem mul_self_zpow (b : G) (m : ℤ) : b * b ^ m = b ^ (m + 1) := by
  conv_lhs => congr rw [← zpow_one b]
  rw [← zpow_add, add_commₓ]

@[to_additive add_self_zsmul]
theorem mul_zpow_self (b : G) (m : ℤ) : b ^ m * b = b ^ (m + 1) := by
  conv_lhs => congr skip rw [← zpow_one b]
  rw [← zpow_add, add_commₓ]

@[to_additive sub_zsmul]
theorem zpow_sub (a : G) (m n : ℤ) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ := by
  rw [sub_eq_add_neg, zpow_add, zpow_neg]

@[to_additive one_add_zsmul]
theorem zpow_one_add (a : G) (i : ℤ) : a ^ (1 + i) = a * a ^ i := by
  rw [zpow_add, zpow_one]

@[to_additive]
theorem zpow_mul_comm (a : G) (i j : ℤ) : a ^ i * a ^ j = a ^ j * a ^ i := by
  rw [← zpow_add, ← zpow_add, add_commₓ]

-- note that `mul_zsmul` and `zpow_mul` have the primes swapped since their argument order
-- and therefore the more "natural" choice of lemma is reversed.
@[to_additive mul_zsmul']
theorem zpow_mul (a : G) (m n : ℤ) : a ^ (m * n) = (a ^ m) ^ n :=
  Int.induction_on n
    (by
      simp )
    (fun n ihn => by
      simp [mul_addₓ, zpow_add, ihn])
    fun n ihn => by
    simp only [mul_sub, zpow_sub, ihn, mul_oneₓ, zpow_one]

@[to_additive mul_zsmul]
theorem zpow_mul' (a : G) (m n : ℤ) : a ^ (m * n) = (a ^ n) ^ m := by
  rw [mul_comm, zpow_mul]

@[to_additive bit0_zsmul]
theorem zpow_bit0 (a : G) (n : ℤ) : a ^ bit0 n = a ^ n * a ^ n :=
  zpow_add _ _ _

@[to_additive bit1_zsmul]
theorem zpow_bit1 (a : G) (n : ℤ) : a ^ bit1 n = a ^ n * a ^ n * a := by
  rw [bit1, zpow_add, zpow_bit0, zpow_one]

end Groupₓ

section OrderedAddCommGroup

variable [OrderedAddCommGroup A]

/-! Lemmas about `zsmul` under ordering,  placed here (rather than in `algebra.group_power.order`
with their friends) because they require facts from `data.int.basic`-/


open Int

theorem zsmul_pos {a : A} (ha : 0 < a) {k : ℤ} (hk : (0 : ℤ) < k) : 0 < k • a := by
  lift k to ℕ using Int.le_of_ltₓ hk
  rw [coe_nat_zsmul]
  apply nsmul_pos ha
  exact (coe_nat_pos.mp hk).ne'

theorem zsmul_strict_mono_left {a : A} (ha : 0 < a) : StrictMono fun n : ℤ => n • a := fun n m h =>
  calc
    n • a = n • a + 0 := (add_zeroₓ _).symm
    _ < n • a + (m - n) • a := add_lt_add_left (zsmul_pos ha (sub_pos.mpr h)) _
    _ = m • a := by
      rw [← add_zsmul]
      simp
    

theorem zsmul_mono_left {a : A} (ha : 0 ≤ a) : Monotone fun n : ℤ => n • a := fun n m h =>
  calc
    n • a = n • a + 0 := (add_zeroₓ _).symm
    _ ≤ n • a + (m - n) • a := add_le_add_left (zsmul_nonneg ha (sub_nonneg.mpr h)) _
    _ = m • a := by
      rw [← add_zsmul]
      simp
    

theorem zsmul_le_zsmul {a : A} {n m : ℤ} (ha : 0 ≤ a) (h : n ≤ m) : n • a ≤ m • a :=
  zsmul_mono_left ha h

theorem zsmul_lt_zsmul {a : A} {n m : ℤ} (ha : 0 < a) (h : n < m) : n • a < m • a :=
  zsmul_strict_mono_left ha h

theorem zsmul_le_zsmul_iff {a : A} {n m : ℤ} (ha : 0 < a) : n • a ≤ m • a ↔ n ≤ m :=
  (zsmul_strict_mono_left ha).le_iff_le

theorem zsmul_lt_zsmul_iff {a : A} {n m : ℤ} (ha : 0 < a) : n • a < m • a ↔ n < m :=
  (zsmul_strict_mono_left ha).lt_iff_lt

variable (A)

theorem zsmul_strict_mono_right {n : ℤ} (hn : 0 < n) : StrictMono ((· • ·) n : A → A) := fun a b hab => by
  rw [← sub_pos] at hab
  rw [← sub_pos, ← zsmul_sub]
  exact zsmul_pos hab hn

theorem zsmul_mono_right {n : ℤ} (hn : 0 ≤ n) : Monotone ((· • ·) n : A → A) := fun a b hab => by
  rw [← sub_nonneg] at hab
  rw [← sub_nonneg, ← zsmul_sub]
  exact zsmul_nonneg hab hn

variable {A}

theorem zsmul_le_zsmul' {n : ℤ} (hn : 0 ≤ n) {a₁ a₂ : A} (h : a₁ ≤ a₂) : n • a₁ ≤ n • a₂ :=
  zsmul_mono_right A hn h

theorem zsmul_lt_zsmul' {n : ℤ} (hn : 0 < n) {a₁ a₂ : A} (h : a₁ < a₂) : n • a₁ < n • a₂ :=
  zsmul_strict_mono_right A hn h

theorem abs_nsmul {α : Type _} [LinearOrderedAddCommGroup α] (n : ℕ) (a : α) : abs (n • a) = n • abs a := by
  cases' le_totalₓ a 0 with hneg hpos
  · rw [abs_of_nonpos hneg, ← abs_neg, ← neg_nsmul, abs_of_nonneg]
    exact nsmul_nonneg (neg_nonneg.mpr hneg) n
    
  · rw [abs_of_nonneg hpos, abs_of_nonneg]
    exact nsmul_nonneg hpos n
    

theorem abs_zsmul {α : Type _} [LinearOrderedAddCommGroup α] (n : ℤ) (a : α) : abs (n • a) = abs n • abs a := by
  by_cases' n0 : 0 ≤ n
  · lift n to ℕ using n0
    simp only [abs_nsmul, coe_nat_abs, coe_nat_zsmul]
    
  · lift -n to ℕ using Int.le_of_ltₓ (neg_pos.mpr (not_le.mp n0)) with m h
    rw [← abs_neg (n • a), ← neg_zsmul, ← abs_neg n, ← h, coe_nat_zsmul, coe_nat_abs, coe_nat_zsmul]
    exact abs_nsmul m _
    

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:50: missing argument
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:59:31: expecting tactic arg
theorem abs_add_eq_add_abs_le {α : Type _} [LinearOrderedAddCommGroup α] {a b : α} (hle : a ≤ b) :
    abs (a + b) = abs a + abs b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  by_cases' a0 : 0 ≤ a <;> by_cases' b0 : 0 ≤ b
  · simp [a0, b0, abs_of_nonneg, add_nonneg a0 b0]
    
  · exact (lt_irreflₓ (0 : α) (a0.trans_lt (hle.trans_lt (not_le.mp b0)))).elim
    
  any_goals {
  }
  obtain F := not_le.mp a0
  have : (abs (a + b) = -a + b ↔ b ≤ 0) ↔ (abs (a + b) = abs a + abs b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0) := by
    simp [a0, b0, abs_of_neg, abs_of_nonneg, F, F.le]
  refine'
    this.mp
      ⟨fun h => _, fun h => by
        simp only [le_antisymmₓ h b0, abs_of_neg F, add_zeroₓ]⟩
  by_cases' ba : a + b ≤ 0
  · refine' le_of_eqₓ (eq_zero_of_neg_eq _)
    rwa [abs_of_nonpos ba, neg_add_rev, add_commₓ, add_right_injₓ] at h
    
  · refine' (lt_irreflₓ (0 : α) _).elim
    rw [abs_of_pos (not_le.mp ba), add_left_injₓ] at h
    rwa [eq_zero_of_neg_eq h.symm] at F
    

theorem abs_add_eq_add_abs_iff {α : Type _} [LinearOrderedAddCommGroup α] (a b : α) :
    abs (a + b) = abs a + abs b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  by_cases' ab : a ≤ b
  · exact abs_add_eq_add_abs_le ab
    
  · rw [add_commₓ a, add_commₓ (abs _), abs_add_eq_add_abs_le (not_le.mp ab).le, And.comm, @And.comm (b ≤ 0) _]
    

end OrderedAddCommGroup

section LinearOrderedAddCommGroup

variable [LinearOrderedAddCommGroup A]

theorem zsmul_le_zsmul_iff' {n : ℤ} (hn : 0 < n) {a₁ a₂ : A} : n • a₁ ≤ n • a₂ ↔ a₁ ≤ a₂ :=
  (zsmul_strict_mono_right A hn).le_iff_le

theorem zsmul_lt_zsmul_iff' {n : ℤ} (hn : 0 < n) {a₁ a₂ : A} : n • a₁ < n • a₂ ↔ a₁ < a₂ :=
  (zsmul_strict_mono_right A hn).lt_iff_lt

theorem nsmul_le_nsmul_iff {a : A} {n m : ℕ} (ha : 0 < a) : n • a ≤ m • a ↔ n ≤ m := by
  refine' ⟨fun h => _, nsmul_le_nsmul <| le_of_ltₓ ha⟩
  by_contra H
  exact lt_irreflₓ _ (lt_of_lt_of_leₓ (nsmul_lt_nsmul ha (not_le.mp H)) h)

theorem nsmul_lt_nsmul_iff {a : A} {n m : ℕ} (ha : 0 < a) : n • a < m • a ↔ n < m := by
  refine' ⟨fun h => _, nsmul_lt_nsmul ha⟩
  by_contra H
  exact lt_irreflₓ _ (lt_of_le_of_ltₓ (nsmul_le_nsmul (le_of_ltₓ ha) <| not_lt.mp H) h)

/-- See also `smul_right_injective`. TODO: provide a `no_zero_smul_divisors` instance. We can't
do that here because importing that definition would create import cycles. -/
theorem zsmul_right_injective {m : ℤ} (hm : m ≠ 0) : Function.Injective ((· • ·) m : A → A) := by
  cases hm.symm.lt_or_lt
  · exact (zsmul_strict_mono_right A h).Injective
    
  · intro a b hab
    refine' (zsmul_strict_mono_right A (neg_pos.mpr h)).Injective _
    rw [neg_zsmul, neg_zsmul, hab]
    

theorem zsmul_right_inj {a b : A} {m : ℤ} (hm : m ≠ 0) : m • a = m • b ↔ a = b :=
  (zsmul_right_injective hm).eq_iff

/-- Alias of `zsmul_right_inj`, for ease of discovery alongside `zsmul_le_zsmul_iff'` and
`zsmul_lt_zsmul_iff'`. -/
theorem zsmul_eq_zsmul_iff' {a b : A} {m : ℤ} (hm : m ≠ 0) : m • a = m • b ↔ a = b :=
  zsmul_right_inj hm

end LinearOrderedAddCommGroup

@[simp]
theorem WithBot.coe_nsmul [AddMonoidₓ A] (a : A) (n : ℕ) : ((n • a : A) : WithBot A) = n • a :=
  AddMonoidHom.map_nsmul ⟨(coe : A → WithBot A), WithBot.coe_zero, WithBot.coe_add⟩ a n

theorem nsmul_eq_mul' [Semiringₓ R] (a : R) (n : ℕ) : n • a = a * n := by
  induction' n with n ih <;> [rw [zero_nsmul, Nat.cast_zeroₓ, mul_zero],
    rw [succ_nsmul', ih, Nat.cast_succₓ, mul_addₓ, mul_oneₓ]]

@[simp]
theorem nsmul_eq_mul [Semiringₓ R] (n : ℕ) (a : R) : n • a = n * a := by
  rw [nsmul_eq_mul', (n.cast_commute a).Eq]

theorem mul_nsmul_left [Semiringₓ R] (a b : R) (n : ℕ) : n • (a * b) = a * n • b := by
  rw [nsmul_eq_mul', nsmul_eq_mul', mul_assoc]

theorem mul_nsmul_assoc [Semiringₓ R] (a b : R) (n : ℕ) : n • (a * b) = n • a * b := by
  rw [nsmul_eq_mul, nsmul_eq_mul, mul_assoc]

@[simp, norm_cast]
theorem Nat.cast_powₓ [Semiringₓ R] (n m : ℕ) : (↑(n ^ m) : R) = ↑n ^ m := by
  induction' m with m ih
  · rw [pow_zeroₓ, pow_zeroₓ]
    exact Nat.cast_oneₓ
    
  · rw [pow_succ'ₓ, pow_succ'ₓ, Nat.cast_mulₓ, ih]
    

@[simp, norm_cast]
theorem Int.coe_nat_pow (n m : ℕ) : ((n ^ m : ℕ) : ℤ) = n ^ m := by
  induction' m with m ih <;> [exact Int.coe_nat_one, rw [pow_succ'ₓ, pow_succ'ₓ, Int.coe_nat_mul, ih]]

theorem Int.nat_abs_pow (n : ℤ) (k : ℕ) : Int.natAbs (n ^ k) = Int.natAbs n ^ k := by
  induction' k with k ih <;> [rfl, rw [pow_succ'ₓ, Int.nat_abs_mul, pow_succ'ₓ, ih]]

-- The next four lemmas allow us to replace multiplication by a numeral with a `zsmul` expression.
-- They are used by the `noncomm_ring` tactic, to normalise expressions before passing to `abel`.
theorem bit0_mul [Ringₓ R] {n r : R} : bit0 n * r = (2 : ℤ) • (n * r) := by
  dsimp [bit0]
  rw [add_mulₓ, add_zsmul, one_zsmul]

theorem mul_bit0 [Ringₓ R] {n r : R} : r * bit0 n = (2 : ℤ) • (r * n) := by
  dsimp [bit0]
  rw [mul_addₓ, add_zsmul, one_zsmul]

theorem bit1_mul [Ringₓ R] {n r : R} : bit1 n * r = (2 : ℤ) • (n * r) + r := by
  dsimp [bit1]
  rw [add_mulₓ, bit0_mul, one_mulₓ]

theorem mul_bit1 [Ringₓ R] {n r : R} : r * bit1 n = (2 : ℤ) • (r * n) + r := by
  dsimp [bit1]
  rw [mul_addₓ, mul_bit0, mul_oneₓ]

@[simp]
theorem zsmul_eq_mul [Ringₓ R] (a : R) : ∀ n : ℤ, n • a = n * a
  | (n : ℕ) => by
    rw [coe_nat_zsmul, nsmul_eq_mul]
    rfl
  | -[1+ n] => by
    simp [Nat.cast_succₓ, neg_add_rev, Int.cast_neg_succ_of_nat, add_mulₓ]

theorem zsmul_eq_mul' [Ringₓ R] (a : R) (n : ℤ) : n • a = a * n := by
  rw [zsmul_eq_mul, (n.cast_commute a).Eq]

theorem mul_zsmul_left [Ringₓ R] (a b : R) (n : ℤ) : n • (a * b) = a * n • b := by
  rw [zsmul_eq_mul', zsmul_eq_mul', mul_assoc]

theorem mul_zsmul_assoc [Ringₓ R] (a b : R) (n : ℤ) : n • (a * b) = n • a * b := by
  rw [zsmul_eq_mul, zsmul_eq_mul, mul_assoc]

theorem zsmul_int_int (a b : ℤ) : a • b = a * b := by
  simp

theorem zsmul_int_one (n : ℤ) : n • 1 = n := by
  simp

@[simp, norm_cast]
theorem Int.cast_pow [Ringₓ R] (n : ℤ) (m : ℕ) : (↑(n ^ m) : R) = ↑n ^ m := by
  induction' m with m ih
  · rw [pow_zeroₓ, pow_zeroₓ, Int.cast_oneₓ]
    
  · rw [pow_succₓ, pow_succₓ, Int.cast_mul, ih]
    

theorem neg_one_pow_eq_pow_mod_two [Ringₓ R] {n : ℕ} : (-1 : R) ^ n = -1 ^ (n % 2) := by
  rw [← Nat.mod_add_divₓ n 2, pow_addₓ, pow_mulₓ] <;> simp [sq]

section OrderedSemiring

variable [OrderedSemiring R] {a : R}

/-- Bernoulli's inequality. This version works for semirings but requires
additional hypotheses `0 ≤ a * a` and `0 ≤ (1 + a) * (1 + a)`. -/
theorem one_add_mul_le_pow' (Hsq : 0 ≤ a * a) (Hsq' : 0 ≤ (1 + a) * (1 + a)) (H : 0 ≤ 2 + a) :
    ∀ n : ℕ, 1 + (n : R) * a ≤ (1 + a) ^ n
  | 0 => by
    simp
  | 1 => by
    simp
  | n + 2 =>
    have : 0 ≤ (n : R) * (a * a * (2 + a)) + a * a := add_nonneg (mul_nonneg n.cast_nonneg (mul_nonneg Hsq H)) Hsq
    calc
      1 + (↑(n + 2) : R) * a ≤ 1 + ↑(n + 2) * a + (n * (a * a * (2 + a)) + a * a) := (le_add_iff_nonneg_right _).2 this
      _ = (1 + a) * (1 + a) * (1 + n * a) := by
        simp [add_mulₓ, mul_addₓ, bit0, mul_assoc, (n.cast_commute (_ : R)).left_comm]
        ac_rfl
      _ ≤ (1 + a) * (1 + a) * (1 + a) ^ n := mul_le_mul_of_nonneg_left (one_add_mul_le_pow' n) Hsq'
      _ = (1 + a) ^ (n + 2) := by
        simp only [pow_succₓ, mul_assoc]
      

private theorem pow_le_pow_of_le_one_aux (h : 0 ≤ a) (ha : a ≤ 1) (i : ℕ) : ∀ k : ℕ, a ^ (i + k) ≤ a ^ i
  | 0 => by
    simp
  | k + 1 => by
    rw [← add_assocₓ, ← one_mulₓ (a ^ i), pow_succₓ]
    exact mul_le_mul ha (pow_le_pow_of_le_one_aux _) (pow_nonneg h _) zero_le_one

theorem pow_le_pow_of_le_one (h : 0 ≤ a) (ha : a ≤ 1) {i j : ℕ} (hij : i ≤ j) : a ^ j ≤ a ^ i := by
  let ⟨k, hk⟩ := Nat.exists_eq_add_of_le hij
  rw [hk] <;> exact pow_le_pow_of_le_one_aux h ha _ _

theorem pow_le_of_le_one (h₀ : 0 ≤ a) (h₁ : a ≤ 1) {n : ℕ} (hn : n ≠ 0) : a ^ n ≤ a :=
  (pow_oneₓ a).subst (pow_le_pow_of_le_one h₀ h₁ (Nat.pos_of_ne_zeroₓ hn))

theorem sq_le (h₀ : 0 ≤ a) (h₁ : a ≤ 1) : a ^ 2 ≤ a :=
  pow_le_of_le_one h₀ h₁ two_ne_zero

end OrderedSemiring

section LinearOrderedSemiring

variable [LinearOrderedSemiring R]

theorem sign_cases_of_C_mul_pow_nonneg {C r : R} (h : ∀ n : ℕ, 0 ≤ C * r ^ n) : C = 0 ∨ 0 < C ∧ 0 ≤ r := by
  have : 0 ≤ C := by
    simpa only [pow_zeroₓ, mul_oneₓ] using h 0
  refine' this.eq_or_lt.elim (fun h => Or.inl h.symm) fun hC => Or.inr ⟨hC, _⟩
  refine' nonneg_of_mul_nonneg_left _ hC
  simpa only [pow_oneₓ] using h 1

end LinearOrderedSemiring

section LinearOrderedRing

variable [LinearOrderedRing R] {a : R} {n : ℕ}

@[simp]
theorem abs_pow (a : R) (n : ℕ) : abs (a ^ n) = abs a ^ n :=
  (pow_abs a n).symm

@[simp]
theorem pow_bit1_neg_iff : a ^ bit1 n < 0 ↔ a < 0 :=
  ⟨fun h => not_leₓ.1 fun h' => not_leₓ.2 h <| pow_nonneg h' _, fun ha => pow_bit1_neg ha n⟩

@[simp]
theorem pow_bit1_nonneg_iff : 0 ≤ a ^ bit1 n ↔ 0 ≤ a :=
  le_iff_le_iff_lt_iff_lt.2 pow_bit1_neg_iff

@[simp]
theorem pow_bit1_nonpos_iff : a ^ bit1 n ≤ 0 ↔ a ≤ 0 := by
  simp only [le_iff_lt_or_eqₓ, pow_bit1_neg_iff, pow_eq_zero_iff (bit1_pos (zero_le n))]

@[simp]
theorem pow_bit1_pos_iff : 0 < a ^ bit1 n ↔ 0 < a :=
  lt_iff_lt_of_le_iff_le pow_bit1_nonpos_iff

theorem Even.pow_nonneg (hn : Even n) (a : R) : 0 ≤ a ^ n := by
  cases' hn with k hk <;> simpa only [hk, two_mul] using pow_bit0_nonneg a k

theorem Even.pow_pos (hn : Even n) (ha : a ≠ 0) : 0 < a ^ n := by
  cases' hn with k hk <;> simpa only [hk, two_mul] using pow_bit0_pos ha k

theorem Odd.pow_nonpos (hn : Odd n) (ha : a ≤ 0) : a ^ n ≤ 0 := by
  cases' hn with k hk <;> simpa only [hk, two_mul] using pow_bit1_nonpos_iff.mpr ha

theorem Odd.pow_neg (hn : Odd n) (ha : a < 0) : a ^ n < 0 := by
  cases' hn with k hk <;> simpa only [hk, two_mul] using pow_bit1_neg_iff.mpr ha

theorem Odd.pow_nonneg_iff (hn : Odd n) : 0 ≤ a ^ n ↔ 0 ≤ a :=
  ⟨fun h => le_of_not_ltₓ fun ha => h.not_lt <| hn.pow_neg ha, fun ha => pow_nonneg ha n⟩

theorem Odd.pow_nonpos_iff (hn : Odd n) : a ^ n ≤ 0 ↔ a ≤ 0 :=
  ⟨fun h => le_of_not_ltₓ fun ha => h.not_lt <| pow_pos ha _, hn.pow_nonpos⟩

theorem Odd.pow_pos_iff (hn : Odd n) : 0 < a ^ n ↔ 0 < a :=
  ⟨fun h => lt_of_not_ge' fun ha => h.not_le <| hn.pow_nonpos ha, fun ha => pow_pos ha n⟩

theorem Odd.pow_neg_iff (hn : Odd n) : a ^ n < 0 ↔ a < 0 :=
  ⟨fun h => lt_of_not_ge' fun ha => h.not_le <| pow_nonneg ha _, hn.pow_neg⟩

theorem Even.pow_pos_iff (hn : Even n) (h₀ : 0 < n) : 0 < a ^ n ↔ a ≠ 0 :=
  ⟨fun h ha => by
    rw [ha, zero_pow h₀] at h
    exact lt_irreflₓ 0 h, hn.pow_pos⟩

theorem Even.pow_abs {p : ℕ} (hp : Even p) (a : R) : abs a ^ p = a ^ p := by
  rw [← abs_pow, abs_eq_self]
  exact hp.pow_nonneg _

@[simp]
theorem pow_bit0_abs (a : R) (p : ℕ) : abs a ^ bit0 p = a ^ bit0 p :=
  (even_bit0 _).pow_abs _

theorem strict_mono_pow_bit1 (n : ℕ) : StrictMono fun a : R => a ^ bit1 n := by
  intro a b hab
  cases' le_totalₓ a 0 with ha ha
  · cases' le_or_ltₓ b 0 with hb hb
    · rw [← neg_lt_neg_iff, ← neg_pow_bit1, ← neg_pow_bit1]
      exact pow_lt_pow_of_lt_left (neg_lt_neg hab) (neg_nonneg.2 hb) (bit1_pos (zero_le n))
      
    · exact (pow_bit1_nonpos_iff.2 ha).trans_lt (pow_bit1_pos_iff.2 hb)
      
    
  · exact pow_lt_pow_of_lt_left hab ha (bit1_pos (zero_le n))
    

theorem Odd.strict_mono_pow (hn : Odd n) : StrictMono fun a : R => a ^ n := by
  cases' hn with k hk <;> simpa only [hk, two_mul] using strict_mono_pow_bit1 _

/-- Bernoulli's inequality for `n : ℕ`, `-2 ≤ a`. -/
theorem one_add_mul_le_pow (H : -2 ≤ a) (n : ℕ) : 1 + (n : R) * a ≤ (1 + a) ^ n :=
  one_add_mul_le_pow' (mul_self_nonneg _) (mul_self_nonneg _) (neg_le_iff_add_nonneg'.1 H) _

/-- Bernoulli's inequality reformulated to estimate `a^n`. -/
theorem one_add_mul_sub_le_pow (H : -1 ≤ a) (n : ℕ) : 1 + (n : R) * (a - 1) ≤ a ^ n := by
  have : -2 ≤ a - 1 := by
    rwa [bit0, neg_add, ← sub_eq_add_neg, sub_le_sub_iff_right]
  simpa only [add_sub_cancel'_right] using one_add_mul_le_pow this n

end LinearOrderedRing

/-- Bernoulli's inequality reformulated to estimate `(n : K)`. -/
theorem Nat.cast_le_pow_sub_div_sub {K : Type _} [LinearOrderedField K] {a : K} (H : 1 < a) (n : ℕ) :
    (n : K) ≤ (a ^ n - 1) / (a - 1) :=
  (le_div_iff (sub_pos.2 H)).2 <|
    le_sub_left_of_add_le <| one_add_mul_sub_le_pow ((neg_le_self <| @zero_le_one K _).trans H.le) _

/-- For any `a > 1` and a natural `n` we have `n ≤ a ^ n / (a - 1)`. See also
`nat.cast_le_pow_sub_div_sub` for a stronger inequality with `a ^ n - 1` in the numerator. -/
theorem Nat.cast_le_pow_div_sub {K : Type _} [LinearOrderedField K] {a : K} (H : 1 < a) (n : ℕ) :
    (n : K) ≤ a ^ n / (a - 1) :=
  (n.cast_le_pow_sub_div_sub H).trans <| div_le_div_of_le (sub_nonneg.2 H.le) (sub_le_self _ zero_le_one)

namespace Int

theorem units_sq (u : ℤˣ) : u ^ 2 = 1 :=
  (sq u).symm ▸ units_mul_self u

alias Int.units_sq ← Int.units_pow_two

theorem units_pow_eq_pow_mod_two (u : ℤˣ) (n : ℕ) : u ^ n = u ^ (n % 2) := by
  conv => lhs rw [← Nat.mod_add_divₓ n 2] <;> rw [pow_addₓ, pow_mulₓ, units_sq, one_pow, mul_oneₓ]

@[simp]
theorem nat_abs_sq (x : ℤ) : (x.natAbs ^ 2 : ℤ) = x ^ 2 := by
  rw [sq, Int.nat_abs_mul_self', sq]

alias Int.nat_abs_sq ← Int.nat_abs_pow_two

theorem abs_le_self_sq (a : ℤ) : (Int.natAbs a : ℤ) ≤ a ^ 2 := by
  rw [← Int.nat_abs_sq a, sq]
  norm_cast
  apply Nat.le_mul_self

alias Int.abs_le_self_sq ← Int.abs_le_self_pow_two

theorem le_self_sq (b : ℤ) : b ≤ b ^ 2 :=
  le_transₓ le_nat_abs (abs_le_self_sq _)

alias Int.le_self_sq ← Int.le_self_pow_two

theorem pow_right_injective {x : ℤ} (h : 1 < x.natAbs) : Function.Injective ((· ^ ·) x : ℕ → ℤ) := by
  suffices Function.Injective (nat_abs ∘ ((· ^ ·) x : ℕ → ℤ)) by
    exact Function.Injective.of_comp this
  convert Nat.pow_right_injective h
  ext n
  rw [Function.comp_app, nat_abs_pow]

end Int

variable (M G A)

/-- Monoid homomorphisms from `multiplicative ℕ` are defined by the image
of `multiplicative.of_add 1`. -/
def powersHom [Monoidₓ M] : M ≃ (Multiplicative ℕ →* M) where
  toFun := fun x =>
    ⟨fun n => x ^ n.toAdd, by
      convert pow_zeroₓ x
      exact to_add_one, fun m n => pow_addₓ x m n⟩
  invFun := fun f => f (Multiplicative.ofAdd 1)
  left_inv := pow_oneₓ
  right_inv := fun f =>
    MonoidHom.ext fun n => by
      simp [← f.map_pow, ← of_add_nsmul]

/-- Monoid homomorphisms from `multiplicative ℤ` are defined by the image
of `multiplicative.of_add 1`. -/
def zpowersHom [Groupₓ G] : G ≃ (Multiplicative ℤ →* G) where
  toFun := fun x => ⟨fun n => x ^ n.toAdd, zpow_zero x, fun m n => zpow_add x m n⟩
  invFun := fun f => f (Multiplicative.ofAdd 1)
  left_inv := zpow_one
  right_inv := fun f =>
    MonoidHom.ext fun n => by
      simp [← f.map_zpow, ← of_add_zsmul]

/-- Additive homomorphisms from `ℕ` are defined by the image of `1`. -/
def multiplesHom [AddMonoidₓ A] : A ≃ (ℕ →+ A) where
  toFun := fun x => ⟨fun n => n • x, zero_nsmul x, fun m n => add_nsmul _ _ _⟩
  invFun := fun f => f 1
  left_inv := one_nsmul
  right_inv := fun f => AddMonoidHom.ext_nat <| one_nsmul (f 1)

/-- Additive homomorphisms from `ℤ` are defined by the image of `1`. -/
def zmultiplesHom [AddGroupₓ A] : A ≃ (ℤ →+ A) where
  toFun := fun x => ⟨fun n => n • x, zero_zsmul x, fun m n => add_zsmul _ _ _⟩
  invFun := fun f => f 1
  left_inv := one_zsmul
  right_inv := fun f => AddMonoidHom.ext_int <| one_zsmul (f 1)

attribute [to_additive multiplesHom] powersHom

attribute [to_additive zmultiplesHom] zpowersHom

variable {M G A}

@[simp]
theorem powers_hom_apply [Monoidₓ M] (x : M) (n : Multiplicative ℕ) : powersHom M x n = x ^ n.toAdd :=
  rfl

@[simp]
theorem powers_hom_symm_apply [Monoidₓ M] (f : Multiplicative ℕ →* M) :
    (powersHom M).symm f = f (Multiplicative.ofAdd 1) :=
  rfl

@[simp]
theorem zpowers_hom_apply [Groupₓ G] (x : G) (n : Multiplicative ℤ) : zpowersHom G x n = x ^ n.toAdd :=
  rfl

@[simp]
theorem zpowers_hom_symm_apply [Groupₓ G] (f : Multiplicative ℤ →* G) :
    (zpowersHom G).symm f = f (Multiplicative.ofAdd 1) :=
  rfl

@[simp]
theorem multiples_hom_apply [AddMonoidₓ A] (x : A) (n : ℕ) : multiplesHom A x n = n • x :=
  rfl

attribute [to_additive multiples_hom_apply] powers_hom_apply

@[simp]
theorem multiples_hom_symm_apply [AddMonoidₓ A] (f : ℕ →+ A) : (multiplesHom A).symm f = f 1 :=
  rfl

attribute [to_additive multiples_hom_symm_apply] powers_hom_symm_apply

@[simp]
theorem zmultiples_hom_apply [AddGroupₓ A] (x : A) (n : ℤ) : zmultiplesHom A x n = n • x :=
  rfl

attribute [to_additive zmultiples_hom_apply] zpowers_hom_apply

@[simp]
theorem zmultiples_hom_symm_apply [AddGroupₓ A] (f : ℤ →+ A) : (zmultiplesHom A).symm f = f 1 :=
  rfl

attribute [to_additive zmultiples_hom_symm_apply] zpowers_hom_symm_apply

-- TODO use to_additive in the rest of this file
theorem MonoidHom.apply_mnat [Monoidₓ M] (f : Multiplicative ℕ →* M) (n : Multiplicative ℕ) :
    f n = f (Multiplicative.ofAdd 1) ^ n.toAdd := by
  rw [← powers_hom_symm_apply, ← powers_hom_apply, Equivₓ.apply_symm_apply]

@[ext]
theorem MonoidHom.ext_mnat [Monoidₓ M] ⦃f g : Multiplicative ℕ →* M⦄
    (h : f (Multiplicative.ofAdd 1) = g (Multiplicative.ofAdd 1)) : f = g :=
  MonoidHom.ext fun n => by
    rw [f.apply_mnat, g.apply_mnat, h]

theorem MonoidHom.apply_mint [Groupₓ M] (f : Multiplicative ℤ →* M) (n : Multiplicative ℤ) :
    f n = f (Multiplicative.ofAdd 1) ^ n.toAdd := by
  rw [← zpowers_hom_symm_apply, ← zpowers_hom_apply, Equivₓ.apply_symm_apply]

/-! `monoid_hom.ext_mint` is defined in `data.int.cast` -/


theorem AddMonoidHom.apply_nat [AddMonoidₓ M] (f : ℕ →+ M) (n : ℕ) : f n = n • f 1 := by
  rw [← multiples_hom_symm_apply, ← multiples_hom_apply, Equivₓ.apply_symm_apply]

/-! `add_monoid_hom.ext_nat` is defined in `data.nat.cast` -/


theorem AddMonoidHom.apply_int [AddGroupₓ M] (f : ℤ →+ M) (n : ℤ) : f n = n • f 1 := by
  rw [← zmultiples_hom_symm_apply, ← zmultiples_hom_apply, Equivₓ.apply_symm_apply]

/-! `add_monoid_hom.ext_int` is defined in `data.int.cast` -/


variable (M G A)

/-- If `M` is commutative, `powers_hom` is a multiplicative equivalence. -/
def powersMulHom [CommMonoidₓ M] : M ≃* (Multiplicative ℕ →* M) :=
  { powersHom M with
    map_mul' := fun a b =>
      MonoidHom.ext <| by
        simp [mul_powₓ] }

/-- If `M` is commutative, `zpowers_hom` is a multiplicative equivalence. -/
def zpowersMulHom [CommGroupₓ G] : G ≃* (Multiplicative ℤ →* G) :=
  { zpowersHom G with
    map_mul' := fun a b =>
      MonoidHom.ext <| by
        simp [mul_zpow] }

/-- If `M` is commutative, `multiples_hom` is an additive equivalence. -/
def multiplesAddHom [AddCommMonoidₓ A] : A ≃+ (ℕ →+ A) :=
  { multiplesHom A with
    map_add' := fun a b =>
      AddMonoidHom.ext <| by
        simp [nsmul_add] }

/-- If `M` is commutative, `zmultiples_hom` is an additive equivalence. -/
def zmultiplesAddHom [AddCommGroupₓ A] : A ≃+ (ℤ →+ A) :=
  { zmultiplesHom A with
    map_add' := fun a b =>
      AddMonoidHom.ext <| by
        simp [zsmul_add] }

variable {M G A}

@[simp]
theorem powers_mul_hom_apply [CommMonoidₓ M] (x : M) (n : Multiplicative ℕ) : powersMulHom M x n = x ^ n.toAdd :=
  rfl

@[simp]
theorem powers_mul_hom_symm_apply [CommMonoidₓ M] (f : Multiplicative ℕ →* M) :
    (powersMulHom M).symm f = f (Multiplicative.ofAdd 1) :=
  rfl

@[simp]
theorem zpowers_mul_hom_apply [CommGroupₓ G] (x : G) (n : Multiplicative ℤ) : zpowersMulHom G x n = x ^ n.toAdd :=
  rfl

@[simp]
theorem zpowers_mul_hom_symm_apply [CommGroupₓ G] (f : Multiplicative ℤ →* G) :
    (zpowersMulHom G).symm f = f (Multiplicative.ofAdd 1) :=
  rfl

@[simp]
theorem multiples_add_hom_apply [AddCommMonoidₓ A] (x : A) (n : ℕ) : multiplesAddHom A x n = n • x :=
  rfl

@[simp]
theorem multiples_add_hom_symm_apply [AddCommMonoidₓ A] (f : ℕ →+ A) : (multiplesAddHom A).symm f = f 1 :=
  rfl

@[simp]
theorem zmultiples_add_hom_apply [AddCommGroupₓ A] (x : A) (n : ℤ) : zmultiplesAddHom A x n = n • x :=
  rfl

@[simp]
theorem zmultiples_add_hom_symm_apply [AddCommGroupₓ A] (f : ℤ →+ A) : (zmultiplesAddHom A).symm f = f 1 :=
  rfl

/-!
### Commutativity (again)

Facts about `semiconj_by` and `commute` that require `zpow` or `zsmul`, or the fact that integer
multiplication equals semiring multiplication.
-/


namespace SemiconjBy

section

variable [Semiringₓ R] {a x y : R}

@[simp]
theorem cast_nat_mul_right (h : SemiconjBy a x y) (n : ℕ) : SemiconjBy a ((n : R) * x) (n * y) :=
  SemiconjBy.mul_right (Nat.commute_cast _ _) h

@[simp]
theorem cast_nat_mul_left (h : SemiconjBy a x y) (n : ℕ) : SemiconjBy ((n : R) * a) x y :=
  SemiconjBy.mul_left (Nat.cast_commute _ _) h

@[simp]
theorem cast_nat_mul_cast_nat_mul (h : SemiconjBy a x y) (m n : ℕ) : SemiconjBy ((m : R) * a) (n * x) (n * y) :=
  (h.cast_nat_mul_left m).cast_nat_mul_right n

end

variable [Monoidₓ M] [Groupₓ G] [Ringₓ R]

@[simp, to_additive]
theorem units_zpow_right {a : M} {x y : Mˣ} (h : SemiconjBy a x y) : ∀ m : ℤ, SemiconjBy a ↑(x ^ m) ↑(y ^ m)
  | (n : ℕ) => by
    simp only [zpow_coe_nat, Units.coe_pow, h, pow_right]
  | -[1+ n] => by
    simp only [zpow_neg_succ_of_nat, Units.coe_pow, units_inv_right, h, pow_right]

variable {a b x y x' y' : R}

@[simp]
theorem cast_int_mul_right (h : SemiconjBy a x y) (m : ℤ) : SemiconjBy a ((m : ℤ) * x) (m * y) :=
  SemiconjBy.mul_right (Int.commute_cast _ _) h

@[simp]
theorem cast_int_mul_left (h : SemiconjBy a x y) (m : ℤ) : SemiconjBy ((m : R) * a) x y :=
  SemiconjBy.mul_left (Int.cast_commute _ _) h

@[simp]
theorem cast_int_mul_cast_int_mul (h : SemiconjBy a x y) (m n : ℤ) : SemiconjBy ((m : R) * a) (n * x) (n * y) :=
  (h.cast_int_mul_left m).cast_int_mul_right n

end SemiconjBy

namespace Commute

section

variable [Semiringₓ R] {a b : R}

@[simp]
theorem cast_nat_mul_right (h : Commute a b) (n : ℕ) : Commute a ((n : R) * b) :=
  h.cast_nat_mul_right n

@[simp]
theorem cast_nat_mul_left (h : Commute a b) (n : ℕ) : Commute ((n : R) * a) b :=
  h.cast_nat_mul_left n

@[simp]
theorem cast_nat_mul_cast_nat_mul (h : Commute a b) (m n : ℕ) : Commute ((m : R) * a) (n * b) :=
  h.cast_nat_mul_cast_nat_mul m n

@[simp]
theorem self_cast_nat_mul (n : ℕ) : Commute a (n * a) :=
  (Commute.refl a).cast_nat_mul_right n

@[simp]
theorem cast_nat_mul_self (n : ℕ) : Commute ((n : R) * a) a :=
  (Commute.refl a).cast_nat_mul_left n

@[simp]
theorem self_cast_nat_mul_cast_nat_mul (m n : ℕ) : Commute ((m : R) * a) (n * a) :=
  (Commute.refl a).cast_nat_mul_cast_nat_mul m n

end

variable [Monoidₓ M] [Groupₓ G] [Ringₓ R]

@[simp, to_additive]
theorem units_zpow_right {a : M} {u : Mˣ} (h : Commute a u) (m : ℤ) : Commute a ↑(u ^ m) :=
  h.units_zpow_right m

@[simp, to_additive]
theorem units_zpow_left {u : Mˣ} {a : M} (h : Commute (↑u) a) (m : ℤ) : Commute (↑(u ^ m)) a :=
  (h.symm.units_zpow_right m).symm

variable {a b : R}

@[simp]
theorem cast_int_mul_right (h : Commute a b) (m : ℤ) : Commute a (m * b) :=
  h.cast_int_mul_right m

@[simp]
theorem cast_int_mul_left (h : Commute a b) (m : ℤ) : Commute ((m : R) * a) b :=
  h.cast_int_mul_left m

theorem cast_int_mul_cast_int_mul (h : Commute a b) (m n : ℤ) : Commute ((m : R) * a) (n * b) :=
  h.cast_int_mul_cast_int_mul m n

variable (a) (m n : ℤ)

@[simp]
theorem cast_int_left : Commute (m : R) a := by
  rw [← mul_oneₓ (m : R)]
  exact (one_left a).cast_int_mul_left m

@[simp]
theorem cast_int_right : Commute a m := by
  rw [← mul_oneₓ (m : R)]
  exact (one_right a).cast_int_mul_right m

@[simp]
theorem self_cast_int_mul : Commute a (n * a) :=
  (Commute.refl a).cast_int_mul_right n

@[simp]
theorem cast_int_mul_self : Commute ((n : R) * a) a :=
  (Commute.refl a).cast_int_mul_left n

theorem self_cast_int_mul_cast_int_mul : Commute ((m : R) * a) (n * a) :=
  (Commute.refl a).cast_int_mul_cast_int_mul m n

end Commute

section Multiplicative

open Multiplicative

@[simp]
theorem Nat.to_add_pow (a : Multiplicative ℕ) (b : ℕ) : toAdd (a ^ b) = toAdd a * b := by
  induction' b with b ih
  · erw [pow_zeroₓ, to_add_one, mul_zero]
    
  · simp [*, pow_succₓ, add_commₓ, Nat.mul_succ]
    

@[simp]
theorem Nat.of_add_mul (a b : ℕ) : ofAdd (a * b) = ofAdd a ^ b :=
  (Nat.to_add_pow _ _).symm

@[simp]
theorem Int.to_add_pow (a : Multiplicative ℤ) (b : ℕ) : toAdd (a ^ b) = toAdd a * b := by
  induction b <;> simp [*, mul_addₓ, pow_succₓ, add_commₓ]

@[simp]
theorem Int.to_add_zpow (a : Multiplicative ℤ) (b : ℤ) : toAdd (a ^ b) = toAdd a * b :=
  Int.induction_on b
    (by
      simp )
    (by
      simp (config := { contextual := true })[zpow_add, mul_addₓ])
    (by
      simp (config := { contextual := true })[zpow_add, mul_addₓ, sub_eq_add_neg, -Int.add_neg_one])

@[simp]
theorem Int.of_add_mul (a b : ℤ) : ofAdd (a * b) = ofAdd a ^ b :=
  (Int.to_add_zpow _ _).symm

end Multiplicative

namespace Units

variable [Monoidₓ M]

theorem conj_pow (u : Mˣ) (x : M) (n : ℕ) : (↑u * x * ↑u⁻¹) ^ n = u * x ^ n * ↑u⁻¹ :=
  (divp_eq_iff_mul_eq.2 ((u.mk_semiconj_by x).pow_right n).Eq.symm).symm

theorem conj_pow' (u : Mˣ) (x : M) (n : ℕ) : (↑u⁻¹ * x * u) ^ n = ↑u⁻¹ * x ^ n * u :=
  u⁻¹.conj_pow x n

end Units

namespace MulOpposite

/-- Moving to the opposite monoid commutes with taking powers. -/
@[simp]
theorem op_pow [Monoidₓ M] (x : M) (n : ℕ) : op (x ^ n) = op x ^ n :=
  rfl

@[simp]
theorem unop_pow [Monoidₓ M] (x : Mᵐᵒᵖ) (n : ℕ) : unop (x ^ n) = unop x ^ n :=
  rfl

/-- Moving to the opposite group or group_with_zero commutes with taking powers. -/
@[simp]
theorem op_zpow [DivInvMonoidₓ M] (x : M) (z : ℤ) : op (x ^ z) = op x ^ z :=
  rfl

@[simp]
theorem unop_zpow [DivInvMonoidₓ M] (x : Mᵐᵒᵖ) (z : ℤ) : unop (x ^ z) = unop x ^ z :=
  rfl

end MulOpposite

