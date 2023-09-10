/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathbin.Data.Rat.Order
import Mathbin.Data.Rat.Lemmas
import Mathbin.Data.Int.CharZero
import Mathbin.Algebra.GroupWithZero.Power
import Mathbin.Algebra.Field.Opposite
import Mathbin.Algebra.Order.Field.Basic

#align_import data.rat.cast from "leanprover-community/mathlib"@"acebd8d49928f6ed8920e502a6c90674e75bd441"

/-!
# Casts for Rational Numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Summary

We define the canonical injection from ℚ into an arbitrary division ring and prove various
casting lemmas showing the well-behavedness of this injection.

## Notations

- `/.` is infix notation for `rat.mk`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, cast, coercion, casting
-/


variable {F ι α β : Type _}

namespace Rat

open scoped Rat

section WithDivRing

variable [DivisionRing α]

#print Rat.cast_coe_int /-
@[simp, norm_cast]
theorem cast_coe_int (n : ℤ) : ((n : ℚ) : α) = n :=
  (cast_def _).trans <| show (n / (1 : ℕ) : α) = n by rw [Nat.cast_one, div_one]
#align rat.cast_coe_int Rat.cast_coe_int
-/

#print Rat.cast_coe_nat /-
@[simp, norm_cast]
theorem cast_coe_nat (n : ℕ) : ((n : ℚ) : α) = n := by
  rw [← Int.cast_ofNat, cast_coe_int, Int.cast_ofNat]
#align rat.cast_coe_nat Rat.cast_coe_nat
-/

#print Rat.cast_zero /-
@[simp, norm_cast]
theorem cast_zero : ((0 : ℚ) : α) = 0 :=
  (cast_coe_int _).trans Int.cast_zero
#align rat.cast_zero Rat.cast_zero
-/

#print Rat.cast_one /-
@[simp, norm_cast]
theorem cast_one : ((1 : ℚ) : α) = 1 :=
  (cast_coe_int _).trans Int.cast_one
#align rat.cast_one Rat.cast_one
-/

#print Rat.cast_commute /-
theorem cast_commute (r : ℚ) (a : α) : Commute (↑r) a := by
  simpa only [cast_def] using (r.1.cast_commute a).divLeft (r.2.cast_commute a)
#align rat.cast_commute Rat.cast_commute
-/

#print Rat.cast_comm /-
theorem cast_comm (r : ℚ) (a : α) : (r : α) * a = a * r :=
  (cast_commute r a).Eq
#align rat.cast_comm Rat.cast_comm
-/

#print Rat.commute_cast /-
theorem commute_cast (a : α) (r : ℚ) : Commute a r :=
  (r.cast_commute a).symm
#align rat.commute_cast Rat.commute_cast
-/

#print Rat.cast_mk_of_ne_zero /-
@[norm_cast]
theorem cast_mk_of_ne_zero (a b : ℤ) (b0 : (b : α) ≠ 0) : (a /. b : α) = a / b :=
  by
  have b0' : b ≠ 0 := by refine' mt _ b0; simp (config := { contextual := true })
  cases' e : a /. b with n d h c
  have d0 : (d : α) ≠ 0 := by
    intro d0
    have dd := denom_dvd a b
    cases' show (d : ℤ) ∣ b by rwa [e] at dd  with k ke
    have : (b : α) = (d : α) * (k : α) := by rw [ke, Int.cast_mul, Int.cast_ofNat]
    rw [d0, MulZeroClass.zero_mul] at this ; contradiction
  rw [num_denom'] at e 
  have := congr_arg (coe : ℤ → α) ((mk_eq b0' <| ne_of_gt <| Int.coe_nat_pos.2 h).1 e)
  rw [Int.cast_mul, Int.cast_mul, Int.cast_ofNat] at this 
  symm
  rw [cast_def, div_eq_mul_inv, eq_div_iff_mul_eq d0, mul_assoc, (d.commute_cast _).Eq, ← mul_assoc,
    this, mul_assoc, mul_inv_cancel b0, mul_one]
#align rat.cast_mk_of_ne_zero Rat.cast_mk_of_ne_zero
-/

#print Rat.cast_add_of_ne_zero /-
@[norm_cast]
theorem cast_add_of_ne_zero :
    ∀ {m n : ℚ}, (m.den : α) ≠ 0 → (n.den : α) ≠ 0 → ((m + n : ℚ) : α) = m + n
  | ⟨n₁, d₁, h₁, c₁⟩, ⟨n₂, d₂, h₂, c₂⟩ => fun (d₁0 : (d₁ : α) ≠ 0) (d₂0 : (d₂ : α) ≠ 0) =>
    by
    have d₁0' : (d₁ : ℤ) ≠ 0 :=
      Int.coe_nat_ne_zero.2 fun e => by rw [e] at d₁0  <;> exact d₁0 Nat.cast_zero
    have d₂0' : (d₂ : ℤ) ≠ 0 :=
      Int.coe_nat_ne_zero.2 fun e => by rw [e] at d₂0  <;> exact d₂0 Nat.cast_zero
    rw [num_denom', num_denom', add_def d₁0' d₂0']
    suffices (n₁ * (d₂ * (d₂⁻¹ * d₁⁻¹)) + n₂ * (d₁ * d₂⁻¹) * d₁⁻¹ : α) = n₁ * d₁⁻¹ + n₂ * d₂⁻¹
      by
      rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero, cast_mk_of_ne_zero]
      · simpa [division_def, left_distrib, right_distrib, mul_inv_rev, d₁0, d₂0, mul_assoc]
      all_goals simp [d₁0, d₂0]
    rw [← mul_assoc (d₂ : α), mul_inv_cancel d₂0, one_mul, (Nat.cast_commute _ _).Eq]
    simp [d₁0, mul_assoc]
#align rat.cast_add_of_ne_zero Rat.cast_add_of_ne_zero
-/

#print Rat.cast_neg /-
@[simp, norm_cast]
theorem cast_neg : ∀ n, ((-n : ℚ) : α) = -n
  | ⟨n, d, h, c⟩ => by
    simpa only [cast_def] using
      show (↑(-n) / d : α) = -(n / d) by
        rw [div_eq_mul_inv, div_eq_mul_inv, Int.cast_neg, neg_mul_eq_neg_mul]
#align rat.cast_neg Rat.cast_neg
-/

#print Rat.cast_sub_of_ne_zero /-
@[norm_cast]
theorem cast_sub_of_ne_zero {m n : ℚ} (m0 : (m.den : α) ≠ 0) (n0 : (n.den : α) ≠ 0) :
    ((m - n : ℚ) : α) = m - n :=
  by
  have : ((-n).den : α) ≠ 0 := by cases n <;> exact n0
  simp [sub_eq_add_neg, cast_add_of_ne_zero m0 this]
#align rat.cast_sub_of_ne_zero Rat.cast_sub_of_ne_zero
-/

#print Rat.cast_mul_of_ne_zero /-
@[norm_cast]
theorem cast_mul_of_ne_zero :
    ∀ {m n : ℚ}, (m.den : α) ≠ 0 → (n.den : α) ≠ 0 → ((m * n : ℚ) : α) = m * n
  | ⟨n₁, d₁, h₁, c₁⟩, ⟨n₂, d₂, h₂, c₂⟩ => fun (d₁0 : (d₁ : α) ≠ 0) (d₂0 : (d₂ : α) ≠ 0) =>
    by
    have d₁0' : (d₁ : ℤ) ≠ 0 :=
      Int.coe_nat_ne_zero.2 fun e => by rw [e] at d₁0  <;> exact d₁0 Nat.cast_zero
    have d₂0' : (d₂ : ℤ) ≠ 0 :=
      Int.coe_nat_ne_zero.2 fun e => by rw [e] at d₂0  <;> exact d₂0 Nat.cast_zero
    rw [num_denom', num_denom', mul_def d₁0' d₂0']
    suffices (n₁ * (n₂ * d₂⁻¹ * d₁⁻¹) : α) = n₁ * (d₁⁻¹ * (n₂ * d₂⁻¹))
      by
      rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero, cast_mk_of_ne_zero]
      · simpa [division_def, mul_inv_rev, d₁0, d₂0, mul_assoc]
      all_goals simp [d₁0, d₂0]
    rw [(d₁.commute_cast (_ : α)).inv_right₀.Eq]
#align rat.cast_mul_of_ne_zero Rat.cast_mul_of_ne_zero
-/

#print Rat.cast_inv_nat /-
@[simp]
theorem cast_inv_nat (n : ℕ) : ((n⁻¹ : ℚ) : α) = n⁻¹ :=
  by
  cases n; · simp
  simp_rw [coe_nat_eq_mk, inv_def, mk, mk_nat, dif_neg n.succ_ne_zero, mk_pnat]
  simp [cast_def]
#align rat.cast_inv_nat Rat.cast_inv_nat
-/

#print Rat.cast_inv_int /-
@[simp]
theorem cast_inv_int (n : ℤ) : ((n⁻¹ : ℚ) : α) = n⁻¹ :=
  by
  cases n
  · simp [cast_inv_nat]
  · simp only [Int.cast_negSucc, ← Nat.cast_succ, cast_neg, inv_neg, cast_inv_nat]
#align rat.cast_inv_int Rat.cast_inv_int
-/

#print Rat.cast_inv_of_ne_zero /-
@[norm_cast]
theorem cast_inv_of_ne_zero : ∀ {n : ℚ}, (n.num : α) ≠ 0 → (n.den : α) ≠ 0 → ((n⁻¹ : ℚ) : α) = n⁻¹
  | ⟨n, d, h, c⟩ => fun (n0 : (n : α) ≠ 0) (d0 : (d : α) ≠ 0) =>
    by
    have n0' : (n : ℤ) ≠ 0 := fun e => by rw [e] at n0  <;> exact n0 Int.cast_zero
    have d0' : (d : ℤ) ≠ 0 :=
      Int.coe_nat_ne_zero.2 fun e => by rw [e] at d0  <;> exact d0 Nat.cast_zero
    rw [num_denom', inv_def]
    rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero, inv_div] <;> simp [n0, d0]
#align rat.cast_inv_of_ne_zero Rat.cast_inv_of_ne_zero
-/

#print Rat.cast_div_of_ne_zero /-
@[norm_cast]
theorem cast_div_of_ne_zero {m n : ℚ} (md : (m.den : α) ≠ 0) (nn : (n.num : α) ≠ 0)
    (nd : (n.den : α) ≠ 0) : ((m / n : ℚ) : α) = m / n :=
  by
  have : (n⁻¹.den : ℤ) ∣ n.num := by
    conv in n⁻¹.den => rw [← @num_denom n, inv_def] <;> apply denom_dvd
  have : (n⁻¹.den : α) = 0 → (n.num : α) = 0 := fun h =>
    by
    let ⟨k, e⟩ := this
    have := congr_arg (coe : ℤ → α) e <;>
      rwa [Int.cast_mul, Int.cast_ofNat, h, MulZeroClass.zero_mul] at this 
  rw [division_def, cast_mul_of_ne_zero md (mt this nn), cast_inv_of_ne_zero nn nd, division_def]
#align rat.cast_div_of_ne_zero Rat.cast_div_of_ne_zero
-/

#print Rat.cast_inj /-
@[simp, norm_cast]
theorem cast_inj [CharZero α] : ∀ {m n : ℚ}, (m : α) = n ↔ m = n
  | ⟨n₁, d₁, h₁, c₁⟩, ⟨n₂, d₂, h₂, c₂⟩ =>
    by
    refine' ⟨fun h => _, congr_arg _⟩
    have d₁0 : d₁ ≠ 0 := ne_of_gt h₁
    have d₂0 : d₂ ≠ 0 := ne_of_gt h₂
    have d₁a : (d₁ : α) ≠ 0 := Nat.cast_ne_zero.2 d₁0
    have d₂a : (d₂ : α) ≠ 0 := Nat.cast_ne_zero.2 d₂0
    rw [num_denom', num_denom'] at h ⊢
    rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero] at h  <;> simp [d₁0, d₂0] at h ⊢
    rwa [eq_div_iff_mul_eq d₂a, division_def, mul_assoc, (d₁.cast_commute (d₂ : α)).inv_left₀.Eq, ←
      mul_assoc, ← division_def, eq_comm, eq_div_iff_mul_eq d₁a, eq_comm, ← Int.cast_ofNat d₁, ←
      Int.cast_mul, ← Int.cast_ofNat d₂, ← Int.cast_mul, Int.cast_inj, ←
      mk_eq (Int.coe_nat_ne_zero.2 d₁0) (Int.coe_nat_ne_zero.2 d₂0)] at h 
#align rat.cast_inj Rat.cast_inj
-/

#print Rat.cast_injective /-
theorem cast_injective [CharZero α] : Function.Injective (coe : ℚ → α)
  | m, n => cast_inj.1
#align rat.cast_injective Rat.cast_injective
-/

#print Rat.cast_eq_zero /-
@[simp]
theorem cast_eq_zero [CharZero α] {n : ℚ} : (n : α) = 0 ↔ n = 0 := by rw [← cast_zero, cast_inj]
#align rat.cast_eq_zero Rat.cast_eq_zero
-/

#print Rat.cast_ne_zero /-
theorem cast_ne_zero [CharZero α] {n : ℚ} : (n : α) ≠ 0 ↔ n ≠ 0 :=
  not_congr cast_eq_zero
#align rat.cast_ne_zero Rat.cast_ne_zero
-/

#print Rat.cast_add /-
@[simp, norm_cast]
theorem cast_add [CharZero α] (m n) : ((m + n : ℚ) : α) = m + n :=
  cast_add_of_ne_zero (Nat.cast_ne_zero.2 <| ne_of_gt m.Pos) (Nat.cast_ne_zero.2 <| ne_of_gt n.Pos)
#align rat.cast_add Rat.cast_add
-/

#print Rat.cast_sub /-
@[simp, norm_cast]
theorem cast_sub [CharZero α] (m n) : ((m - n : ℚ) : α) = m - n :=
  cast_sub_of_ne_zero (Nat.cast_ne_zero.2 <| ne_of_gt m.Pos) (Nat.cast_ne_zero.2 <| ne_of_gt n.Pos)
#align rat.cast_sub Rat.cast_sub
-/

#print Rat.cast_mul /-
@[simp, norm_cast]
theorem cast_mul [CharZero α] (m n) : ((m * n : ℚ) : α) = m * n :=
  cast_mul_of_ne_zero (Nat.cast_ne_zero.2 <| ne_of_gt m.Pos) (Nat.cast_ne_zero.2 <| ne_of_gt n.Pos)
#align rat.cast_mul Rat.cast_mul
-/

#print Rat.cast_bit0 /-
@[simp, norm_cast]
theorem cast_bit0 [CharZero α] (n : ℚ) : ((bit0 n : ℚ) : α) = bit0 n :=
  cast_add _ _
#align rat.cast_bit0 Rat.cast_bit0
-/

#print Rat.cast_bit1 /-
@[simp, norm_cast]
theorem cast_bit1 [CharZero α] (n : ℚ) : ((bit1 n : ℚ) : α) = bit1 n := by
  rw [bit1, cast_add, cast_one, cast_bit0] <;> rfl
#align rat.cast_bit1 Rat.cast_bit1
-/

variable (α) [CharZero α]

#print Rat.castHom /-
/-- Coercion `ℚ → α` as a `ring_hom`. -/
def castHom : ℚ →+* α :=
  ⟨coe, cast_one, cast_mul, cast_zero, cast_add⟩
#align rat.cast_hom Rat.castHom
-/

variable {α}

#print Rat.coe_cast_hom /-
@[simp]
theorem coe_cast_hom : ⇑(castHom α) = coe :=
  rfl
#align rat.coe_cast_hom Rat.coe_cast_hom
-/

#print Rat.cast_inv /-
@[simp, norm_cast]
theorem cast_inv (n) : ((n⁻¹ : ℚ) : α) = n⁻¹ :=
  map_inv₀ (castHom α) _
#align rat.cast_inv Rat.cast_inv
-/

#print Rat.cast_div /-
@[simp, norm_cast]
theorem cast_div (m n) : ((m / n : ℚ) : α) = m / n :=
  map_div₀ (castHom α) _ _
#align rat.cast_div Rat.cast_div
-/

#print Rat.cast_zpow /-
@[simp, norm_cast]
theorem cast_zpow (q : ℚ) (n : ℤ) : ((q ^ n : ℚ) : α) = q ^ n :=
  map_zpow₀ (castHom α) q n
#align rat.cast_zpow Rat.cast_zpow
-/

#print Rat.cast_mk /-
@[norm_cast]
theorem cast_mk (a b : ℤ) : (a /. b : α) = a / b := by simp only [mk_eq_div, cast_div, cast_coe_int]
#align rat.cast_mk Rat.cast_mk
-/

#print Rat.cast_pow /-
@[simp, norm_cast]
theorem cast_pow (q) (k : ℕ) : ((q ^ k : ℚ) : α) = q ^ k :=
  (castHom α).map_pow q k
#align rat.cast_pow Rat.cast_pow
-/

end WithDivRing

section LinearOrderedField

variable {K : Type _} [LinearOrderedField K]

#print Rat.cast_pos_of_pos /-
theorem cast_pos_of_pos {r : ℚ} (hr : 0 < r) : (0 : K) < r :=
  by
  rw [Rat.cast_def]
  exact div_pos (Int.cast_pos.2 <| num_pos_iff_pos.2 hr) (Nat.cast_pos.2 r.pos)
#align rat.cast_pos_of_pos Rat.cast_pos_of_pos
-/

#print Rat.cast_strictMono /-
@[mono]
theorem cast_strictMono : StrictMono (coe : ℚ → K) := fun m n => by
  simpa only [sub_pos, cast_sub] using @cast_pos_of_pos K _ (n - m)
#align rat.cast_strict_mono Rat.cast_strictMono
-/

#print Rat.cast_mono /-
@[mono]
theorem cast_mono : Monotone (coe : ℚ → K) :=
  cast_strictMono.Monotone
#align rat.cast_mono Rat.cast_mono
-/

#print Rat.castOrderEmbedding /-
/-- Coercion from `ℚ` as an order embedding. -/
@[simps]
def castOrderEmbedding : ℚ ↪o K :=
  OrderEmbedding.ofStrictMono coe cast_strictMono
#align rat.cast_order_embedding Rat.castOrderEmbedding
-/

#print Rat.cast_le /-
@[simp, norm_cast]
theorem cast_le {m n : ℚ} : (m : K) ≤ n ↔ m ≤ n :=
  castOrderEmbedding.le_iff_le
#align rat.cast_le Rat.cast_le
-/

#print Rat.cast_lt /-
@[simp, norm_cast]
theorem cast_lt {m n : ℚ} : (m : K) < n ↔ m < n :=
  cast_strictMono.lt_iff_lt
#align rat.cast_lt Rat.cast_lt
-/

#print Rat.cast_nonneg /-
@[simp]
theorem cast_nonneg {n : ℚ} : 0 ≤ (n : K) ↔ 0 ≤ n := by norm_cast
#align rat.cast_nonneg Rat.cast_nonneg
-/

#print Rat.cast_nonpos /-
@[simp]
theorem cast_nonpos {n : ℚ} : (n : K) ≤ 0 ↔ n ≤ 0 := by norm_cast
#align rat.cast_nonpos Rat.cast_nonpos
-/

#print Rat.cast_pos /-
@[simp]
theorem cast_pos {n : ℚ} : (0 : K) < n ↔ 0 < n := by norm_cast
#align rat.cast_pos Rat.cast_pos
-/

#print Rat.cast_lt_zero /-
@[simp]
theorem cast_lt_zero {n : ℚ} : (n : K) < 0 ↔ n < 0 := by norm_cast
#align rat.cast_lt_zero Rat.cast_lt_zero
-/

#print Rat.cast_min /-
@[simp, norm_cast]
theorem cast_min {a b : ℚ} : (↑(min a b) : K) = min a b :=
  (@cast_mono K _).map_min
#align rat.cast_min Rat.cast_min
-/

#print Rat.cast_max /-
@[simp, norm_cast]
theorem cast_max {a b : ℚ} : (↑(max a b) : K) = max a b :=
  (@cast_mono K _).map_max
#align rat.cast_max Rat.cast_max
-/

#print Rat.cast_abs /-
@[simp, norm_cast]
theorem cast_abs {q : ℚ} : ((|q| : ℚ) : K) = |q| := by simp [abs_eq_max_neg]
#align rat.cast_abs Rat.cast_abs
-/

open Set

#print Rat.preimage_cast_Icc /-
@[simp]
theorem preimage_cast_Icc (a b : ℚ) : coe ⁻¹' Icc (a : K) b = Icc a b := by ext x; simp
#align rat.preimage_cast_Icc Rat.preimage_cast_Icc
-/

#print Rat.preimage_cast_Ico /-
@[simp]
theorem preimage_cast_Ico (a b : ℚ) : coe ⁻¹' Ico (a : K) b = Ico a b := by ext x; simp
#align rat.preimage_cast_Ico Rat.preimage_cast_Ico
-/

#print Rat.preimage_cast_Ioc /-
@[simp]
theorem preimage_cast_Ioc (a b : ℚ) : coe ⁻¹' Ioc (a : K) b = Ioc a b := by ext x; simp
#align rat.preimage_cast_Ioc Rat.preimage_cast_Ioc
-/

#print Rat.preimage_cast_Ioo /-
@[simp]
theorem preimage_cast_Ioo (a b : ℚ) : coe ⁻¹' Ioo (a : K) b = Ioo a b := by ext x; simp
#align rat.preimage_cast_Ioo Rat.preimage_cast_Ioo
-/

#print Rat.preimage_cast_Ici /-
@[simp]
theorem preimage_cast_Ici (a : ℚ) : coe ⁻¹' Ici (a : K) = Ici a := by ext x; simp
#align rat.preimage_cast_Ici Rat.preimage_cast_Ici
-/

#print Rat.preimage_cast_Iic /-
@[simp]
theorem preimage_cast_Iic (a : ℚ) : coe ⁻¹' Iic (a : K) = Iic a := by ext x; simp
#align rat.preimage_cast_Iic Rat.preimage_cast_Iic
-/

#print Rat.preimage_cast_Ioi /-
@[simp]
theorem preimage_cast_Ioi (a : ℚ) : coe ⁻¹' Ioi (a : K) = Ioi a := by ext x; simp
#align rat.preimage_cast_Ioi Rat.preimage_cast_Ioi
-/

#print Rat.preimage_cast_Iio /-
@[simp]
theorem preimage_cast_Iio (a : ℚ) : coe ⁻¹' Iio (a : K) = Iio a := by ext x; simp
#align rat.preimage_cast_Iio Rat.preimage_cast_Iio
-/

end LinearOrderedField

#print Rat.cast_id /-
@[norm_cast]
theorem cast_id (n : ℚ) : (↑n : ℚ) = n := by rw [cast_def, num_div_denom]
#align rat.cast_id Rat.cast_id
-/

#print Rat.cast_eq_id /-
@[simp]
theorem cast_eq_id : (coe : ℚ → ℚ) = id :=
  funext cast_id
#align rat.cast_eq_id Rat.cast_eq_id
-/

#print Rat.castHom_rat /-
@[simp]
theorem castHom_rat : castHom ℚ = RingHom.id ℚ :=
  RingHom.ext cast_id
#align rat.cast_hom_rat Rat.castHom_rat
-/

end Rat

open Rat

#print map_ratCast /-
@[simp]
theorem map_ratCast [DivisionRing α] [DivisionRing β] [RingHomClass F α β] (f : F) (q : ℚ) :
    f q = q := by rw [cast_def, map_div₀, map_intCast, map_natCast, cast_def]
#align map_rat_cast map_ratCast
-/

#print eq_ratCast /-
@[simp]
theorem eq_ratCast {k} [DivisionRing k] [RingHomClass F ℚ k] (f : F) (r : ℚ) : f r = r := by
  rw [← map_ratCast f, Rat.cast_id]
#align eq_rat_cast eq_ratCast
-/

namespace MonoidWithZeroHom

variable {M₀ : Type _} [MonoidWithZero M₀] [MonoidWithZeroHomClass F ℚ M₀] {f g : F}

#print MonoidWithZeroHom.ext_rat' /-
/-- If `f` and `g` agree on the integers then they are equal `φ`. -/
theorem ext_rat' (h : ∀ m : ℤ, f m = g m) : f = g :=
  FunLike.ext f g fun r => by
    rw [← r.num_div_denom, div_eq_mul_inv, map_mul, map_mul, h, ← Int.cast_ofNat,
      eq_on_inv₀ f g (h _)]
#align monoid_with_zero_hom.ext_rat' MonoidWithZeroHom.ext_rat'
-/

#print MonoidWithZeroHom.ext_rat /-
/-- If `f` and `g` agree on the integers then they are equal `φ`.

See note [partially-applied ext lemmas] for why `comp` is used here. -/
@[ext]
theorem ext_rat {f g : ℚ →*₀ M₀}
    (h : f.comp (Int.castRingHom ℚ : ℤ →*₀ ℚ) = g.comp (Int.castRingHom ℚ)) : f = g :=
  ext_rat' <| congr_fun h
#align monoid_with_zero_hom.ext_rat MonoidWithZeroHom.ext_rat
-/

#print MonoidWithZeroHom.ext_rat_on_pnat /-
/-- Positive integer values of a morphism `φ` and its value on `-1` completely determine `φ`. -/
theorem ext_rat_on_pnat (same_on_neg_one : f (-1) = g (-1))
    (same_on_pnat : ∀ n : ℕ, 0 < n → f n = g n) : f = g :=
  ext_rat' <|
    FunLike.congr_fun <|
      show
        (f : ℚ →*₀ M₀).comp (Int.castRingHom ℚ : ℤ →*₀ ℚ) =
          (g : ℚ →*₀ M₀).comp (Int.castRingHom ℚ : ℤ →*₀ ℚ)
        from ext_int' (by simpa) (by simpa)
#align monoid_with_zero_hom.ext_rat_on_pnat MonoidWithZeroHom.ext_rat_on_pnat
-/

end MonoidWithZeroHom

#print RingHom.ext_rat /-
/-- Any two ring homomorphisms from `ℚ` to a semiring are equal. If the codomain is a division ring,
then this lemma follows from `eq_rat_cast`. -/
theorem RingHom.ext_rat {R : Type _} [Semiring R] [RingHomClass F ℚ R] (f g : F) : f = g :=
  MonoidWithZeroHom.ext_rat' <|
    RingHom.congr_fun <|
      ((f : ℚ →+* R).comp (Int.castRingHom ℚ)).ext_int ((g : ℚ →+* R).comp (Int.castRingHom ℚ))
#align ring_hom.ext_rat RingHom.ext_rat
-/

#print Rat.subsingleton_ringHom /-
instance Rat.subsingleton_ringHom {R : Type _} [Semiring R] : Subsingleton (ℚ →+* R) :=
  ⟨RingHom.ext_rat⟩
#align rat.subsingleton_ring_hom Rat.subsingleton_ringHom
-/

section Smul

namespace Rat

variable {K : Type _} [DivisionRing K]

#print Rat.distribSMul /-
instance (priority := 100) distribSMul : DistribSMul ℚ K
    where
  smul := (· • ·)
  smul_zero a := by rw [smul_def, MulZeroClass.mul_zero]
  smul_add a x y := by simp only [smul_def, mul_add, cast_add]
#align rat.distrib_smul Rat.distribSMul
-/

#print Rat.isScalarTower_right /-
instance isScalarTower_right : IsScalarTower ℚ K K :=
  ⟨fun a x y => by simp only [smul_def, smul_eq_mul, mul_assoc]⟩
#align rat.is_scalar_tower_right Rat.isScalarTower_right
-/

end Rat

end Smul

