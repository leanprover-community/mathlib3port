/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Algebra.Order.Field.Defs
import Data.Rat.Field
import Data.Int.Cast.Lemmas
import Tactic.AssertExists

#align_import data.rat.order from "leanprover-community/mathlib"@"c3291da49cfa65f0d43b094750541c0731edc932"

/-!
# Order for Rational Numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Summary

We define the order on `ℚ`, prove that `ℚ` is a discrete, linearly ordered field, and define
functions such as `abs` and `sqrt` that depend on this order.

## Notations

- `/.` is infix notation for `rat.mk`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, order, ordering, sqrt, abs
-/


namespace Rat

variable (a b c : ℚ)

open scoped Rat

/-- A rational number is called nonnegative if its numerator is nonnegative. -/
protected def Nonneg (r : ℚ) : Prop :=
  0 ≤ r.num
#align rat.nonneg Rat.Nonneg

#print Rat.divInt_nonneg_iff_of_pos_right /-
@[simp]
theorem divInt_nonneg_iff_of_pos_right (a : ℤ) {b : ℤ} (h : 0 < b) : (a /. b).NonNeg ↔ 0 ≤ a :=
  by
  generalize ha : a /. b = x; cases' x with n₁ d₁ h₁ c₁; rw [num_denom'] at ha
  simp [Rat.Nonneg]
  have d0 := Int.ofNat_lt.2 h₁
  have := (mk_eq (ne_of_gt h) (ne_of_gt d0)).1 ha
  constructor <;> intro h₂
  · apply nonneg_of_mul_nonneg_left _ d0
    rw [this]; exact mul_nonneg h₂ (le_of_lt h)
  · apply nonneg_of_mul_nonneg_left _ h
    rw [← this]; exact mul_nonneg h₂ (Int.ofNat_zero_le _)
#align rat.mk_nonneg Rat.divInt_nonneg_iff_of_pos_right
-/

#print Rat.add_nonneg /-
protected theorem add_nonneg {a b} : Rat.Nonneg a → Rat.Nonneg b → Rat.Nonneg (a + b) :=
  numDenCasesOn' a fun n₁ d₁ h₁ =>
    numDenCasesOn' b fun n₂ d₂ h₂ =>
      by
      have d₁0 : 0 < (d₁ : ℤ) := Int.natCast_pos.2 (Nat.pos_of_ne_zero h₁)
      have d₂0 : 0 < (d₂ : ℤ) := Int.natCast_pos.2 (Nat.pos_of_ne_zero h₂)
      simp [d₁0, d₂0, h₁, h₂, mul_pos d₁0 d₂0]
      intro n₁0 n₂0
      apply add_nonneg <;> apply mul_nonneg <;>
        ·
          first
          | assumption
          | apply Int.ofNat_zero_le
#align rat.nonneg_add Rat.add_nonneg
-/

#print Rat.mul_nonneg /-
protected theorem mul_nonneg {a b} : Rat.Nonneg a → Rat.Nonneg b → Rat.Nonneg (a * b) :=
  numDenCasesOn' a fun n₁ d₁ h₁ =>
    numDenCasesOn' b fun n₂ d₂ h₂ =>
      by
      have d₁0 : 0 < (d₁ : ℤ) := Int.natCast_pos.2 (Nat.pos_of_ne_zero h₁)
      have d₂0 : 0 < (d₂ : ℤ) := Int.natCast_pos.2 (Nat.pos_of_ne_zero h₂)
      simp (config := { contextual := true }) [d₁0, d₂0, h₁, h₂, mul_pos d₁0 d₂0, mul_nonneg]
#align rat.nonneg_mul Rat.mul_nonneg
-/

#print Rat.nonneg_antisymm /-
protected theorem nonneg_antisymm {a} : Rat.Nonneg a → Rat.Nonneg (-a) → a = 0 :=
  numDenCasesOn' a fun n d h =>
    by
    have d0 : 0 < (d : ℤ) := Int.natCast_pos.2 (Nat.pos_of_ne_zero h)
    simp [d0, h]
    exact fun h₁ h₂ => le_antisymm h₂ h₁
#align rat.nonneg_antisymm Rat.nonneg_antisymm
-/

#print Rat.nonneg_total /-
protected theorem nonneg_total : Rat.Nonneg a ∨ Rat.Nonneg (-a) := by
  cases' a with n <;> exact Or.imp_right neg_nonneg_of_nonpos (le_total 0 n)
#align rat.nonneg_total Rat.nonneg_total
-/

#print Rat.instDecidableLeRatInstLERat /-
instance instDecidableLeRatInstLERat : Decidable (Rat.Nonneg a) := by
  cases a <;> unfold Rat.Nonneg <;> infer_instance
#align rat.decidable_nonneg Rat.instDecidableLeRatInstLERat
-/

/-- Relation `a ≤ b` on `ℚ` defined as `a ≤ b ↔ rat.nonneg (b - a)`. Use `a ≤ b` instead of
`rat.le a b`. -/
protected def Le (a b : ℚ) :=
  Rat.Nonneg (b - a)
#align rat.le Rat.Le

instance : LE ℚ :=
  ⟨Rat.Le⟩

instance decidableLe : DecidableRel ((· ≤ ·) : ℚ → ℚ → Prop)
  | a, b => show Decidable (Rat.Nonneg (b - a)) by infer_instance
#align rat.decidable_le Rat.decidableLe

#print Rat.divInt_le_divInt /-
protected theorem divInt_le_divInt {a b c d : ℤ} (b0 : 0 < b) (d0 : 0 < d) :
    a /. b ≤ c /. d ↔ a * d ≤ c * b := by
  show Rat.Nonneg _ ↔ _
  rw [← sub_nonneg]
  simp [sub_eq_add_neg, ne_of_gt b0, ne_of_gt d0, mul_pos d0 b0]
#align rat.le_def Rat.divInt_le_divInt
-/

/- warning: rat.le_refl clashes with le_refl -> le_refl
Case conversion may be inaccurate. Consider using '#align rat.le_refl le_reflₓ'. -/
#print le_refl /-
protected theorem le_refl : a ≤ a :=
  show Rat.Nonneg (a - a) by rw [sub_self] <;> exact le_refl (0 : ℤ)
#align rat.le_refl le_refl
-/

#print Rat.le_total /-
protected theorem le_total : a ≤ b ∨ b ≤ a := by
  have := Rat.nonneg_total (b - a) <;> rwa [neg_sub] at this
#align rat.le_total Rat.le_total
-/

/- warning: rat.le_antisymm clashes with le_antisymm -> le_antisymm
Case conversion may be inaccurate. Consider using '#align rat.le_antisymm le_antisymmₓ'. -/
#print le_antisymm /-
protected theorem le_antisymm {a b : ℚ} (hab : a ≤ b) (hba : b ≤ a) : a = b :=
  by
  have := eq_neg_of_add_eq_zero_left (Rat.nonneg_antisymm hba <| by rwa [← sub_eq_add_neg, neg_sub])
  rwa [neg_neg] at this
#align rat.le_antisymm le_antisymm
-/

/- warning: rat.le_trans clashes with le_trans -> le_trans
Case conversion may be inaccurate. Consider using '#align rat.le_trans le_transₓ'. -/
#print le_trans /-
protected theorem le_trans {a b c : ℚ} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  by
  have : Rat.Nonneg (b - a + (c - b)) := Rat.add_nonneg hab hbc
  simpa [sub_eq_add_neg, add_comm, add_left_comm]
#align rat.le_trans le_trans
-/

instance : LinearOrder ℚ where
  le := Rat.Le
  le_refl := le_refl
  le_trans := @le_trans
  le_antisymm := @le_antisymm
  le_total := Rat.le_total
  DecidableEq := by infer_instance
  decidableLe a b := Rat.instDecidableLeRatInstLERat (b - a)

-- Extra instances to short-circuit type class resolution
instance : LT ℚ := by infer_instance

instance : DistribLattice ℚ := by infer_instance

instance : Lattice ℚ := by infer_instance

instance : SemilatticeInf ℚ := by infer_instance

instance : SemilatticeSup ℚ := by infer_instance

instance : Inf ℚ := by infer_instance

instance : Sup ℚ := by infer_instance

instance : PartialOrder ℚ := by infer_instance

instance : Preorder ℚ := by infer_instance

#print Rat.le_def /-
protected theorem le_def {p q : ℚ} : p ≤ q ↔ p.num * q.den ≤ q.num * p.den :=
  by
  rw [← @num_denom q, ← @num_denom p]
  conv_rhs => simp only [num_denom]
  exact Rat.divInt_le_divInt (by exact_mod_cast p.pos) (by exact_mod_cast q.pos)
#align rat.le_def' Rat.le_def
-/

#print Rat.lt_def /-
protected theorem lt_def {p q : ℚ} : p < q ↔ p.num * q.den < q.num * p.den :=
  by
  rw [lt_iff_le_and_ne, Rat.le_def]
  suffices p ≠ q ↔ p.num * q.denom ≠ q.num * p.denom
    by
    constructor <;> intro h
    · exact lt_iff_le_and_ne.elim_right ⟨h.left, this.elim_left h.right⟩
    · have tmp := lt_iff_le_and_ne.elim_left h; exact ⟨tmp.left, this.elim_right tmp.right⟩
  exact not_iff_not.elim_right eq_iff_mul_eq_mul
#align rat.lt_def Rat.lt_def
-/

theorem nonneg_iff_zero_le {a} : Rat.Nonneg a ↔ 0 ≤ a :=
  show Rat.Nonneg a ↔ Rat.Nonneg (a - 0) by simp
#align rat.nonneg_iff_zero_le Rat.nonneg_iff_zero_le

#print Rat.num_nonneg /-
theorem num_nonneg : ∀ {a : ℚ}, 0 ≤ a.num ↔ 0 ≤ a
  | ⟨n, d, h, c⟩ => @nonneg_iff_zero_le ⟨n, d, h, c⟩
#align rat.num_nonneg_iff_zero_le Rat.num_nonneg
-/

#print Rat.add_le_add_left /-
protected theorem add_le_add_left {a b c : ℚ} : c + a ≤ c + b ↔ a ≤ b := by
  unfold LE.le Rat.Le <;> rw [add_sub_add_left_eq_sub]
#align rat.add_le_add_left Rat.add_le_add_left
-/

/- warning: rat.mul_nonneg clashes with rat.nonneg_mul -> Rat.mul_nonneg
Case conversion may be inaccurate. Consider using '#align rat.mul_nonneg Rat.mul_nonnegₓ'. -/
#print Rat.mul_nonneg /-
protected theorem mul_nonneg {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  rw [← nonneg_iff_zero_le] at ha hb ⊢ <;> exact Rat.mul_nonneg ha hb
#align rat.mul_nonneg Rat.mul_nonneg
-/

instance : LinearOrderedField ℚ :=
  { Rat.field, Rat.linearOrder,
    Rat.semiring with
    zero_le_one := by decide
    add_le_add_left := fun a b ab c => Rat.add_le_add_left.2 ab
    mul_pos := fun a b ha hb =>
      lt_of_le_of_ne (Rat.mul_nonneg (le_of_lt ha) (le_of_lt hb))
        (mul_ne_zero (ne_of_lt ha).symm (ne_of_lt hb).symm).symm }

-- Extra instances to short-circuit type class resolution
instance : LinearOrderedCommRing ℚ := by infer_instance

instance : LinearOrderedRing ℚ := by infer_instance

instance : OrderedRing ℚ := by infer_instance

instance : LinearOrderedSemiring ℚ := by infer_instance

instance : OrderedSemiring ℚ := by infer_instance

instance : LinearOrderedAddCommGroup ℚ := by infer_instance

instance : OrderedAddCommGroup ℚ := by infer_instance

instance : OrderedCancelAddCommMonoid ℚ := by infer_instance

instance : OrderedAddCommMonoid ℚ := by infer_instance

#print Rat.num_pos /-
theorem num_pos {a : ℚ} : 0 < a.num ↔ 0 < a :=
  lt_iff_lt_of_le_iff_le <| by
    simpa [(by cases a <;> rfl : (-a).num = -a.num)] using @num_nonneg_iff_zero_le (-a)
#align rat.num_pos_iff_pos Rat.num_pos
-/

#print Rat.div_lt_div_iff_mul_lt_mul /-
theorem div_lt_div_iff_mul_lt_mul {a b c d : ℤ} (b_pos : 0 < b) (d_pos : 0 < d) :
    (a : ℚ) / b < c / d ↔ a * d < c * b :=
  by
  simp only [lt_iff_le_not_le]
  apply and_congr
  · simp [div_num_denom, Rat.divInt_le_divInt b_pos d_pos]
  · apply not_congr; simp [div_num_denom, Rat.divInt_le_divInt d_pos b_pos]
#align rat.div_lt_div_iff_mul_lt_mul Rat.div_lt_div_iff_mul_lt_mul
-/

#print Rat.lt_one_iff_num_lt_denom /-
theorem lt_one_iff_num_lt_denom {q : ℚ} : q < 1 ↔ q.num < q.den := by simp [Rat.lt_def]
#align rat.lt_one_iff_num_lt_denom Rat.lt_one_iff_num_lt_denom
-/

#print Rat.abs_def /-
theorem abs_def (q : ℚ) : |q| = q.num.natAbs /. q.den :=
  by
  cases' le_total q 0 with hq hq
  · rw [abs_of_nonpos hq]
    rw [← @num_denom q, ← mk_zero_one, Rat.divInt_le_divInt (Int.natCast_pos.2 q.pos) zero_lt_one,
      mul_one, MulZeroClass.zero_mul] at hq
    rw [Int.ofNat_natAbs_of_nonpos hq, ← neg_def, num_denom]
  · rw [abs_of_nonneg hq]
    rw [← @num_denom q, ← mk_zero_one, Rat.divInt_le_divInt zero_lt_one (Int.natCast_pos.2 q.pos),
      mul_one, MulZeroClass.zero_mul] at hq
    rw [Int.natAbs_of_nonneg hq, num_denom]
#align rat.abs_def Rat.abs_def
-/

end Rat

-- We make some assertions here about declarations that do not need to be in the import dependencies
-- for this file, but have been in the past.
assert_not_exists Fintype

assert_not_exists Set.Icc

assert_not_exists GaloisConnection

-- These are less significant, but should not be relaxed until at least after port to Lean 4.
assert_not_exists LinearOrderedCommGroupWithZero

-- This one doesn't exist anywhere!
-- assert_not_exists positive.add_comm_semigroup
