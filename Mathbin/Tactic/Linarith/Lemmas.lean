/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Algebra.Order.Ring.Unbundled.Basic

#align_import tactic.linarith.lemmas from "leanprover-community/mathlib"@"9b2660e1b25419042c8da10bf411aa3c67f14383"

/-!
# Lemmas for `linarith`

This file contains auxiliary lemmas that `linarith` uses to construct proofs.
If you find yourself looking for a theorem here, you might be in the wrong place.
-/


namespace Linarith

theorem zero_lt_one {α} [OrderedSemiring α] [Nontrivial α] : (0 : α) < 1 :=
  zero_lt_one
#align linarith.zero_lt_one Linarith.zero_lt_one

#print Linarith.eq_of_eq_of_eq /-
theorem eq_of_eq_of_eq {α} [OrderedSemiring α] {a b : α} (ha : a = 0) (hb : b = 0) : a + b = 0 := by
  simp [*]
#align linarith.eq_of_eq_of_eq Linarith.eq_of_eq_of_eq
-/

#print Linarith.le_of_eq_of_le /-
theorem le_of_eq_of_le {α} [OrderedSemiring α] {a b : α} (ha : a = 0) (hb : b ≤ 0) : a + b ≤ 0 := by
  simp [*]
#align linarith.le_of_eq_of_le Linarith.le_of_eq_of_le
-/

#print Linarith.lt_of_eq_of_lt /-
theorem lt_of_eq_of_lt {α} [OrderedSemiring α] {a b : α} (ha : a = 0) (hb : b < 0) : a + b < 0 := by
  simp [*]
#align linarith.lt_of_eq_of_lt Linarith.lt_of_eq_of_lt
-/

#print Linarith.le_of_le_of_eq /-
theorem le_of_le_of_eq {α} [OrderedSemiring α] {a b : α} (ha : a ≤ 0) (hb : b = 0) : a + b ≤ 0 := by
  simp [*]
#align linarith.le_of_le_of_eq Linarith.le_of_le_of_eq
-/

#print Linarith.lt_of_lt_of_eq /-
theorem lt_of_lt_of_eq {α} [OrderedSemiring α] {a b : α} (ha : a < 0) (hb : b = 0) : a + b < 0 := by
  simp [*]
#align linarith.lt_of_lt_of_eq Linarith.lt_of_lt_of_eq
-/

theorem hMul_neg {α} [StrictOrderedRing α] {a b : α} (ha : a < 0) (hb : 0 < b) : b * a < 0 :=
  have : -b * a > 0 := mul_pos_of_neg_of_neg (neg_neg_of_pos hb) ha
  neg_of_neg_pos (by simpa)
#align linarith.mul_neg Linarith.hMul_neg

theorem hMul_nonpos {α} [OrderedRing α] {a b : α} (ha : a ≤ 0) (hb : 0 < b) : b * a ≤ 0 :=
  by
  have : -b * a ≥ 0 := mul_nonneg_of_nonpos_of_nonpos (le_of_lt (neg_neg_of_pos hb)) ha
  simpa
#align linarith.mul_nonpos Linarith.hMul_nonpos

-- used alongside `mul_neg` and `mul_nonpos`, so has the same argument pattern for uniformity
@[nolint unused_arguments]
theorem hMul_eq {α} [OrderedSemiring α] {a b : α} (ha : a = 0) (hb : 0 < b) : b * a = 0 := by
  simp [*]
#align linarith.mul_eq Linarith.hMul_eq

#print Linarith.eq_of_not_lt_of_not_gt /-
theorem eq_of_not_lt_of_not_gt {α} [LinearOrder α] (a b : α) (h1 : ¬a < b) (h2 : ¬b < a) : a = b :=
  le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)
#align linarith.eq_of_not_lt_of_not_gt Linarith.eq_of_not_lt_of_not_gt
-/

-- used in the `nlinarith` normalization steps. The `_` argument is for uniformity.
@[nolint unused_arguments]
theorem hMul_zero_eq {α} {R : α → α → Prop} [Semiring α] {a b : α} (_ : R a 0) (h : b = 0) :
    a * b = 0 := by simp [h]
#align linarith.mul_zero_eq Linarith.hMul_zero_eq

-- used in the `nlinarith` normalization steps. The `_` argument is for uniformity.
@[nolint unused_arguments]
theorem zero_hMul_eq {α} {R : α → α → Prop} [Semiring α] {a b : α} (h : a = 0) (_ : R b 0) :
    a * b = 0 := by simp [h]
#align linarith.zero_mul_eq Linarith.zero_hMul_eq

end Linarith

