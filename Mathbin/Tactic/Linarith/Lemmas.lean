/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathbin.Algebra.Order.Ring.Defs

/-!
# Lemmas for `linarith`

This file contains auxiliary lemmas that `linarith` uses to construct proofs.
If you find yourself looking for a theorem here, you might be in the wrong place.
-/


namespace Linarith

theorem eq_of_eq_of_eq {α} [OrderedSemiring α] {a b : α} (ha : a = 0) (hb : b = 0) : a + b = 0 := by
  simp [*]
#align linarith.eq_of_eq_of_eq Linarith.eq_of_eq_of_eq

theorem le_of_eq_of_le {α} [OrderedSemiring α] {a b : α} (ha : a = 0) (hb : b ≤ 0) : a + b ≤ 0 := by
  simp [*]
#align linarith.le_of_eq_of_le Linarith.le_of_eq_of_le

theorem lt_of_eq_of_lt {α} [OrderedSemiring α] {a b : α} (ha : a = 0) (hb : b < 0) : a + b < 0 := by
  simp [*]
#align linarith.lt_of_eq_of_lt Linarith.lt_of_eq_of_lt

theorem le_of_le_of_eq {α} [OrderedSemiring α] {a b : α} (ha : a ≤ 0) (hb : b = 0) : a + b ≤ 0 := by
  simp [*]
#align linarith.le_of_le_of_eq Linarith.le_of_le_of_eq

theorem lt_of_lt_of_eq {α} [OrderedSemiring α] {a b : α} (ha : a < 0) (hb : b = 0) : a + b < 0 := by
  simp [*]
#align linarith.lt_of_lt_of_eq Linarith.lt_of_lt_of_eq

theorem mul_neg {α} [StrictOrderedRing α] {a b : α} (ha : a < 0) (hb : 0 < b) : b * a < 0 :=
  have : -b * a > 0 := mul_pos_of_neg_of_neg (neg_neg_of_pos hb) ha
  neg_of_neg_pos (by simpa)
#align linarith.mul_neg Linarith.mul_neg

theorem mul_nonpos {α} [OrderedRing α] {a b : α} (ha : a ≤ 0) (hb : 0 < b) : b * a ≤ 0 := by
  have : -b * a ≥ 0 := mul_nonneg_of_nonpos_of_nonpos (le_of_lt (neg_neg_of_pos hb)) ha
  simpa
#align linarith.mul_nonpos Linarith.mul_nonpos

-- used alongside `mul_neg` and `mul_nonpos`, so has the same argument pattern for uniformity
@[nolint unused_arguments]
theorem mul_eq {α} [OrderedSemiring α] {a b : α} (ha : a = 0) (hb : 0 < b) : b * a = 0 := by
  simp [*]
#align linarith.mul_eq Linarith.mul_eq

theorem eq_of_not_lt_of_not_gt {α} [LinearOrder α] (a b : α) (h1 : ¬a < b) (h2 : ¬b < a) : a = b :=
  le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)
#align linarith.eq_of_not_lt_of_not_gt Linarith.eq_of_not_lt_of_not_gt

-- used in the `nlinarith` normalization steps. The `_` argument is for uniformity.
@[nolint unused_arguments]
theorem mul_zero_eq {α} {R : α → α → Prop} [Semiring α] {a b : α} (_ : R a 0) (h : b = 0) :
    a * b = 0 := by simp [h]
#align linarith.mul_zero_eq Linarith.mul_zero_eq

-- used in the `nlinarith` normalization steps. The `_` argument is for uniformity.
@[nolint unused_arguments]
theorem zero_mul_eq {α} {R : α → α → Prop} [Semiring α] {a b : α} (h : a = 0) (_ : R b 0) :
    a * b = 0 := by simp [h]
#align linarith.zero_mul_eq Linarith.zero_mul_eq

end Linarith

