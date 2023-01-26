/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Patrick Massot

! This file was ported from Lean 3 source module data.set.pointwise.interval
! leanprover-community/mathlib commit f93c11933efbc3c2f0299e47b8ff83e9b539cbf6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Intervals.UnorderedInterval
import Mathbin.Data.Set.Intervals.Monoid
import Mathbin.Data.Set.Pointwise.Basic
import Mathbin.Algebra.Order.Field.Basic
import Mathbin.Algebra.Order.Group.MinMax

/-!
# (Pre)images of intervals

In this file we prove a bunch of trivial lemmas like “if we add `a` to all points of `[b, c]`,
then we get `[a + b, a + c]`”. For the functions `x ↦ x ± a`, `x ↦ a ± x`, and `x ↦ -x` we prove
lemmas about preimages and images of all intervals. We also prove a few lemmas about images under
`x ↦ a * x`, `x ↦ x * a` and `x ↦ x⁻¹`.
-/


open Interval Pointwise

variable {α : Type _}

namespace Set

section OrderedAddCommGroup

variable [OrderedAddCommGroup α] (a b c : α)

/-!
### Preimages under `x ↦ a + x`
-/


@[simp]
theorem preimage_const_add_ici : (fun x => a + x) ⁻¹' Ici b = Ici (b - a) :=
  ext fun x => sub_le_iff_le_add'.symm
#align set.preimage_const_add_Ici Set.preimage_const_add_ici

@[simp]
theorem preimage_const_add_ioi : (fun x => a + x) ⁻¹' Ioi b = Ioi (b - a) :=
  ext fun x => sub_lt_iff_lt_add'.symm
#align set.preimage_const_add_Ioi Set.preimage_const_add_ioi

@[simp]
theorem preimage_const_add_iic : (fun x => a + x) ⁻¹' Iic b = Iic (b - a) :=
  ext fun x => le_sub_iff_add_le'.symm
#align set.preimage_const_add_Iic Set.preimage_const_add_iic

@[simp]
theorem preimage_const_add_iio : (fun x => a + x) ⁻¹' Iio b = Iio (b - a) :=
  ext fun x => lt_sub_iff_add_lt'.symm
#align set.preimage_const_add_Iio Set.preimage_const_add_iio

@[simp]
theorem preimage_const_add_icc : (fun x => a + x) ⁻¹' Icc b c = Icc (b - a) (c - a) := by
  simp [← Ici_inter_Iic]
#align set.preimage_const_add_Icc Set.preimage_const_add_icc

@[simp]
theorem preimage_const_add_ico : (fun x => a + x) ⁻¹' Ico b c = Ico (b - a) (c - a) := by
  simp [← Ici_inter_Iio]
#align set.preimage_const_add_Ico Set.preimage_const_add_ico

@[simp]
theorem preimage_const_add_ioc : (fun x => a + x) ⁻¹' Ioc b c = Ioc (b - a) (c - a) := by
  simp [← Ioi_inter_Iic]
#align set.preimage_const_add_Ioc Set.preimage_const_add_ioc

@[simp]
theorem preimage_const_add_ioo : (fun x => a + x) ⁻¹' Ioo b c = Ioo (b - a) (c - a) := by
  simp [← Ioi_inter_Iio]
#align set.preimage_const_add_Ioo Set.preimage_const_add_ioo

/-!
### Preimages under `x ↦ x + a`
-/


@[simp]
theorem preimage_add_const_ici : (fun x => x + a) ⁻¹' Ici b = Ici (b - a) :=
  ext fun x => sub_le_iff_le_add.symm
#align set.preimage_add_const_Ici Set.preimage_add_const_ici

@[simp]
theorem preimage_add_const_ioi : (fun x => x + a) ⁻¹' Ioi b = Ioi (b - a) :=
  ext fun x => sub_lt_iff_lt_add.symm
#align set.preimage_add_const_Ioi Set.preimage_add_const_ioi

@[simp]
theorem preimage_add_const_iic : (fun x => x + a) ⁻¹' Iic b = Iic (b - a) :=
  ext fun x => le_sub_iff_add_le.symm
#align set.preimage_add_const_Iic Set.preimage_add_const_iic

@[simp]
theorem preimage_add_const_iio : (fun x => x + a) ⁻¹' Iio b = Iio (b - a) :=
  ext fun x => lt_sub_iff_add_lt.symm
#align set.preimage_add_const_Iio Set.preimage_add_const_iio

@[simp]
theorem preimage_add_const_icc : (fun x => x + a) ⁻¹' Icc b c = Icc (b - a) (c - a) := by
  simp [← Ici_inter_Iic]
#align set.preimage_add_const_Icc Set.preimage_add_const_icc

@[simp]
theorem preimage_add_const_ico : (fun x => x + a) ⁻¹' Ico b c = Ico (b - a) (c - a) := by
  simp [← Ici_inter_Iio]
#align set.preimage_add_const_Ico Set.preimage_add_const_ico

@[simp]
theorem preimage_add_const_ioc : (fun x => x + a) ⁻¹' Ioc b c = Ioc (b - a) (c - a) := by
  simp [← Ioi_inter_Iic]
#align set.preimage_add_const_Ioc Set.preimage_add_const_ioc

@[simp]
theorem preimage_add_const_ioo : (fun x => x + a) ⁻¹' Ioo b c = Ioo (b - a) (c - a) := by
  simp [← Ioi_inter_Iio]
#align set.preimage_add_const_Ioo Set.preimage_add_const_ioo

/-!
### Preimages under `x ↦ -x`
-/


@[simp]
theorem preimage_neg_ici : -Ici a = Iic (-a) :=
  ext fun x => le_neg
#align set.preimage_neg_Ici Set.preimage_neg_ici

@[simp]
theorem preimage_neg_iic : -Iic a = Ici (-a) :=
  ext fun x => neg_le
#align set.preimage_neg_Iic Set.preimage_neg_iic

@[simp]
theorem preimage_neg_ioi : -Ioi a = Iio (-a) :=
  ext fun x => lt_neg
#align set.preimage_neg_Ioi Set.preimage_neg_ioi

@[simp]
theorem preimage_neg_iio : -Iio a = Ioi (-a) :=
  ext fun x => neg_lt
#align set.preimage_neg_Iio Set.preimage_neg_iio

@[simp]
theorem preimage_neg_icc : -Icc a b = Icc (-b) (-a) := by simp [← Ici_inter_Iic, inter_comm]
#align set.preimage_neg_Icc Set.preimage_neg_icc

@[simp]
theorem preimage_neg_ico : -Ico a b = Ioc (-b) (-a) := by
  simp [← Ici_inter_Iio, ← Ioi_inter_Iic, inter_comm]
#align set.preimage_neg_Ico Set.preimage_neg_ico

@[simp]
theorem preimage_neg_ioc : -Ioc a b = Ico (-b) (-a) := by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]
#align set.preimage_neg_Ioc Set.preimage_neg_ioc

@[simp]
theorem preimage_neg_ioo : -Ioo a b = Ioo (-b) (-a) := by simp [← Ioi_inter_Iio, inter_comm]
#align set.preimage_neg_Ioo Set.preimage_neg_ioo

/-!
### Preimages under `x ↦ x - a`
-/


@[simp]
theorem preimage_sub_const_ici : (fun x => x - a) ⁻¹' Ici b = Ici (b + a) := by
  simp [sub_eq_add_neg]
#align set.preimage_sub_const_Ici Set.preimage_sub_const_ici

@[simp]
theorem preimage_sub_const_ioi : (fun x => x - a) ⁻¹' Ioi b = Ioi (b + a) := by
  simp [sub_eq_add_neg]
#align set.preimage_sub_const_Ioi Set.preimage_sub_const_ioi

@[simp]
theorem preimage_sub_const_iic : (fun x => x - a) ⁻¹' Iic b = Iic (b + a) := by
  simp [sub_eq_add_neg]
#align set.preimage_sub_const_Iic Set.preimage_sub_const_iic

@[simp]
theorem preimage_sub_const_iio : (fun x => x - a) ⁻¹' Iio b = Iio (b + a) := by
  simp [sub_eq_add_neg]
#align set.preimage_sub_const_Iio Set.preimage_sub_const_iio

@[simp]
theorem preimage_sub_const_icc : (fun x => x - a) ⁻¹' Icc b c = Icc (b + a) (c + a) := by
  simp [sub_eq_add_neg]
#align set.preimage_sub_const_Icc Set.preimage_sub_const_icc

@[simp]
theorem preimage_sub_const_ico : (fun x => x - a) ⁻¹' Ico b c = Ico (b + a) (c + a) := by
  simp [sub_eq_add_neg]
#align set.preimage_sub_const_Ico Set.preimage_sub_const_ico

@[simp]
theorem preimage_sub_const_ioc : (fun x => x - a) ⁻¹' Ioc b c = Ioc (b + a) (c + a) := by
  simp [sub_eq_add_neg]
#align set.preimage_sub_const_Ioc Set.preimage_sub_const_ioc

@[simp]
theorem preimage_sub_const_ioo : (fun x => x - a) ⁻¹' Ioo b c = Ioo (b + a) (c + a) := by
  simp [sub_eq_add_neg]
#align set.preimage_sub_const_Ioo Set.preimage_sub_const_ioo

/-!
### Preimages under `x ↦ a - x`
-/


@[simp]
theorem preimage_const_sub_ici : (fun x => a - x) ⁻¹' Ici b = Iic (a - b) :=
  ext fun x => le_sub_comm
#align set.preimage_const_sub_Ici Set.preimage_const_sub_ici

@[simp]
theorem preimage_const_sub_iic : (fun x => a - x) ⁻¹' Iic b = Ici (a - b) :=
  ext fun x => sub_le_comm
#align set.preimage_const_sub_Iic Set.preimage_const_sub_iic

@[simp]
theorem preimage_const_sub_ioi : (fun x => a - x) ⁻¹' Ioi b = Iio (a - b) :=
  ext fun x => lt_sub_comm
#align set.preimage_const_sub_Ioi Set.preimage_const_sub_ioi

@[simp]
theorem preimage_const_sub_iio : (fun x => a - x) ⁻¹' Iio b = Ioi (a - b) :=
  ext fun x => sub_lt_comm
#align set.preimage_const_sub_Iio Set.preimage_const_sub_iio

@[simp]
theorem preimage_const_sub_icc : (fun x => a - x) ⁻¹' Icc b c = Icc (a - c) (a - b) := by
  simp [← Ici_inter_Iic, inter_comm]
#align set.preimage_const_sub_Icc Set.preimage_const_sub_icc

@[simp]
theorem preimage_const_sub_ico : (fun x => a - x) ⁻¹' Ico b c = Ioc (a - c) (a - b) := by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]
#align set.preimage_const_sub_Ico Set.preimage_const_sub_ico

@[simp]
theorem preimage_const_sub_ioc : (fun x => a - x) ⁻¹' Ioc b c = Ico (a - c) (a - b) := by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]
#align set.preimage_const_sub_Ioc Set.preimage_const_sub_ioc

@[simp]
theorem preimage_const_sub_ioo : (fun x => a - x) ⁻¹' Ioo b c = Ioo (a - c) (a - b) := by
  simp [← Ioi_inter_Iio, inter_comm]
#align set.preimage_const_sub_Ioo Set.preimage_const_sub_ioo

/-!
### Images under `x ↦ a + x`
-/


@[simp]
theorem image_const_add_iic : (fun x => a + x) '' Iic b = Iic (a + b) := by simp [add_comm]
#align set.image_const_add_Iic Set.image_const_add_iic

@[simp]
theorem image_const_add_iio : (fun x => a + x) '' Iio b = Iio (a + b) := by simp [add_comm]
#align set.image_const_add_Iio Set.image_const_add_iio

/-!
### Images under `x ↦ x + a`
-/


@[simp]
theorem image_add_const_iic : (fun x => x + a) '' Iic b = Iic (b + a) := by simp
#align set.image_add_const_Iic Set.image_add_const_iic

@[simp]
theorem image_add_const_iio : (fun x => x + a) '' Iio b = Iio (b + a) := by simp
#align set.image_add_const_Iio Set.image_add_const_iio

/-!
### Images under `x ↦ -x`
-/


theorem image_neg_ici : Neg.neg '' Ici a = Iic (-a) := by simp
#align set.image_neg_Ici Set.image_neg_ici

theorem image_neg_iic : Neg.neg '' Iic a = Ici (-a) := by simp
#align set.image_neg_Iic Set.image_neg_iic

theorem image_neg_ioi : Neg.neg '' Ioi a = Iio (-a) := by simp
#align set.image_neg_Ioi Set.image_neg_ioi

theorem image_neg_iio : Neg.neg '' Iio a = Ioi (-a) := by simp
#align set.image_neg_Iio Set.image_neg_iio

theorem image_neg_icc : Neg.neg '' Icc a b = Icc (-b) (-a) := by simp
#align set.image_neg_Icc Set.image_neg_icc

theorem image_neg_ico : Neg.neg '' Ico a b = Ioc (-b) (-a) := by simp
#align set.image_neg_Ico Set.image_neg_ico

theorem image_neg_ioc : Neg.neg '' Ioc a b = Ico (-b) (-a) := by simp
#align set.image_neg_Ioc Set.image_neg_ioc

theorem image_neg_ioo : Neg.neg '' Ioo a b = Ioo (-b) (-a) := by simp
#align set.image_neg_Ioo Set.image_neg_ioo

/-!
### Images under `x ↦ a - x`
-/


@[simp]
theorem image_const_sub_ici : (fun x => a - x) '' Ici b = Iic (a - b) := by
  simp [sub_eq_add_neg, image_comp (fun x => a + x) fun x => -x]
#align set.image_const_sub_Ici Set.image_const_sub_ici

@[simp]
theorem image_const_sub_iic : (fun x => a - x) '' Iic b = Ici (a - b) := by
  simp [sub_eq_add_neg, image_comp (fun x => a + x) fun x => -x, add_comm]
#align set.image_const_sub_Iic Set.image_const_sub_iic

@[simp]
theorem image_const_sub_ioi : (fun x => a - x) '' Ioi b = Iio (a - b) := by
  simp [sub_eq_add_neg, image_comp (fun x => a + x) fun x => -x]
#align set.image_const_sub_Ioi Set.image_const_sub_ioi

@[simp]
theorem image_const_sub_iio : (fun x => a - x) '' Iio b = Ioi (a - b) := by
  simp [sub_eq_add_neg, image_comp (fun x => a + x) fun x => -x, add_comm]
#align set.image_const_sub_Iio Set.image_const_sub_iio

@[simp]
theorem image_const_sub_icc : (fun x => a - x) '' Icc b c = Icc (a - c) (a - b) := by
  simp [sub_eq_add_neg, image_comp (fun x => a + x) fun x => -x, add_comm]
#align set.image_const_sub_Icc Set.image_const_sub_icc

@[simp]
theorem image_const_sub_ico : (fun x => a - x) '' Ico b c = Ioc (a - c) (a - b) := by
  simp [sub_eq_add_neg, image_comp (fun x => a + x) fun x => -x, add_comm]
#align set.image_const_sub_Ico Set.image_const_sub_ico

@[simp]
theorem image_const_sub_ioc : (fun x => a - x) '' Ioc b c = Ico (a - c) (a - b) := by
  simp [sub_eq_add_neg, image_comp (fun x => a + x) fun x => -x, add_comm]
#align set.image_const_sub_Ioc Set.image_const_sub_ioc

@[simp]
theorem image_const_sub_ioo : (fun x => a - x) '' Ioo b c = Ioo (a - c) (a - b) := by
  simp [sub_eq_add_neg, image_comp (fun x => a + x) fun x => -x, add_comm]
#align set.image_const_sub_Ioo Set.image_const_sub_ioo

/-!
### Images under `x ↦ x - a`
-/


@[simp]
theorem image_sub_const_ici : (fun x => x - a) '' Ici b = Ici (b - a) := by simp [sub_eq_neg_add]
#align set.image_sub_const_Ici Set.image_sub_const_ici

@[simp]
theorem image_sub_const_iic : (fun x => x - a) '' Iic b = Iic (b - a) := by simp [sub_eq_neg_add]
#align set.image_sub_const_Iic Set.image_sub_const_iic

@[simp]
theorem image_sub_const_ioi : (fun x => x - a) '' Ioi b = Ioi (b - a) := by simp [sub_eq_neg_add]
#align set.image_sub_const_Ioi Set.image_sub_const_ioi

@[simp]
theorem image_sub_const_iio : (fun x => x - a) '' Iio b = Iio (b - a) := by simp [sub_eq_neg_add]
#align set.image_sub_const_Iio Set.image_sub_const_iio

@[simp]
theorem image_sub_const_icc : (fun x => x - a) '' Icc b c = Icc (b - a) (c - a) := by
  simp [sub_eq_neg_add]
#align set.image_sub_const_Icc Set.image_sub_const_icc

@[simp]
theorem image_sub_const_ico : (fun x => x - a) '' Ico b c = Ico (b - a) (c - a) := by
  simp [sub_eq_neg_add]
#align set.image_sub_const_Ico Set.image_sub_const_ico

@[simp]
theorem image_sub_const_ioc : (fun x => x - a) '' Ioc b c = Ioc (b - a) (c - a) := by
  simp [sub_eq_neg_add]
#align set.image_sub_const_Ioc Set.image_sub_const_ioc

@[simp]
theorem image_sub_const_ioo : (fun x => x - a) '' Ioo b c = Ioo (b - a) (c - a) := by
  simp [sub_eq_neg_add]
#align set.image_sub_const_Ioo Set.image_sub_const_ioo

/-!
### Bijections
-/


theorem iic_add_bij : BijOn (· + a) (Iic b) (Iic (b + a)) :=
  image_add_const_iic a b ▸ ((add_left_injective _).InjOn _).bij_on_image
#align set.Iic_add_bij Set.iic_add_bij

theorem iio_add_bij : BijOn (· + a) (Iio b) (Iio (b + a)) :=
  image_add_const_iio a b ▸ ((add_left_injective _).InjOn _).bij_on_image
#align set.Iio_add_bij Set.iio_add_bij

end OrderedAddCommGroup

section LinearOrderedAddCommGroup

variable [LinearOrderedAddCommGroup α] (a b c d : α)

@[simp]
theorem preimage_const_add_uIcc : (fun x => a + x) ⁻¹' [b, c] = [b - a, c - a] := by
  simp only [← Icc_min_max, preimage_const_add_Icc, min_sub_sub_right, max_sub_sub_right]
#align set.preimage_const_add_uIcc Set.preimage_const_add_uIcc

@[simp]
theorem preimage_add_const_uIcc : (fun x => x + a) ⁻¹' [b, c] = [b - a, c - a] := by
  simpa only [add_comm] using preimage_const_add_uIcc a b c
#align set.preimage_add_const_uIcc Set.preimage_add_const_uIcc

@[simp]
theorem preimage_neg_uIcc : -[a, b] = [-a, -b] := by
  simp only [← Icc_min_max, preimage_neg_Icc, min_neg_neg, max_neg_neg]
#align set.preimage_neg_uIcc Set.preimage_neg_uIcc

@[simp]
theorem preimage_sub_const_uIcc : (fun x => x - a) ⁻¹' [b, c] = [b + a, c + a] := by
  simp [sub_eq_add_neg]
#align set.preimage_sub_const_uIcc Set.preimage_sub_const_uIcc

@[simp]
theorem preimage_const_sub_uIcc : (fun x => a - x) ⁻¹' [b, c] = [a - b, a - c] :=
  by
  simp_rw [← Icc_min_max, preimage_const_sub_Icc]
  simp only [sub_eq_add_neg, min_add_add_left, max_add_add_left, min_neg_neg, max_neg_neg]
#align set.preimage_const_sub_uIcc Set.preimage_const_sub_uIcc

@[simp]
theorem image_const_add_uIcc : (fun x => a + x) '' [b, c] = [a + b, a + c] := by simp [add_comm]
#align set.image_const_add_uIcc Set.image_const_add_uIcc

@[simp]
theorem image_add_const_uIcc : (fun x => x + a) '' [b, c] = [b + a, c + a] := by simp
#align set.image_add_const_uIcc Set.image_add_const_uIcc

@[simp]
theorem image_const_sub_uIcc : (fun x => a - x) '' [b, c] = [a - b, a - c] := by
  simp [sub_eq_add_neg, image_comp (fun x => a + x) fun x => -x]
#align set.image_const_sub_uIcc Set.image_const_sub_uIcc

@[simp]
theorem image_sub_const_uIcc : (fun x => x - a) '' [b, c] = [b - a, c - a] := by
  simp [sub_eq_add_neg, add_comm]
#align set.image_sub_const_uIcc Set.image_sub_const_uIcc

theorem image_neg_uIcc : Neg.neg '' [a, b] = [-a, -b] := by simp
#align set.image_neg_uIcc Set.image_neg_uIcc

variable {a b c d}

/-- If `[c, d]` is a subinterval of `[a, b]`, then the distance between `c` and `d` is less than or
equal to that of `a` and `b` -/
theorem abs_sub_le_of_uIcc_subset_uIcc (h : [c, d] ⊆ [a, b]) : |d - c| ≤ |b - a| :=
  by
  rw [← max_sub_min_eq_abs, ← max_sub_min_eq_abs]
  rw [uIcc_subset_uIcc_iff_le] at h
  exact sub_le_sub h.2 h.1
#align set.abs_sub_le_of_uIcc_subset_uIcc Set.abs_sub_le_of_uIcc_subset_uIcc

/-- If `c ∈ [a, b]`, then the distance between `a` and `c` is less than or equal to
that of `a` and `b`  -/
theorem abs_sub_left_of_mem_uIcc (h : c ∈ [a, b]) : |c - a| ≤ |b - a| :=
  abs_sub_le_of_uIcc_subset_uIcc <| uIcc_subset_uIcc_left h
#align set.abs_sub_left_of_mem_uIcc Set.abs_sub_left_of_mem_uIcc

/-- If `x ∈ [a, b]`, then the distance between `c` and `b` is less than or equal to
that of `a` and `b`  -/
theorem abs_sub_right_of_mem_uIcc (h : c ∈ [a, b]) : |b - c| ≤ |b - a| :=
  abs_sub_le_of_uIcc_subset_uIcc <| uIcc_subset_uIcc_right h
#align set.abs_sub_right_of_mem_uIcc Set.abs_sub_right_of_mem_uIcc

end LinearOrderedAddCommGroup

/-!
### Multiplication and inverse in a field
-/


section LinearOrderedField

variable [LinearOrderedField α] {a : α}

@[simp]
theorem preimage_mul_const_iio (a : α) {c : α} (h : 0 < c) :
    (fun x => x * c) ⁻¹' Iio a = Iio (a / c) :=
  ext fun x => (lt_div_iff h).symm
#align set.preimage_mul_const_Iio Set.preimage_mul_const_iio

@[simp]
theorem preimage_mul_const_ioi (a : α) {c : α} (h : 0 < c) :
    (fun x => x * c) ⁻¹' Ioi a = Ioi (a / c) :=
  ext fun x => (div_lt_iff h).symm
#align set.preimage_mul_const_Ioi Set.preimage_mul_const_ioi

@[simp]
theorem preimage_mul_const_iic (a : α) {c : α} (h : 0 < c) :
    (fun x => x * c) ⁻¹' Iic a = Iic (a / c) :=
  ext fun x => (le_div_iff h).symm
#align set.preimage_mul_const_Iic Set.preimage_mul_const_iic

@[simp]
theorem preimage_mul_const_ici (a : α) {c : α} (h : 0 < c) :
    (fun x => x * c) ⁻¹' Ici a = Ici (a / c) :=
  ext fun x => (div_le_iff h).symm
#align set.preimage_mul_const_Ici Set.preimage_mul_const_ici

@[simp]
theorem preimage_mul_const_ioo (a b : α) {c : α} (h : 0 < c) :
    (fun x => x * c) ⁻¹' Ioo a b = Ioo (a / c) (b / c) := by simp [← Ioi_inter_Iio, h]
#align set.preimage_mul_const_Ioo Set.preimage_mul_const_ioo

@[simp]
theorem preimage_mul_const_ioc (a b : α) {c : α} (h : 0 < c) :
    (fun x => x * c) ⁻¹' Ioc a b = Ioc (a / c) (b / c) := by simp [← Ioi_inter_Iic, h]
#align set.preimage_mul_const_Ioc Set.preimage_mul_const_ioc

@[simp]
theorem preimage_mul_const_ico (a b : α) {c : α} (h : 0 < c) :
    (fun x => x * c) ⁻¹' Ico a b = Ico (a / c) (b / c) := by simp [← Ici_inter_Iio, h]
#align set.preimage_mul_const_Ico Set.preimage_mul_const_ico

@[simp]
theorem preimage_mul_const_icc (a b : α) {c : α} (h : 0 < c) :
    (fun x => x * c) ⁻¹' Icc a b = Icc (a / c) (b / c) := by simp [← Ici_inter_Iic, h]
#align set.preimage_mul_const_Icc Set.preimage_mul_const_icc

@[simp]
theorem preimage_mul_const_iio_of_neg (a : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Iio a = Ioi (a / c) :=
  ext fun x => (div_lt_iff_of_neg h).symm
#align set.preimage_mul_const_Iio_of_neg Set.preimage_mul_const_iio_of_neg

@[simp]
theorem preimage_mul_const_ioi_of_neg (a : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ioi a = Iio (a / c) :=
  ext fun x => (lt_div_iff_of_neg h).symm
#align set.preimage_mul_const_Ioi_of_neg Set.preimage_mul_const_ioi_of_neg

@[simp]
theorem preimage_mul_const_iic_of_neg (a : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Iic a = Ici (a / c) :=
  ext fun x => (div_le_iff_of_neg h).symm
#align set.preimage_mul_const_Iic_of_neg Set.preimage_mul_const_iic_of_neg

@[simp]
theorem preimage_mul_const_ici_of_neg (a : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ici a = Iic (a / c) :=
  ext fun x => (le_div_iff_of_neg h).symm
#align set.preimage_mul_const_Ici_of_neg Set.preimage_mul_const_ici_of_neg

@[simp]
theorem preimage_mul_const_ioo_of_neg (a b : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ioo a b = Ioo (b / c) (a / c) := by simp [← Ioi_inter_Iio, h, inter_comm]
#align set.preimage_mul_const_Ioo_of_neg Set.preimage_mul_const_ioo_of_neg

@[simp]
theorem preimage_mul_const_ioc_of_neg (a b : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ioc a b = Ico (b / c) (a / c) := by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, h, inter_comm]
#align set.preimage_mul_const_Ioc_of_neg Set.preimage_mul_const_ioc_of_neg

@[simp]
theorem preimage_mul_const_ico_of_neg (a b : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ico a b = Ioc (b / c) (a / c) := by
  simp [← Ici_inter_Iio, ← Ioi_inter_Iic, h, inter_comm]
#align set.preimage_mul_const_Ico_of_neg Set.preimage_mul_const_ico_of_neg

@[simp]
theorem preimage_mul_const_icc_of_neg (a b : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Icc a b = Icc (b / c) (a / c) := by simp [← Ici_inter_Iic, h, inter_comm]
#align set.preimage_mul_const_Icc_of_neg Set.preimage_mul_const_icc_of_neg

@[simp]
theorem preimage_const_mul_iio (a : α) {c : α} (h : 0 < c) : (· * ·) c ⁻¹' Iio a = Iio (a / c) :=
  ext fun x => (lt_div_iff' h).symm
#align set.preimage_const_mul_Iio Set.preimage_const_mul_iio

@[simp]
theorem preimage_const_mul_ioi (a : α) {c : α} (h : 0 < c) : (· * ·) c ⁻¹' Ioi a = Ioi (a / c) :=
  ext fun x => (div_lt_iff' h).symm
#align set.preimage_const_mul_Ioi Set.preimage_const_mul_ioi

@[simp]
theorem preimage_const_mul_iic (a : α) {c : α} (h : 0 < c) : (· * ·) c ⁻¹' Iic a = Iic (a / c) :=
  ext fun x => (le_div_iff' h).symm
#align set.preimage_const_mul_Iic Set.preimage_const_mul_iic

@[simp]
theorem preimage_const_mul_ici (a : α) {c : α} (h : 0 < c) : (· * ·) c ⁻¹' Ici a = Ici (a / c) :=
  ext fun x => (div_le_iff' h).symm
#align set.preimage_const_mul_Ici Set.preimage_const_mul_ici

@[simp]
theorem preimage_const_mul_ioo (a b : α) {c : α} (h : 0 < c) :
    (· * ·) c ⁻¹' Ioo a b = Ioo (a / c) (b / c) := by simp [← Ioi_inter_Iio, h]
#align set.preimage_const_mul_Ioo Set.preimage_const_mul_ioo

@[simp]
theorem preimage_const_mul_ioc (a b : α) {c : α} (h : 0 < c) :
    (· * ·) c ⁻¹' Ioc a b = Ioc (a / c) (b / c) := by simp [← Ioi_inter_Iic, h]
#align set.preimage_const_mul_Ioc Set.preimage_const_mul_ioc

@[simp]
theorem preimage_const_mul_ico (a b : α) {c : α} (h : 0 < c) :
    (· * ·) c ⁻¹' Ico a b = Ico (a / c) (b / c) := by simp [← Ici_inter_Iio, h]
#align set.preimage_const_mul_Ico Set.preimage_const_mul_ico

@[simp]
theorem preimage_const_mul_icc (a b : α) {c : α} (h : 0 < c) :
    (· * ·) c ⁻¹' Icc a b = Icc (a / c) (b / c) := by simp [← Ici_inter_Iic, h]
#align set.preimage_const_mul_Icc Set.preimage_const_mul_icc

@[simp]
theorem preimage_const_mul_iio_of_neg (a : α) {c : α} (h : c < 0) :
    (· * ·) c ⁻¹' Iio a = Ioi (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Iio_of_neg a h
#align set.preimage_const_mul_Iio_of_neg Set.preimage_const_mul_iio_of_neg

@[simp]
theorem preimage_const_mul_ioi_of_neg (a : α) {c : α} (h : c < 0) :
    (· * ·) c ⁻¹' Ioi a = Iio (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ioi_of_neg a h
#align set.preimage_const_mul_Ioi_of_neg Set.preimage_const_mul_ioi_of_neg

@[simp]
theorem preimage_const_mul_iic_of_neg (a : α) {c : α} (h : c < 0) :
    (· * ·) c ⁻¹' Iic a = Ici (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Iic_of_neg a h
#align set.preimage_const_mul_Iic_of_neg Set.preimage_const_mul_iic_of_neg

@[simp]
theorem preimage_const_mul_ici_of_neg (a : α) {c : α} (h : c < 0) :
    (· * ·) c ⁻¹' Ici a = Iic (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ici_of_neg a h
#align set.preimage_const_mul_Ici_of_neg Set.preimage_const_mul_ici_of_neg

@[simp]
theorem preimage_const_mul_ioo_of_neg (a b : α) {c : α} (h : c < 0) :
    (· * ·) c ⁻¹' Ioo a b = Ioo (b / c) (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ioo_of_neg a b h
#align set.preimage_const_mul_Ioo_of_neg Set.preimage_const_mul_ioo_of_neg

@[simp]
theorem preimage_const_mul_ioc_of_neg (a b : α) {c : α} (h : c < 0) :
    (· * ·) c ⁻¹' Ioc a b = Ico (b / c) (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ioc_of_neg a b h
#align set.preimage_const_mul_Ioc_of_neg Set.preimage_const_mul_ioc_of_neg

@[simp]
theorem preimage_const_mul_ico_of_neg (a b : α) {c : α} (h : c < 0) :
    (· * ·) c ⁻¹' Ico a b = Ioc (b / c) (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ico_of_neg a b h
#align set.preimage_const_mul_Ico_of_neg Set.preimage_const_mul_ico_of_neg

@[simp]
theorem preimage_const_mul_icc_of_neg (a b : α) {c : α} (h : c < 0) :
    (· * ·) c ⁻¹' Icc a b = Icc (b / c) (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Icc_of_neg a b h
#align set.preimage_const_mul_Icc_of_neg Set.preimage_const_mul_icc_of_neg

@[simp]
theorem preimage_mul_const_uIcc (ha : a ≠ 0) (b c : α) :
    (fun x => x * a) ⁻¹' [b, c] = [b / a, c / a] :=
  (lt_or_gt_of_ne ha).elim
    (fun h => by
      simp [← Icc_min_max, h, h.le, min_div_div_right_of_nonpos, max_div_div_right_of_nonpos])
    fun ha : 0 < a => by simp [← Icc_min_max, ha, ha.le, min_div_div_right, max_div_div_right]
#align set.preimage_mul_const_uIcc Set.preimage_mul_const_uIcc

@[simp]
theorem preimage_const_mul_uIcc (ha : a ≠ 0) (b c : α) :
    (fun x => a * x) ⁻¹' [b, c] = [b / a, c / a] := by
  simp only [← preimage_mul_const_uIcc ha, mul_comm]
#align set.preimage_const_mul_uIcc Set.preimage_const_mul_uIcc

@[simp]
theorem preimage_div_const_uIcc (ha : a ≠ 0) (b c : α) :
    (fun x => x / a) ⁻¹' [b, c] = [b * a, c * a] := by
  simp only [div_eq_mul_inv, preimage_mul_const_uIcc (inv_ne_zero ha), inv_inv]
#align set.preimage_div_const_uIcc Set.preimage_div_const_uIcc

@[simp]
theorem image_mul_const_uIcc (a b c : α) : (fun x => x * a) '' [b, c] = [b * a, c * a] :=
  if ha : a = 0 then by simp [ha]
  else
    calc
      (fun x => x * a) '' [b, c] = (fun x => x * a⁻¹) ⁻¹' [b, c] :=
        (Units.mk0 a ha).mul_right.image_eq_preimage _
      _ = (fun x => x / a) ⁻¹' [b, c] := by simp only [div_eq_mul_inv]
      _ = [b * a, c * a] := preimage_div_const_uIcc ha _ _
      
#align set.image_mul_const_uIcc Set.image_mul_const_uIcc

@[simp]
theorem image_const_mul_uIcc (a b c : α) : (fun x => a * x) '' [b, c] = [a * b, a * c] := by
  simpa only [mul_comm] using image_mul_const_uIcc a b c
#align set.image_const_mul_uIcc Set.image_const_mul_uIcc

@[simp]
theorem image_div_const_uIcc (a b c : α) : (fun x => x / a) '' [b, c] = [b / a, c / a] := by
  simp only [div_eq_mul_inv, image_mul_const_uIcc]
#align set.image_div_const_uIcc Set.image_div_const_uIcc

theorem image_mul_right_Icc' (a b : α) {c : α} (h : 0 < c) :
    (fun x => x * c) '' Icc a b = Icc (a * c) (b * c) :=
  ((Units.mk0 c h.ne').mul_right.image_eq_preimage _).trans (by simp [h, division_def])
#align set.image_mul_right_Icc' Set.image_mul_right_Icc'

theorem image_mul_right_icc {a b c : α} (hab : a ≤ b) (hc : 0 ≤ c) :
    (fun x => x * c) '' Icc a b = Icc (a * c) (b * c) :=
  by
  cases eq_or_lt_of_le hc
  · subst c
    simp [(nonempty_Icc.2 hab).image_const]
  exact image_mul_right_Icc' a b ‹0 < c›
#align set.image_mul_right_Icc Set.image_mul_right_icc

theorem image_mul_left_Icc' {a : α} (h : 0 < a) (b c : α) :
    (· * ·) a '' Icc b c = Icc (a * b) (a * c) := by
  convert image_mul_right_Icc' b c h using 1 <;> simp only [mul_comm _ a]
#align set.image_mul_left_Icc' Set.image_mul_left_Icc'

theorem image_mul_left_icc {a b c : α} (ha : 0 ≤ a) (hbc : b ≤ c) :
    (· * ·) a '' Icc b c = Icc (a * b) (a * c) := by
  convert image_mul_right_Icc hbc ha using 1 <;> simp only [mul_comm _ a]
#align set.image_mul_left_Icc Set.image_mul_left_icc

theorem image_mul_right_ioo (a b : α) {c : α} (h : 0 < c) :
    (fun x => x * c) '' Ioo a b = Ioo (a * c) (b * c) :=
  ((Units.mk0 c h.ne').mul_right.image_eq_preimage _).trans (by simp [h, division_def])
#align set.image_mul_right_Ioo Set.image_mul_right_ioo

theorem image_mul_left_ioo {a : α} (h : 0 < a) (b c : α) :
    (· * ·) a '' Ioo b c = Ioo (a * b) (a * c) := by
  convert image_mul_right_Ioo b c h using 1 <;> simp only [mul_comm _ a]
#align set.image_mul_left_Ioo Set.image_mul_left_ioo

/-- The (pre)image under `inv` of `Ioo 0 a` is `Ioi a⁻¹`. -/
theorem inv_ioo_0_left {a : α} (ha : 0 < a) : (Ioo 0 a)⁻¹ = Ioi a⁻¹ :=
  by
  ext x
  exact
    ⟨fun h => inv_inv x ▸ (inv_lt_inv ha h.1).2 h.2, fun h =>
      ⟨inv_pos.2 <| (inv_pos.2 ha).trans h,
        inv_inv a ▸ (inv_lt_inv ((inv_pos.2 ha).trans h) (inv_pos.2 ha)).2 h⟩⟩
#align set.inv_Ioo_0_left Set.inv_ioo_0_left

theorem inv_ioi {a : α} (ha : 0 < a) : (Ioi a)⁻¹ = Ioo 0 a⁻¹ := by
  rw [inv_eq_iff_inv_eq, inv_Ioo_0_left (inv_pos.2 ha), inv_inv]
#align set.inv_Ioi Set.inv_ioi

theorem image_const_mul_ioi_zero {k : Type _} [LinearOrderedField k] {x : k} (hx : 0 < x) :
    (fun y => x * y) '' Ioi (0 : k) = Ioi 0 := by
  erw [(Units.mk0 x hx.ne').mul_left.image_eq_preimage, preimage_const_mul_Ioi 0 (inv_pos.mpr hx),
    zero_div]
#align set.image_const_mul_Ioi_zero Set.image_const_mul_ioi_zero

/-!
### Images under `x ↦ a * x + b`
-/


@[simp]
theorem image_affine_Icc' {a : α} (h : 0 < a) (b c d : α) :
    (fun x => a * x + b) '' Icc c d = Icc (a * c + b) (a * d + b) :=
  by
  suffices (fun x => x + b) '' ((fun x => a * x) '' Icc c d) = Icc (a * c + b) (a * d + b) by
    rwa [Set.image_image] at this
  rw [image_mul_left_Icc' h, image_add_const_Icc]
#align set.image_affine_Icc' Set.image_affine_Icc'

end LinearOrderedField

end Set

