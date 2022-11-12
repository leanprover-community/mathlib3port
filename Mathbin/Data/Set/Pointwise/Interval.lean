/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Patrick Massot
-/
import Mathbin.Data.Set.Intervals.UnorderedInterval
import Mathbin.Data.Set.Pointwise.Basic
import Mathbin.Algebra.Order.Field.Basic

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

section HasExistsAddOfLe

/-!
The lemmas in this section state that addition maps intervals bijectively. The typeclass
`has_exists_add_of_le` is defined specifically to make them work when combined with
`ordered_cancel_add_comm_monoid`; the lemmas below therefore apply to all
`ordered_add_comm_group`, but also to `ℕ` and `ℝ≥0`, which are not groups.

TODO : move as much as possible in this file to the setting of this weaker typeclass.
-/


variable [OrderedCancelAddCommMonoid α] [HasExistsAddOfLe α] (a b d : α)

theorem Icc_add_bij : BijOn (· + d) (IccCat a b) (IccCat (a + d) (b + d)) := by
  refine'
    ⟨fun _ h => ⟨add_le_add_right h.1 _, add_le_add_right h.2 _⟩, fun _ _ _ _ h => add_right_cancel h, fun _ h => _⟩
  obtain ⟨c, rfl⟩ := exists_add_of_le h.1
  rw [mem_Icc, add_right_comm, add_le_add_iff_right, add_le_add_iff_right] at h
  exact ⟨a + c, h, by rw [add_right_comm]⟩
#align set.Icc_add_bij Set.Icc_add_bij

theorem Ioo_add_bij : BijOn (· + d) (IooCat a b) (IooCat (a + d) (b + d)) := by
  refine'
    ⟨fun _ h => ⟨add_lt_add_right h.1 _, add_lt_add_right h.2 _⟩, fun _ _ _ _ h => add_right_cancel h, fun _ h => _⟩
  obtain ⟨c, rfl⟩ := exists_add_of_le h.1.le
  rw [mem_Ioo, add_right_comm, add_lt_add_iff_right, add_lt_add_iff_right] at h
  exact ⟨a + c, h, by rw [add_right_comm]⟩
#align set.Ioo_add_bij Set.Ioo_add_bij

theorem Ioc_add_bij : BijOn (· + d) (IocCat a b) (IocCat (a + d) (b + d)) := by
  refine'
    ⟨fun _ h => ⟨add_lt_add_right h.1 _, add_le_add_right h.2 _⟩, fun _ _ _ _ h => add_right_cancel h, fun _ h => _⟩
  obtain ⟨c, rfl⟩ := exists_add_of_le h.1.le
  rw [mem_Ioc, add_right_comm, add_lt_add_iff_right, add_le_add_iff_right] at h
  exact ⟨a + c, h, by rw [add_right_comm]⟩
#align set.Ioc_add_bij Set.Ioc_add_bij

theorem Ico_add_bij : BijOn (· + d) (IcoCat a b) (IcoCat (a + d) (b + d)) := by
  refine'
    ⟨fun _ h => ⟨add_le_add_right h.1 _, add_lt_add_right h.2 _⟩, fun _ _ _ _ h => add_right_cancel h, fun _ h => _⟩
  obtain ⟨c, rfl⟩ := exists_add_of_le h.1
  rw [mem_Ico, add_right_comm, add_le_add_iff_right, add_lt_add_iff_right] at h
  exact ⟨a + c, h, by rw [add_right_comm]⟩
#align set.Ico_add_bij Set.Ico_add_bij

theorem Ici_add_bij : BijOn (· + d) (IciCat a) (IciCat (a + d)) := by
  refine' ⟨fun x h => add_le_add_right (mem_Ici.mp h) _, fun _ _ _ _ h => add_right_cancel h, fun _ h => _⟩
  obtain ⟨c, rfl⟩ := exists_add_of_le (mem_Ici.mp h)
  rw [mem_Ici, add_right_comm, add_le_add_iff_right] at h
  exact ⟨a + c, h, by rw [add_right_comm]⟩
#align set.Ici_add_bij Set.Ici_add_bij

theorem Ioi_add_bij : BijOn (· + d) (IoiCat a) (IoiCat (a + d)) := by
  refine' ⟨fun x h => add_lt_add_right (mem_Ioi.mp h) _, fun _ _ _ _ h => add_right_cancel h, fun _ h => _⟩
  obtain ⟨c, rfl⟩ := exists_add_of_le (mem_Ioi.mp h).le
  rw [mem_Ioi, add_right_comm, add_lt_add_iff_right] at h
  exact ⟨a + c, h, by rw [add_right_comm]⟩
#align set.Ioi_add_bij Set.Ioi_add_bij

end HasExistsAddOfLe

section OrderedAddCommGroup

variable [OrderedAddCommGroup α] (a b c : α)

/-!
### Preimages under `x ↦ a + x`
-/


@[simp]
theorem preimage_const_add_Ici : (fun x => a + x) ⁻¹' IciCat b = IciCat (b - a) :=
  ext fun x => sub_le_iff_le_add'.symm
#align set.preimage_const_add_Ici Set.preimage_const_add_Ici

@[simp]
theorem preimage_const_add_Ioi : (fun x => a + x) ⁻¹' IoiCat b = IoiCat (b - a) :=
  ext fun x => sub_lt_iff_lt_add'.symm
#align set.preimage_const_add_Ioi Set.preimage_const_add_Ioi

@[simp]
theorem preimage_const_add_Iic : (fun x => a + x) ⁻¹' IicCat b = IicCat (b - a) :=
  ext fun x => le_sub_iff_add_le'.symm
#align set.preimage_const_add_Iic Set.preimage_const_add_Iic

@[simp]
theorem preimage_const_add_Iio : (fun x => a + x) ⁻¹' IioCat b = IioCat (b - a) :=
  ext fun x => lt_sub_iff_add_lt'.symm
#align set.preimage_const_add_Iio Set.preimage_const_add_Iio

@[simp]
theorem preimage_const_add_Icc : (fun x => a + x) ⁻¹' IccCat b c = IccCat (b - a) (c - a) := by simp [← Ici_inter_Iic]
#align set.preimage_const_add_Icc Set.preimage_const_add_Icc

@[simp]
theorem preimage_const_add_Ico : (fun x => a + x) ⁻¹' IcoCat b c = IcoCat (b - a) (c - a) := by simp [← Ici_inter_Iio]
#align set.preimage_const_add_Ico Set.preimage_const_add_Ico

@[simp]
theorem preimage_const_add_Ioc : (fun x => a + x) ⁻¹' IocCat b c = IocCat (b - a) (c - a) := by simp [← Ioi_inter_Iic]
#align set.preimage_const_add_Ioc Set.preimage_const_add_Ioc

@[simp]
theorem preimage_const_add_Ioo : (fun x => a + x) ⁻¹' IooCat b c = IooCat (b - a) (c - a) := by simp [← Ioi_inter_Iio]
#align set.preimage_const_add_Ioo Set.preimage_const_add_Ioo

/-!
### Preimages under `x ↦ x + a`
-/


@[simp]
theorem preimage_add_const_Ici : (fun x => x + a) ⁻¹' IciCat b = IciCat (b - a) :=
  ext fun x => sub_le_iff_le_add.symm
#align set.preimage_add_const_Ici Set.preimage_add_const_Ici

@[simp]
theorem preimage_add_const_Ioi : (fun x => x + a) ⁻¹' IoiCat b = IoiCat (b - a) :=
  ext fun x => sub_lt_iff_lt_add.symm
#align set.preimage_add_const_Ioi Set.preimage_add_const_Ioi

@[simp]
theorem preimage_add_const_Iic : (fun x => x + a) ⁻¹' IicCat b = IicCat (b - a) :=
  ext fun x => le_sub_iff_add_le.symm
#align set.preimage_add_const_Iic Set.preimage_add_const_Iic

@[simp]
theorem preimage_add_const_Iio : (fun x => x + a) ⁻¹' IioCat b = IioCat (b - a) :=
  ext fun x => lt_sub_iff_add_lt.symm
#align set.preimage_add_const_Iio Set.preimage_add_const_Iio

@[simp]
theorem preimage_add_const_Icc : (fun x => x + a) ⁻¹' IccCat b c = IccCat (b - a) (c - a) := by simp [← Ici_inter_Iic]
#align set.preimage_add_const_Icc Set.preimage_add_const_Icc

@[simp]
theorem preimage_add_const_Ico : (fun x => x + a) ⁻¹' IcoCat b c = IcoCat (b - a) (c - a) := by simp [← Ici_inter_Iio]
#align set.preimage_add_const_Ico Set.preimage_add_const_Ico

@[simp]
theorem preimage_add_const_Ioc : (fun x => x + a) ⁻¹' IocCat b c = IocCat (b - a) (c - a) := by simp [← Ioi_inter_Iic]
#align set.preimage_add_const_Ioc Set.preimage_add_const_Ioc

@[simp]
theorem preimage_add_const_Ioo : (fun x => x + a) ⁻¹' IooCat b c = IooCat (b - a) (c - a) := by simp [← Ioi_inter_Iio]
#align set.preimage_add_const_Ioo Set.preimage_add_const_Ioo

/-!
### Preimages under `x ↦ -x`
-/


@[simp]
theorem preimage_neg_Ici : -IciCat a = IicCat (-a) :=
  ext fun x => le_neg
#align set.preimage_neg_Ici Set.preimage_neg_Ici

@[simp]
theorem preimage_neg_Iic : -IicCat a = IciCat (-a) :=
  ext fun x => neg_le
#align set.preimage_neg_Iic Set.preimage_neg_Iic

@[simp]
theorem preimage_neg_Ioi : -IoiCat a = IioCat (-a) :=
  ext fun x => lt_neg
#align set.preimage_neg_Ioi Set.preimage_neg_Ioi

@[simp]
theorem preimage_neg_Iio : -IioCat a = IoiCat (-a) :=
  ext fun x => neg_lt
#align set.preimage_neg_Iio Set.preimage_neg_Iio

@[simp]
theorem preimage_neg_Icc : -IccCat a b = IccCat (-b) (-a) := by simp [← Ici_inter_Iic, inter_comm]
#align set.preimage_neg_Icc Set.preimage_neg_Icc

@[simp]
theorem preimage_neg_Ico : -IcoCat a b = IocCat (-b) (-a) := by simp [← Ici_inter_Iio, ← Ioi_inter_Iic, inter_comm]
#align set.preimage_neg_Ico Set.preimage_neg_Ico

@[simp]
theorem preimage_neg_Ioc : -IocCat a b = IcoCat (-b) (-a) := by simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]
#align set.preimage_neg_Ioc Set.preimage_neg_Ioc

@[simp]
theorem preimage_neg_Ioo : -IooCat a b = IooCat (-b) (-a) := by simp [← Ioi_inter_Iio, inter_comm]
#align set.preimage_neg_Ioo Set.preimage_neg_Ioo

/-!
### Preimages under `x ↦ x - a`
-/


@[simp]
theorem preimage_sub_const_Ici : (fun x => x - a) ⁻¹' IciCat b = IciCat (b + a) := by simp [sub_eq_add_neg]
#align set.preimage_sub_const_Ici Set.preimage_sub_const_Ici

@[simp]
theorem preimage_sub_const_Ioi : (fun x => x - a) ⁻¹' IoiCat b = IoiCat (b + a) := by simp [sub_eq_add_neg]
#align set.preimage_sub_const_Ioi Set.preimage_sub_const_Ioi

@[simp]
theorem preimage_sub_const_Iic : (fun x => x - a) ⁻¹' IicCat b = IicCat (b + a) := by simp [sub_eq_add_neg]
#align set.preimage_sub_const_Iic Set.preimage_sub_const_Iic

@[simp]
theorem preimage_sub_const_Iio : (fun x => x - a) ⁻¹' IioCat b = IioCat (b + a) := by simp [sub_eq_add_neg]
#align set.preimage_sub_const_Iio Set.preimage_sub_const_Iio

@[simp]
theorem preimage_sub_const_Icc : (fun x => x - a) ⁻¹' IccCat b c = IccCat (b + a) (c + a) := by simp [sub_eq_add_neg]
#align set.preimage_sub_const_Icc Set.preimage_sub_const_Icc

@[simp]
theorem preimage_sub_const_Ico : (fun x => x - a) ⁻¹' IcoCat b c = IcoCat (b + a) (c + a) := by simp [sub_eq_add_neg]
#align set.preimage_sub_const_Ico Set.preimage_sub_const_Ico

@[simp]
theorem preimage_sub_const_Ioc : (fun x => x - a) ⁻¹' IocCat b c = IocCat (b + a) (c + a) := by simp [sub_eq_add_neg]
#align set.preimage_sub_const_Ioc Set.preimage_sub_const_Ioc

@[simp]
theorem preimage_sub_const_Ioo : (fun x => x - a) ⁻¹' IooCat b c = IooCat (b + a) (c + a) := by simp [sub_eq_add_neg]
#align set.preimage_sub_const_Ioo Set.preimage_sub_const_Ioo

/-!
### Preimages under `x ↦ a - x`
-/


@[simp]
theorem preimage_const_sub_Ici : (fun x => a - x) ⁻¹' IciCat b = IicCat (a - b) :=
  ext fun x => le_sub_comm
#align set.preimage_const_sub_Ici Set.preimage_const_sub_Ici

@[simp]
theorem preimage_const_sub_Iic : (fun x => a - x) ⁻¹' IicCat b = IciCat (a - b) :=
  ext fun x => sub_le_comm
#align set.preimage_const_sub_Iic Set.preimage_const_sub_Iic

@[simp]
theorem preimage_const_sub_Ioi : (fun x => a - x) ⁻¹' IoiCat b = IioCat (a - b) :=
  ext fun x => lt_sub_comm
#align set.preimage_const_sub_Ioi Set.preimage_const_sub_Ioi

@[simp]
theorem preimage_const_sub_Iio : (fun x => a - x) ⁻¹' IioCat b = IoiCat (a - b) :=
  ext fun x => sub_lt_comm
#align set.preimage_const_sub_Iio Set.preimage_const_sub_Iio

@[simp]
theorem preimage_const_sub_Icc : (fun x => a - x) ⁻¹' IccCat b c = IccCat (a - c) (a - b) := by
  simp [← Ici_inter_Iic, inter_comm]
#align set.preimage_const_sub_Icc Set.preimage_const_sub_Icc

@[simp]
theorem preimage_const_sub_Ico : (fun x => a - x) ⁻¹' IcoCat b c = IocCat (a - c) (a - b) := by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]
#align set.preimage_const_sub_Ico Set.preimage_const_sub_Ico

@[simp]
theorem preimage_const_sub_Ioc : (fun x => a - x) ⁻¹' IocCat b c = IcoCat (a - c) (a - b) := by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]
#align set.preimage_const_sub_Ioc Set.preimage_const_sub_Ioc

@[simp]
theorem preimage_const_sub_Ioo : (fun x => a - x) ⁻¹' IooCat b c = IooCat (a - c) (a - b) := by
  simp [← Ioi_inter_Iio, inter_comm]
#align set.preimage_const_sub_Ioo Set.preimage_const_sub_Ioo

/-!
### Images under `x ↦ a + x`
-/


@[simp]
theorem image_const_add_Ici : (fun x => a + x) '' IciCat b = IciCat (a + b) := by simp [add_comm]
#align set.image_const_add_Ici Set.image_const_add_Ici

@[simp]
theorem image_const_add_Iic : (fun x => a + x) '' IicCat b = IicCat (a + b) := by simp [add_comm]
#align set.image_const_add_Iic Set.image_const_add_Iic

@[simp]
theorem image_const_add_Iio : (fun x => a + x) '' IioCat b = IioCat (a + b) := by simp [add_comm]
#align set.image_const_add_Iio Set.image_const_add_Iio

@[simp]
theorem image_const_add_Ioi : (fun x => a + x) '' IoiCat b = IoiCat (a + b) := by simp [add_comm]
#align set.image_const_add_Ioi Set.image_const_add_Ioi

@[simp]
theorem image_const_add_Icc : (fun x => a + x) '' IccCat b c = IccCat (a + b) (a + c) := by simp [add_comm]
#align set.image_const_add_Icc Set.image_const_add_Icc

@[simp]
theorem image_const_add_Ico : (fun x => a + x) '' IcoCat b c = IcoCat (a + b) (a + c) := by simp [add_comm]
#align set.image_const_add_Ico Set.image_const_add_Ico

@[simp]
theorem image_const_add_Ioc : (fun x => a + x) '' IocCat b c = IocCat (a + b) (a + c) := by simp [add_comm]
#align set.image_const_add_Ioc Set.image_const_add_Ioc

@[simp]
theorem image_const_add_Ioo : (fun x => a + x) '' IooCat b c = IooCat (a + b) (a + c) := by simp [add_comm]
#align set.image_const_add_Ioo Set.image_const_add_Ioo

/-!
### Images under `x ↦ x + a`
-/


@[simp]
theorem image_add_const_Ici : (fun x => x + a) '' IciCat b = IciCat (b + a) := by simp
#align set.image_add_const_Ici Set.image_add_const_Ici

@[simp]
theorem image_add_const_Iic : (fun x => x + a) '' IicCat b = IicCat (b + a) := by simp
#align set.image_add_const_Iic Set.image_add_const_Iic

@[simp]
theorem image_add_const_Iio : (fun x => x + a) '' IioCat b = IioCat (b + a) := by simp
#align set.image_add_const_Iio Set.image_add_const_Iio

@[simp]
theorem image_add_const_Ioi : (fun x => x + a) '' IoiCat b = IoiCat (b + a) := by simp
#align set.image_add_const_Ioi Set.image_add_const_Ioi

@[simp]
theorem image_add_const_Icc : (fun x => x + a) '' IccCat b c = IccCat (b + a) (c + a) := by simp
#align set.image_add_const_Icc Set.image_add_const_Icc

@[simp]
theorem image_add_const_Ico : (fun x => x + a) '' IcoCat b c = IcoCat (b + a) (c + a) := by simp
#align set.image_add_const_Ico Set.image_add_const_Ico

@[simp]
theorem image_add_const_Ioc : (fun x => x + a) '' IocCat b c = IocCat (b + a) (c + a) := by simp
#align set.image_add_const_Ioc Set.image_add_const_Ioc

@[simp]
theorem image_add_const_Ioo : (fun x => x + a) '' IooCat b c = IooCat (b + a) (c + a) := by simp
#align set.image_add_const_Ioo Set.image_add_const_Ioo

/-!
### Images under `x ↦ -x`
-/


theorem image_neg_Ici : Neg.neg '' IciCat a = IicCat (-a) := by simp
#align set.image_neg_Ici Set.image_neg_Ici

theorem image_neg_Iic : Neg.neg '' IicCat a = IciCat (-a) := by simp
#align set.image_neg_Iic Set.image_neg_Iic

theorem image_neg_Ioi : Neg.neg '' IoiCat a = IioCat (-a) := by simp
#align set.image_neg_Ioi Set.image_neg_Ioi

theorem image_neg_Iio : Neg.neg '' IioCat a = IoiCat (-a) := by simp
#align set.image_neg_Iio Set.image_neg_Iio

theorem image_neg_Icc : Neg.neg '' IccCat a b = IccCat (-b) (-a) := by simp
#align set.image_neg_Icc Set.image_neg_Icc

theorem image_neg_Ico : Neg.neg '' IcoCat a b = IocCat (-b) (-a) := by simp
#align set.image_neg_Ico Set.image_neg_Ico

theorem image_neg_Ioc : Neg.neg '' IocCat a b = IcoCat (-b) (-a) := by simp
#align set.image_neg_Ioc Set.image_neg_Ioc

theorem image_neg_Ioo : Neg.neg '' IooCat a b = IooCat (-b) (-a) := by simp
#align set.image_neg_Ioo Set.image_neg_Ioo

/-!
### Images under `x ↦ a - x`
-/


@[simp]
theorem image_const_sub_Ici : (fun x => a - x) '' IciCat b = IicCat (a - b) := by
  simp [sub_eq_add_neg, image_comp (fun x => a + x) fun x => -x]
#align set.image_const_sub_Ici Set.image_const_sub_Ici

@[simp]
theorem image_const_sub_Iic : (fun x => a - x) '' IicCat b = IciCat (a - b) := by
  simp [sub_eq_add_neg, image_comp (fun x => a + x) fun x => -x]
#align set.image_const_sub_Iic Set.image_const_sub_Iic

@[simp]
theorem image_const_sub_Ioi : (fun x => a - x) '' IoiCat b = IioCat (a - b) := by
  simp [sub_eq_add_neg, image_comp (fun x => a + x) fun x => -x]
#align set.image_const_sub_Ioi Set.image_const_sub_Ioi

@[simp]
theorem image_const_sub_Iio : (fun x => a - x) '' IioCat b = IoiCat (a - b) := by
  simp [sub_eq_add_neg, image_comp (fun x => a + x) fun x => -x]
#align set.image_const_sub_Iio Set.image_const_sub_Iio

@[simp]
theorem image_const_sub_Icc : (fun x => a - x) '' IccCat b c = IccCat (a - c) (a - b) := by
  simp [sub_eq_add_neg, image_comp (fun x => a + x) fun x => -x]
#align set.image_const_sub_Icc Set.image_const_sub_Icc

@[simp]
theorem image_const_sub_Ico : (fun x => a - x) '' IcoCat b c = IocCat (a - c) (a - b) := by
  simp [sub_eq_add_neg, image_comp (fun x => a + x) fun x => -x]
#align set.image_const_sub_Ico Set.image_const_sub_Ico

@[simp]
theorem image_const_sub_Ioc : (fun x => a - x) '' IocCat b c = IcoCat (a - c) (a - b) := by
  simp [sub_eq_add_neg, image_comp (fun x => a + x) fun x => -x]
#align set.image_const_sub_Ioc Set.image_const_sub_Ioc

@[simp]
theorem image_const_sub_Ioo : (fun x => a - x) '' IooCat b c = IooCat (a - c) (a - b) := by
  simp [sub_eq_add_neg, image_comp (fun x => a + x) fun x => -x]
#align set.image_const_sub_Ioo Set.image_const_sub_Ioo

/-!
### Images under `x ↦ x - a`
-/


@[simp]
theorem image_sub_const_Ici : (fun x => x - a) '' IciCat b = IciCat (b - a) := by simp [sub_eq_neg_add]
#align set.image_sub_const_Ici Set.image_sub_const_Ici

@[simp]
theorem image_sub_const_Iic : (fun x => x - a) '' IicCat b = IicCat (b - a) := by simp [sub_eq_neg_add]
#align set.image_sub_const_Iic Set.image_sub_const_Iic

@[simp]
theorem image_sub_const_Ioi : (fun x => x - a) '' IoiCat b = IoiCat (b - a) := by simp [sub_eq_neg_add]
#align set.image_sub_const_Ioi Set.image_sub_const_Ioi

@[simp]
theorem image_sub_const_Iio : (fun x => x - a) '' IioCat b = IioCat (b - a) := by simp [sub_eq_neg_add]
#align set.image_sub_const_Iio Set.image_sub_const_Iio

@[simp]
theorem image_sub_const_Icc : (fun x => x - a) '' IccCat b c = IccCat (b - a) (c - a) := by simp [sub_eq_neg_add]
#align set.image_sub_const_Icc Set.image_sub_const_Icc

@[simp]
theorem image_sub_const_Ico : (fun x => x - a) '' IcoCat b c = IcoCat (b - a) (c - a) := by simp [sub_eq_neg_add]
#align set.image_sub_const_Ico Set.image_sub_const_Ico

@[simp]
theorem image_sub_const_Ioc : (fun x => x - a) '' IocCat b c = IocCat (b - a) (c - a) := by simp [sub_eq_neg_add]
#align set.image_sub_const_Ioc Set.image_sub_const_Ioc

@[simp]
theorem image_sub_const_Ioo : (fun x => x - a) '' IooCat b c = IooCat (b - a) (c - a) := by simp [sub_eq_neg_add]
#align set.image_sub_const_Ioo Set.image_sub_const_Ioo

/-!
### Bijections
-/


theorem Iic_add_bij : BijOn (· + a) (IicCat b) (IicCat (b + a)) := by
  refine' ⟨fun x h => add_le_add_right (mem_Iic.mp h) _, fun _ _ _ _ h => add_right_cancel h, fun _ h => _⟩
  simpa [add_comm a] using h
#align set.Iic_add_bij Set.Iic_add_bij

theorem Iio_add_bij : BijOn (· + a) (IioCat b) (IioCat (b + a)) := by
  refine' ⟨fun x h => add_lt_add_right (mem_Iio.mp h) _, fun _ _ _ _ h => add_right_cancel h, fun _ h => _⟩
  simpa [add_comm a] using h
#align set.Iio_add_bij Set.Iio_add_bij

end OrderedAddCommGroup

section LinearOrderedAddCommGroup

variable [LinearOrderedAddCommGroup α] (a b c d : α)

@[simp]
theorem preimage_const_add_interval : (fun x => a + x) ⁻¹' [b, c] = [b - a, c - a] := by
  simp only [interval, preimage_const_add_Icc, min_sub_sub_right, max_sub_sub_right]
#align set.preimage_const_add_interval Set.preimage_const_add_interval

@[simp]
theorem preimage_add_const_interval : (fun x => x + a) ⁻¹' [b, c] = [b - a, c - a] := by
  simpa only [add_comm] using preimage_const_add_interval a b c
#align set.preimage_add_const_interval Set.preimage_add_const_interval

@[simp]
theorem preimage_neg_interval : -[a, b] = [-a, -b] := by
  simp only [interval, preimage_neg_Icc, min_neg_neg, max_neg_neg]
#align set.preimage_neg_interval Set.preimage_neg_interval

@[simp]
theorem preimage_sub_const_interval : (fun x => x - a) ⁻¹' [b, c] = [b + a, c + a] := by simp [sub_eq_add_neg]
#align set.preimage_sub_const_interval Set.preimage_sub_const_interval

@[simp]
theorem preimage_const_sub_interval : (fun x => a - x) ⁻¹' [b, c] = [a - b, a - c] := by
  rw [interval, interval, preimage_const_sub_Icc]
  simp only [sub_eq_add_neg, min_add_add_left, max_add_add_left, min_neg_neg, max_neg_neg]
#align set.preimage_const_sub_interval Set.preimage_const_sub_interval

@[simp]
theorem image_const_add_interval : (fun x => a + x) '' [b, c] = [a + b, a + c] := by simp [add_comm]
#align set.image_const_add_interval Set.image_const_add_interval

@[simp]
theorem image_add_const_interval : (fun x => x + a) '' [b, c] = [b + a, c + a] := by simp
#align set.image_add_const_interval Set.image_add_const_interval

@[simp]
theorem image_const_sub_interval : (fun x => a - x) '' [b, c] = [a - b, a - c] := by
  simp [sub_eq_add_neg, image_comp (fun x => a + x) fun x => -x]
#align set.image_const_sub_interval Set.image_const_sub_interval

@[simp]
theorem image_sub_const_interval : (fun x => x - a) '' [b, c] = [b - a, c - a] := by simp [sub_eq_add_neg, add_comm]
#align set.image_sub_const_interval Set.image_sub_const_interval

theorem image_neg_interval : Neg.neg '' [a, b] = [-a, -b] := by simp
#align set.image_neg_interval Set.image_neg_interval

variable {a b c d}

/-- If `[c, d]` is a subinterval of `[a, b]`, then the distance between `c` and `d` is less than or
equal to that of `a` and `b` -/
theorem abs_sub_le_of_subinterval (h : [c, d] ⊆ [a, b]) : |d - c| ≤ |b - a| := by
  rw [← max_sub_min_eq_abs, ← max_sub_min_eq_abs]
  rw [interval_subset_interval_iff_le] at h
  exact sub_le_sub h.2 h.1
#align set.abs_sub_le_of_subinterval Set.abs_sub_le_of_subinterval

/-- If `c ∈ [a, b]`, then the distance between `a` and `c` is less than or equal to
that of `a` and `b`  -/
theorem abs_sub_left_of_mem_interval (h : c ∈ [a, b]) : |c - a| ≤ |b - a| :=
  abs_sub_le_of_subinterval (interval_subset_interval_left h)
#align set.abs_sub_left_of_mem_interval Set.abs_sub_left_of_mem_interval

/-- If `x ∈ [a, b]`, then the distance between `c` and `b` is less than or equal to
that of `a` and `b`  -/
theorem abs_sub_right_of_mem_interval (h : c ∈ [a, b]) : |b - c| ≤ |b - a| :=
  abs_sub_le_of_subinterval (interval_subset_interval_right h)
#align set.abs_sub_right_of_mem_interval Set.abs_sub_right_of_mem_interval

end LinearOrderedAddCommGroup

/-!
### Multiplication and inverse in a field
-/


section LinearOrderedField

variable [LinearOrderedField α] {a : α}

@[simp]
theorem preimage_mul_const_Iio (a : α) {c : α} (h : 0 < c) : (fun x => x * c) ⁻¹' IioCat a = IioCat (a / c) :=
  ext fun x => (lt_div_iff h).symm
#align set.preimage_mul_const_Iio Set.preimage_mul_const_Iio

@[simp]
theorem preimage_mul_const_Ioi (a : α) {c : α} (h : 0 < c) : (fun x => x * c) ⁻¹' IoiCat a = IoiCat (a / c) :=
  ext fun x => (div_lt_iff h).symm
#align set.preimage_mul_const_Ioi Set.preimage_mul_const_Ioi

@[simp]
theorem preimage_mul_const_Iic (a : α) {c : α} (h : 0 < c) : (fun x => x * c) ⁻¹' IicCat a = IicCat (a / c) :=
  ext fun x => (le_div_iff h).symm
#align set.preimage_mul_const_Iic Set.preimage_mul_const_Iic

@[simp]
theorem preimage_mul_const_Ici (a : α) {c : α} (h : 0 < c) : (fun x => x * c) ⁻¹' IciCat a = IciCat (a / c) :=
  ext fun x => (div_le_iff h).symm
#align set.preimage_mul_const_Ici Set.preimage_mul_const_Ici

@[simp]
theorem preimage_mul_const_Ioo (a b : α) {c : α} (h : 0 < c) :
    (fun x => x * c) ⁻¹' IooCat a b = IooCat (a / c) (b / c) := by simp [← Ioi_inter_Iio, h]
#align set.preimage_mul_const_Ioo Set.preimage_mul_const_Ioo

@[simp]
theorem preimage_mul_const_Ioc (a b : α) {c : α} (h : 0 < c) :
    (fun x => x * c) ⁻¹' IocCat a b = IocCat (a / c) (b / c) := by simp [← Ioi_inter_Iic, h]
#align set.preimage_mul_const_Ioc Set.preimage_mul_const_Ioc

@[simp]
theorem preimage_mul_const_Ico (a b : α) {c : α} (h : 0 < c) :
    (fun x => x * c) ⁻¹' IcoCat a b = IcoCat (a / c) (b / c) := by simp [← Ici_inter_Iio, h]
#align set.preimage_mul_const_Ico Set.preimage_mul_const_Ico

@[simp]
theorem preimage_mul_const_Icc (a b : α) {c : α} (h : 0 < c) :
    (fun x => x * c) ⁻¹' IccCat a b = IccCat (a / c) (b / c) := by simp [← Ici_inter_Iic, h]
#align set.preimage_mul_const_Icc Set.preimage_mul_const_Icc

@[simp]
theorem preimage_mul_const_Iio_of_neg (a : α) {c : α} (h : c < 0) : (fun x => x * c) ⁻¹' IioCat a = IoiCat (a / c) :=
  ext fun x => (div_lt_iff_of_neg h).symm
#align set.preimage_mul_const_Iio_of_neg Set.preimage_mul_const_Iio_of_neg

@[simp]
theorem preimage_mul_const_Ioi_of_neg (a : α) {c : α} (h : c < 0) : (fun x => x * c) ⁻¹' IoiCat a = IioCat (a / c) :=
  ext fun x => (lt_div_iff_of_neg h).symm
#align set.preimage_mul_const_Ioi_of_neg Set.preimage_mul_const_Ioi_of_neg

@[simp]
theorem preimage_mul_const_Iic_of_neg (a : α) {c : α} (h : c < 0) : (fun x => x * c) ⁻¹' IicCat a = IciCat (a / c) :=
  ext fun x => (div_le_iff_of_neg h).symm
#align set.preimage_mul_const_Iic_of_neg Set.preimage_mul_const_Iic_of_neg

@[simp]
theorem preimage_mul_const_Ici_of_neg (a : α) {c : α} (h : c < 0) : (fun x => x * c) ⁻¹' IciCat a = IicCat (a / c) :=
  ext fun x => (le_div_iff_of_neg h).symm
#align set.preimage_mul_const_Ici_of_neg Set.preimage_mul_const_Ici_of_neg

@[simp]
theorem preimage_mul_const_Ioo_of_neg (a b : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' IooCat a b = IooCat (b / c) (a / c) := by simp [← Ioi_inter_Iio, h, inter_comm]
#align set.preimage_mul_const_Ioo_of_neg Set.preimage_mul_const_Ioo_of_neg

@[simp]
theorem preimage_mul_const_Ioc_of_neg (a b : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' IocCat a b = IcoCat (b / c) (a / c) := by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, h, inter_comm]
#align set.preimage_mul_const_Ioc_of_neg Set.preimage_mul_const_Ioc_of_neg

@[simp]
theorem preimage_mul_const_Ico_of_neg (a b : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' IcoCat a b = IocCat (b / c) (a / c) := by
  simp [← Ici_inter_Iio, ← Ioi_inter_Iic, h, inter_comm]
#align set.preimage_mul_const_Ico_of_neg Set.preimage_mul_const_Ico_of_neg

@[simp]
theorem preimage_mul_const_Icc_of_neg (a b : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' IccCat a b = IccCat (b / c) (a / c) := by simp [← Ici_inter_Iic, h, inter_comm]
#align set.preimage_mul_const_Icc_of_neg Set.preimage_mul_const_Icc_of_neg

@[simp]
theorem preimage_const_mul_Iio (a : α) {c : α} (h : 0 < c) : (· * ·) c ⁻¹' IioCat a = IioCat (a / c) :=
  ext fun x => (lt_div_iff' h).symm
#align set.preimage_const_mul_Iio Set.preimage_const_mul_Iio

@[simp]
theorem preimage_const_mul_Ioi (a : α) {c : α} (h : 0 < c) : (· * ·) c ⁻¹' IoiCat a = IoiCat (a / c) :=
  ext fun x => (div_lt_iff' h).symm
#align set.preimage_const_mul_Ioi Set.preimage_const_mul_Ioi

@[simp]
theorem preimage_const_mul_Iic (a : α) {c : α} (h : 0 < c) : (· * ·) c ⁻¹' IicCat a = IicCat (a / c) :=
  ext fun x => (le_div_iff' h).symm
#align set.preimage_const_mul_Iic Set.preimage_const_mul_Iic

@[simp]
theorem preimage_const_mul_Ici (a : α) {c : α} (h : 0 < c) : (· * ·) c ⁻¹' IciCat a = IciCat (a / c) :=
  ext fun x => (div_le_iff' h).symm
#align set.preimage_const_mul_Ici Set.preimage_const_mul_Ici

@[simp]
theorem preimage_const_mul_Ioo (a b : α) {c : α} (h : 0 < c) : (· * ·) c ⁻¹' IooCat a b = IooCat (a / c) (b / c) := by
  simp [← Ioi_inter_Iio, h]
#align set.preimage_const_mul_Ioo Set.preimage_const_mul_Ioo

@[simp]
theorem preimage_const_mul_Ioc (a b : α) {c : α} (h : 0 < c) : (· * ·) c ⁻¹' IocCat a b = IocCat (a / c) (b / c) := by
  simp [← Ioi_inter_Iic, h]
#align set.preimage_const_mul_Ioc Set.preimage_const_mul_Ioc

@[simp]
theorem preimage_const_mul_Ico (a b : α) {c : α} (h : 0 < c) : (· * ·) c ⁻¹' IcoCat a b = IcoCat (a / c) (b / c) := by
  simp [← Ici_inter_Iio, h]
#align set.preimage_const_mul_Ico Set.preimage_const_mul_Ico

@[simp]
theorem preimage_const_mul_Icc (a b : α) {c : α} (h : 0 < c) : (· * ·) c ⁻¹' IccCat a b = IccCat (a / c) (b / c) := by
  simp [← Ici_inter_Iic, h]
#align set.preimage_const_mul_Icc Set.preimage_const_mul_Icc

@[simp]
theorem preimage_const_mul_Iio_of_neg (a : α) {c : α} (h : c < 0) : (· * ·) c ⁻¹' IioCat a = IoiCat (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Iio_of_neg a h
#align set.preimage_const_mul_Iio_of_neg Set.preimage_const_mul_Iio_of_neg

@[simp]
theorem preimage_const_mul_Ioi_of_neg (a : α) {c : α} (h : c < 0) : (· * ·) c ⁻¹' IoiCat a = IioCat (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ioi_of_neg a h
#align set.preimage_const_mul_Ioi_of_neg Set.preimage_const_mul_Ioi_of_neg

@[simp]
theorem preimage_const_mul_Iic_of_neg (a : α) {c : α} (h : c < 0) : (· * ·) c ⁻¹' IicCat a = IciCat (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Iic_of_neg a h
#align set.preimage_const_mul_Iic_of_neg Set.preimage_const_mul_Iic_of_neg

@[simp]
theorem preimage_const_mul_Ici_of_neg (a : α) {c : α} (h : c < 0) : (· * ·) c ⁻¹' IciCat a = IicCat (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ici_of_neg a h
#align set.preimage_const_mul_Ici_of_neg Set.preimage_const_mul_Ici_of_neg

@[simp]
theorem preimage_const_mul_Ioo_of_neg (a b : α) {c : α} (h : c < 0) :
    (· * ·) c ⁻¹' IooCat a b = IooCat (b / c) (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ioo_of_neg a b h
#align set.preimage_const_mul_Ioo_of_neg Set.preimage_const_mul_Ioo_of_neg

@[simp]
theorem preimage_const_mul_Ioc_of_neg (a b : α) {c : α} (h : c < 0) :
    (· * ·) c ⁻¹' IocCat a b = IcoCat (b / c) (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ioc_of_neg a b h
#align set.preimage_const_mul_Ioc_of_neg Set.preimage_const_mul_Ioc_of_neg

@[simp]
theorem preimage_const_mul_Ico_of_neg (a b : α) {c : α} (h : c < 0) :
    (· * ·) c ⁻¹' IcoCat a b = IocCat (b / c) (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ico_of_neg a b h
#align set.preimage_const_mul_Ico_of_neg Set.preimage_const_mul_Ico_of_neg

@[simp]
theorem preimage_const_mul_Icc_of_neg (a b : α) {c : α} (h : c < 0) :
    (· * ·) c ⁻¹' IccCat a b = IccCat (b / c) (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Icc_of_neg a b h
#align set.preimage_const_mul_Icc_of_neg Set.preimage_const_mul_Icc_of_neg

@[simp]
theorem preimage_mul_const_interval (ha : a ≠ 0) (b c : α) : (fun x => x * a) ⁻¹' [b, c] = [b / a, c / a] :=
  (lt_or_gt_of_ne ha).elim
    (fun ha => by simp [interval, ha, ha.le, min_div_div_right_of_nonpos, max_div_div_right_of_nonpos])
    fun ha : 0 < a => by simp [interval, ha, ha.le, min_div_div_right, max_div_div_right]
#align set.preimage_mul_const_interval Set.preimage_mul_const_interval

@[simp]
theorem preimage_const_mul_interval (ha : a ≠ 0) (b c : α) : (fun x => a * x) ⁻¹' [b, c] = [b / a, c / a] := by
  simp only [← preimage_mul_const_interval ha, mul_comm]
#align set.preimage_const_mul_interval Set.preimage_const_mul_interval

@[simp]
theorem preimage_div_const_interval (ha : a ≠ 0) (b c : α) : (fun x => x / a) ⁻¹' [b, c] = [b * a, c * a] := by
  simp only [div_eq_mul_inv, preimage_mul_const_interval (inv_ne_zero ha), inv_inv]
#align set.preimage_div_const_interval Set.preimage_div_const_interval

@[simp]
theorem image_mul_const_interval (a b c : α) : (fun x => x * a) '' [b, c] = [b * a, c * a] :=
  if ha : a = 0 then by simp [ha]
  else
    calc
      (fun x => x * a) '' [b, c] = (fun x => x * a⁻¹) ⁻¹' [b, c] := (Units.mk0 a ha).mul_right.image_eq_preimage _
      _ = (fun x => x / a) ⁻¹' [b, c] := by simp only [div_eq_mul_inv]
      _ = [b * a, c * a] := preimage_div_const_interval ha _ _
      
#align set.image_mul_const_interval Set.image_mul_const_interval

@[simp]
theorem image_const_mul_interval (a b c : α) : (fun x => a * x) '' [b, c] = [a * b, a * c] := by
  simpa only [mul_comm] using image_mul_const_interval a b c
#align set.image_const_mul_interval Set.image_const_mul_interval

@[simp]
theorem image_div_const_interval (a b c : α) : (fun x => x / a) '' [b, c] = [b / a, c / a] := by
  simp only [div_eq_mul_inv, image_mul_const_interval]
#align set.image_div_const_interval Set.image_div_const_interval

theorem image_mul_right_Icc' (a b : α) {c : α} (h : 0 < c) : (fun x => x * c) '' IccCat a b = IccCat (a * c) (b * c) :=
  ((Units.mk0 c h.ne').mul_right.image_eq_preimage _).trans (by simp [h, division_def])
#align set.image_mul_right_Icc' Set.image_mul_right_Icc'

theorem image_mul_right_Icc {a b c : α} (hab : a ≤ b) (hc : 0 ≤ c) :
    (fun x => x * c) '' IccCat a b = IccCat (a * c) (b * c) := by
  cases eq_or_lt_of_le hc
  · subst c
    simp [(nonempty_Icc.2 hab).image_const]
    
  exact image_mul_right_Icc' a b ‹0 < c›
#align set.image_mul_right_Icc Set.image_mul_right_Icc

theorem image_mul_left_Icc' {a : α} (h : 0 < a) (b c : α) : (· * ·) a '' IccCat b c = IccCat (a * b) (a * c) := by
  convert image_mul_right_Icc' b c h using 1 <;> simp only [mul_comm _ a]
#align set.image_mul_left_Icc' Set.image_mul_left_Icc'

theorem image_mul_left_Icc {a b c : α} (ha : 0 ≤ a) (hbc : b ≤ c) : (· * ·) a '' IccCat b c = IccCat (a * b) (a * c) :=
  by convert image_mul_right_Icc hbc ha using 1 <;> simp only [mul_comm _ a]
#align set.image_mul_left_Icc Set.image_mul_left_Icc

theorem image_mul_right_Ioo (a b : α) {c : α} (h : 0 < c) : (fun x => x * c) '' IooCat a b = IooCat (a * c) (b * c) :=
  ((Units.mk0 c h.ne').mul_right.image_eq_preimage _).trans (by simp [h, division_def])
#align set.image_mul_right_Ioo Set.image_mul_right_Ioo

theorem image_mul_left_Ioo {a : α} (h : 0 < a) (b c : α) : (· * ·) a '' IooCat b c = IooCat (a * b) (a * c) := by
  convert image_mul_right_Ioo b c h using 1 <;> simp only [mul_comm _ a]
#align set.image_mul_left_Ioo Set.image_mul_left_Ioo

/-- The (pre)image under `inv` of `Ioo 0 a` is `Ioi a⁻¹`. -/
theorem inv_Ioo_0_left {a : α} (ha : 0 < a) : (IooCat 0 a)⁻¹ = IoiCat a⁻¹ := by
  ext x
  exact
    ⟨fun h => inv_inv x ▸ (inv_lt_inv ha h.1).2 h.2, fun h =>
      ⟨inv_pos.2 <| (inv_pos.2 ha).trans h, inv_inv a ▸ (inv_lt_inv ((inv_pos.2 ha).trans h) (inv_pos.2 ha)).2 h⟩⟩
#align set.inv_Ioo_0_left Set.inv_Ioo_0_left

theorem inv_Ioi {a : α} (ha : 0 < a) : (IoiCat a)⁻¹ = IooCat 0 a⁻¹ := by
  rw [inv_eq_iff_inv_eq, inv_Ioo_0_left (inv_pos.2 ha), inv_inv]
#align set.inv_Ioi Set.inv_Ioi

theorem image_const_mul_Ioi_zero {k : Type _} [LinearOrderedField k] {x : k} (hx : 0 < x) :
    (fun y => x * y) '' IoiCat (0 : k) = IoiCat 0 := by
  erw [(Units.mk0 x hx.ne').mul_left.image_eq_preimage, preimage_const_mul_Ioi 0 (inv_pos.mpr hx), zero_div]
#align set.image_const_mul_Ioi_zero Set.image_const_mul_Ioi_zero

/-!
### Images under `x ↦ a * x + b`
-/


@[simp]
theorem image_affine_Icc' {a : α} (h : 0 < a) (b c d : α) :
    (fun x => a * x + b) '' IccCat c d = IccCat (a * c + b) (a * d + b) := by
  suffices (fun x => x + b) '' ((fun x => a * x) '' Icc c d) = Icc (a * c + b) (a * d + b) by
    rwa [Set.image_image] at this
  rw [image_mul_left_Icc' h, image_add_const_Icc]
#align set.image_affine_Icc' Set.image_affine_Icc'

end LinearOrderedField

end Set

