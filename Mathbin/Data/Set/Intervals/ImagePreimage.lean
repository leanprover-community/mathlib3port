/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Patrick Massot
-/
import Mathbin.Data.Set.Pointwise.Basic
import Mathbin.Algebra.Order.Field

/-!
# (Pre)images of intervals

In this file we prove a bunch of trivial lemmas like “if we add `a` to all points of `[b, c]`,
then we get `[a + b, a + c]`”. For the functions `x ↦ x ± a`, `x ↦ a ± x`, and `x ↦ -x` we prove
lemmas about preimages and images of all intervals. We also prove a few lemmas about images under
`x ↦ a * x`, `x ↦ x * a` and `x ↦ x⁻¹`.
-/


universe u

open Pointwise

namespace Set

section HasExistsAddOfLe

/-!
The lemmas in this section state that addition maps intervals bijectively. The typeclass
`has_exists_add_of_le` is defined specifically to make them work when combined with
`ordered_cancel_add_comm_monoid`; the lemmas below therefore apply to all
`ordered_add_comm_group`, but also to `ℕ` and `ℝ≥0`, which are not groups.

TODO : move as much as possible in this file to the setting of this weaker typeclass.
-/


variable {α : Type u} [OrderedCancelAddCommMonoid α] [HasExistsAddOfLe α] (a b d : α)

theorem Icc_add_bij : BijOn (· + d) (IccCat a b) (IccCat (a + d) (b + d)) := by
  refine'
    ⟨fun _ h => ⟨add_le_add_right h.1 _, add_le_add_right h.2 _⟩, fun _ _ _ _ h => add_right_cancel h, fun _ h => _⟩
  obtain ⟨c, rfl⟩ := exists_add_of_le h.1
  rw [mem_Icc, add_right_comm, add_le_add_iff_right, add_le_add_iff_right] at h
  exact ⟨a + c, h, by rw [add_right_comm]⟩

theorem Ioo_add_bij : BijOn (· + d) (IooCat a b) (IooCat (a + d) (b + d)) := by
  refine'
    ⟨fun _ h => ⟨add_lt_add_right h.1 _, add_lt_add_right h.2 _⟩, fun _ _ _ _ h => add_right_cancel h, fun _ h => _⟩
  obtain ⟨c, rfl⟩ := exists_add_of_le h.1.le
  rw [mem_Ioo, add_right_comm, add_lt_add_iff_right, add_lt_add_iff_right] at h
  exact ⟨a + c, h, by rw [add_right_comm]⟩

theorem Ioc_add_bij : BijOn (· + d) (IocCat a b) (IocCat (a + d) (b + d)) := by
  refine'
    ⟨fun _ h => ⟨add_lt_add_right h.1 _, add_le_add_right h.2 _⟩, fun _ _ _ _ h => add_right_cancel h, fun _ h => _⟩
  obtain ⟨c, rfl⟩ := exists_add_of_le h.1.le
  rw [mem_Ioc, add_right_comm, add_lt_add_iff_right, add_le_add_iff_right] at h
  exact ⟨a + c, h, by rw [add_right_comm]⟩

theorem Ico_add_bij : BijOn (· + d) (IcoCat a b) (IcoCat (a + d) (b + d)) := by
  refine'
    ⟨fun _ h => ⟨add_le_add_right h.1 _, add_lt_add_right h.2 _⟩, fun _ _ _ _ h => add_right_cancel h, fun _ h => _⟩
  obtain ⟨c, rfl⟩ := exists_add_of_le h.1
  rw [mem_Ico, add_right_comm, add_le_add_iff_right, add_lt_add_iff_right] at h
  exact ⟨a + c, h, by rw [add_right_comm]⟩

theorem Ici_add_bij : BijOn (· + d) (IciCat a) (IciCat (a + d)) := by
  refine' ⟨fun x h => add_le_add_right (mem_Ici.mp h) _, fun _ _ _ _ h => add_right_cancel h, fun _ h => _⟩
  obtain ⟨c, rfl⟩ := exists_add_of_le (mem_Ici.mp h)
  rw [mem_Ici, add_right_comm, add_le_add_iff_right] at h
  exact ⟨a + c, h, by rw [add_right_comm]⟩

theorem Ioi_add_bij : BijOn (· + d) (IoiCat a) (IoiCat (a + d)) := by
  refine' ⟨fun x h => add_lt_add_right (mem_Ioi.mp h) _, fun _ _ _ _ h => add_right_cancel h, fun _ h => _⟩
  obtain ⟨c, rfl⟩ := exists_add_of_le (mem_Ioi.mp h).le
  rw [mem_Ioi, add_right_comm, add_lt_add_iff_right] at h
  exact ⟨a + c, h, by rw [add_right_comm]⟩

end HasExistsAddOfLe

section OrderedAddCommGroup

variable {G : Type u} [OrderedAddCommGroup G] (a b c : G)

/-!
### Preimages under `x ↦ a + x`
-/


@[simp]
theorem preimage_const_add_Ici : (fun x => a + x) ⁻¹' IciCat b = IciCat (b - a) :=
  ext fun x => sub_le_iff_le_add'.symm

@[simp]
theorem preimage_const_add_Ioi : (fun x => a + x) ⁻¹' IoiCat b = IoiCat (b - a) :=
  ext fun x => sub_lt_iff_lt_add'.symm

@[simp]
theorem preimage_const_add_Iic : (fun x => a + x) ⁻¹' IicCat b = IicCat (b - a) :=
  ext fun x => le_sub_iff_add_le'.symm

@[simp]
theorem preimage_const_add_Iio : (fun x => a + x) ⁻¹' IioCat b = IioCat (b - a) :=
  ext fun x => lt_sub_iff_add_lt'.symm

@[simp]
theorem preimage_const_add_Icc : (fun x => a + x) ⁻¹' IccCat b c = IccCat (b - a) (c - a) := by simp [← Ici_inter_Iic]

@[simp]
theorem preimage_const_add_Ico : (fun x => a + x) ⁻¹' IcoCat b c = IcoCat (b - a) (c - a) := by simp [← Ici_inter_Iio]

@[simp]
theorem preimage_const_add_Ioc : (fun x => a + x) ⁻¹' IocCat b c = IocCat (b - a) (c - a) := by simp [← Ioi_inter_Iic]

@[simp]
theorem preimage_const_add_Ioo : (fun x => a + x) ⁻¹' IooCat b c = IooCat (b - a) (c - a) := by simp [← Ioi_inter_Iio]

/-!
### Preimages under `x ↦ x + a`
-/


@[simp]
theorem preimage_add_const_Ici : (fun x => x + a) ⁻¹' IciCat b = IciCat (b - a) :=
  ext fun x => sub_le_iff_le_add.symm

@[simp]
theorem preimage_add_const_Ioi : (fun x => x + a) ⁻¹' IoiCat b = IoiCat (b - a) :=
  ext fun x => sub_lt_iff_lt_add.symm

@[simp]
theorem preimage_add_const_Iic : (fun x => x + a) ⁻¹' IicCat b = IicCat (b - a) :=
  ext fun x => le_sub_iff_add_le.symm

@[simp]
theorem preimage_add_const_Iio : (fun x => x + a) ⁻¹' IioCat b = IioCat (b - a) :=
  ext fun x => lt_sub_iff_add_lt.symm

@[simp]
theorem preimage_add_const_Icc : (fun x => x + a) ⁻¹' IccCat b c = IccCat (b - a) (c - a) := by simp [← Ici_inter_Iic]

@[simp]
theorem preimage_add_const_Ico : (fun x => x + a) ⁻¹' IcoCat b c = IcoCat (b - a) (c - a) := by simp [← Ici_inter_Iio]

@[simp]
theorem preimage_add_const_Ioc : (fun x => x + a) ⁻¹' IocCat b c = IocCat (b - a) (c - a) := by simp [← Ioi_inter_Iic]

@[simp]
theorem preimage_add_const_Ioo : (fun x => x + a) ⁻¹' IooCat b c = IooCat (b - a) (c - a) := by simp [← Ioi_inter_Iio]

/-!
### Preimages under `x ↦ -x`
-/


@[simp]
theorem preimage_neg_Ici : -IciCat a = IicCat (-a) :=
  ext fun x => le_neg

@[simp]
theorem preimage_neg_Iic : -IicCat a = IciCat (-a) :=
  ext fun x => neg_le

@[simp]
theorem preimage_neg_Ioi : -IoiCat a = IioCat (-a) :=
  ext fun x => lt_neg

@[simp]
theorem preimage_neg_Iio : -IioCat a = IoiCat (-a) :=
  ext fun x => neg_lt

@[simp]
theorem preimage_neg_Icc : -IccCat a b = IccCat (-b) (-a) := by simp [← Ici_inter_Iic, inter_comm]

@[simp]
theorem preimage_neg_Ico : -IcoCat a b = IocCat (-b) (-a) := by simp [← Ici_inter_Iio, ← Ioi_inter_Iic, inter_comm]

@[simp]
theorem preimage_neg_Ioc : -IocCat a b = IcoCat (-b) (-a) := by simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]

@[simp]
theorem preimage_neg_Ioo : -IooCat a b = IooCat (-b) (-a) := by simp [← Ioi_inter_Iio, inter_comm]

/-!
### Preimages under `x ↦ x - a`
-/


@[simp]
theorem preimage_sub_const_Ici : (fun x => x - a) ⁻¹' IciCat b = IciCat (b + a) := by simp [sub_eq_add_neg]

@[simp]
theorem preimage_sub_const_Ioi : (fun x => x - a) ⁻¹' IoiCat b = IoiCat (b + a) := by simp [sub_eq_add_neg]

@[simp]
theorem preimage_sub_const_Iic : (fun x => x - a) ⁻¹' IicCat b = IicCat (b + a) := by simp [sub_eq_add_neg]

@[simp]
theorem preimage_sub_const_Iio : (fun x => x - a) ⁻¹' IioCat b = IioCat (b + a) := by simp [sub_eq_add_neg]

@[simp]
theorem preimage_sub_const_Icc : (fun x => x - a) ⁻¹' IccCat b c = IccCat (b + a) (c + a) := by simp [sub_eq_add_neg]

@[simp]
theorem preimage_sub_const_Ico : (fun x => x - a) ⁻¹' IcoCat b c = IcoCat (b + a) (c + a) := by simp [sub_eq_add_neg]

@[simp]
theorem preimage_sub_const_Ioc : (fun x => x - a) ⁻¹' IocCat b c = IocCat (b + a) (c + a) := by simp [sub_eq_add_neg]

@[simp]
theorem preimage_sub_const_Ioo : (fun x => x - a) ⁻¹' IooCat b c = IooCat (b + a) (c + a) := by simp [sub_eq_add_neg]

/-!
### Preimages under `x ↦ a - x`
-/


@[simp]
theorem preimage_const_sub_Ici : (fun x => a - x) ⁻¹' IciCat b = IicCat (a - b) :=
  ext fun x => le_sub

@[simp]
theorem preimage_const_sub_Iic : (fun x => a - x) ⁻¹' IicCat b = IciCat (a - b) :=
  ext fun x => sub_le

@[simp]
theorem preimage_const_sub_Ioi : (fun x => a - x) ⁻¹' IoiCat b = IioCat (a - b) :=
  ext fun x => lt_sub

@[simp]
theorem preimage_const_sub_Iio : (fun x => a - x) ⁻¹' IioCat b = IoiCat (a - b) :=
  ext fun x => sub_lt

@[simp]
theorem preimage_const_sub_Icc : (fun x => a - x) ⁻¹' IccCat b c = IccCat (a - c) (a - b) := by
  simp [← Ici_inter_Iic, inter_comm]

@[simp]
theorem preimage_const_sub_Ico : (fun x => a - x) ⁻¹' IcoCat b c = IocCat (a - c) (a - b) := by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]

@[simp]
theorem preimage_const_sub_Ioc : (fun x => a - x) ⁻¹' IocCat b c = IcoCat (a - c) (a - b) := by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]

@[simp]
theorem preimage_const_sub_Ioo : (fun x => a - x) ⁻¹' IooCat b c = IooCat (a - c) (a - b) := by
  simp [← Ioi_inter_Iio, inter_comm]

/-!
### Images under `x ↦ a + x`
-/


@[simp]
theorem image_const_add_Ici : (fun x => a + x) '' IciCat b = IciCat (a + b) := by simp [add_comm]

@[simp]
theorem image_const_add_Iic : (fun x => a + x) '' IicCat b = IicCat (a + b) := by simp [add_comm]

@[simp]
theorem image_const_add_Iio : (fun x => a + x) '' IioCat b = IioCat (a + b) := by simp [add_comm]

@[simp]
theorem image_const_add_Ioi : (fun x => a + x) '' IoiCat b = IoiCat (a + b) := by simp [add_comm]

@[simp]
theorem image_const_add_Icc : (fun x => a + x) '' IccCat b c = IccCat (a + b) (a + c) := by simp [add_comm]

@[simp]
theorem image_const_add_Ico : (fun x => a + x) '' IcoCat b c = IcoCat (a + b) (a + c) := by simp [add_comm]

@[simp]
theorem image_const_add_Ioc : (fun x => a + x) '' IocCat b c = IocCat (a + b) (a + c) := by simp [add_comm]

@[simp]
theorem image_const_add_Ioo : (fun x => a + x) '' IooCat b c = IooCat (a + b) (a + c) := by simp [add_comm]

/-!
### Images under `x ↦ x + a`
-/


@[simp]
theorem image_add_const_Ici : (fun x => x + a) '' IciCat b = IciCat (b + a) := by simp

@[simp]
theorem image_add_const_Iic : (fun x => x + a) '' IicCat b = IicCat (b + a) := by simp

@[simp]
theorem image_add_const_Iio : (fun x => x + a) '' IioCat b = IioCat (b + a) := by simp

@[simp]
theorem image_add_const_Ioi : (fun x => x + a) '' IoiCat b = IoiCat (b + a) := by simp

@[simp]
theorem image_add_const_Icc : (fun x => x + a) '' IccCat b c = IccCat (b + a) (c + a) := by simp

@[simp]
theorem image_add_const_Ico : (fun x => x + a) '' IcoCat b c = IcoCat (b + a) (c + a) := by simp

@[simp]
theorem image_add_const_Ioc : (fun x => x + a) '' IocCat b c = IocCat (b + a) (c + a) := by simp

@[simp]
theorem image_add_const_Ioo : (fun x => x + a) '' IooCat b c = IooCat (b + a) (c + a) := by simp

/-!
### Images under `x ↦ -x`
-/


theorem image_neg_Ici : Neg.neg '' IciCat a = IicCat (-a) := by simp

theorem image_neg_Iic : Neg.neg '' IicCat a = IciCat (-a) := by simp

theorem image_neg_Ioi : Neg.neg '' IoiCat a = IioCat (-a) := by simp

theorem image_neg_Iio : Neg.neg '' IioCat a = IoiCat (-a) := by simp

theorem image_neg_Icc : Neg.neg '' IccCat a b = IccCat (-b) (-a) := by simp

theorem image_neg_Ico : Neg.neg '' IcoCat a b = IocCat (-b) (-a) := by simp

theorem image_neg_Ioc : Neg.neg '' IocCat a b = IcoCat (-b) (-a) := by simp

theorem image_neg_Ioo : Neg.neg '' IooCat a b = IooCat (-b) (-a) := by simp

/-!
### Images under `x ↦ a - x`
-/


@[simp]
theorem image_const_sub_Ici : (fun x => a - x) '' IciCat b = IicCat (a - b) := by
  simp [sub_eq_add_neg, image_comp (fun x => a + x) fun x => -x]

@[simp]
theorem image_const_sub_Iic : (fun x => a - x) '' IicCat b = IciCat (a - b) := by
  simp [sub_eq_add_neg, image_comp (fun x => a + x) fun x => -x]

@[simp]
theorem image_const_sub_Ioi : (fun x => a - x) '' IoiCat b = IioCat (a - b) := by
  simp [sub_eq_add_neg, image_comp (fun x => a + x) fun x => -x]

@[simp]
theorem image_const_sub_Iio : (fun x => a - x) '' IioCat b = IoiCat (a - b) := by
  simp [sub_eq_add_neg, image_comp (fun x => a + x) fun x => -x]

@[simp]
theorem image_const_sub_Icc : (fun x => a - x) '' IccCat b c = IccCat (a - c) (a - b) := by
  simp [sub_eq_add_neg, image_comp (fun x => a + x) fun x => -x]

@[simp]
theorem image_const_sub_Ico : (fun x => a - x) '' IcoCat b c = IocCat (a - c) (a - b) := by
  simp [sub_eq_add_neg, image_comp (fun x => a + x) fun x => -x]

@[simp]
theorem image_const_sub_Ioc : (fun x => a - x) '' IocCat b c = IcoCat (a - c) (a - b) := by
  simp [sub_eq_add_neg, image_comp (fun x => a + x) fun x => -x]

@[simp]
theorem image_const_sub_Ioo : (fun x => a - x) '' IooCat b c = IooCat (a - c) (a - b) := by
  simp [sub_eq_add_neg, image_comp (fun x => a + x) fun x => -x]

/-!
### Images under `x ↦ x - a`
-/


@[simp]
theorem image_sub_const_Ici : (fun x => x - a) '' IciCat b = IciCat (b - a) := by simp [sub_eq_neg_add]

@[simp]
theorem image_sub_const_Iic : (fun x => x - a) '' IicCat b = IicCat (b - a) := by simp [sub_eq_neg_add]

@[simp]
theorem image_sub_const_Ioi : (fun x => x - a) '' IoiCat b = IoiCat (b - a) := by simp [sub_eq_neg_add]

@[simp]
theorem image_sub_const_Iio : (fun x => x - a) '' IioCat b = IioCat (b - a) := by simp [sub_eq_neg_add]

@[simp]
theorem image_sub_const_Icc : (fun x => x - a) '' IccCat b c = IccCat (b - a) (c - a) := by simp [sub_eq_neg_add]

@[simp]
theorem image_sub_const_Ico : (fun x => x - a) '' IcoCat b c = IcoCat (b - a) (c - a) := by simp [sub_eq_neg_add]

@[simp]
theorem image_sub_const_Ioc : (fun x => x - a) '' IocCat b c = IocCat (b - a) (c - a) := by simp [sub_eq_neg_add]

@[simp]
theorem image_sub_const_Ioo : (fun x => x - a) '' IooCat b c = IooCat (b - a) (c - a) := by simp [sub_eq_neg_add]

/-!
### Bijections
-/


theorem Iic_add_bij : BijOn (· + a) (IicCat b) (IicCat (b + a)) := by
  refine' ⟨fun x h => add_le_add_right (mem_Iic.mp h) _, fun _ _ _ _ h => add_right_cancel h, fun _ h => _⟩
  simpa [add_comm a] using h

theorem Iio_add_bij : BijOn (· + a) (IioCat b) (IioCat (b + a)) := by
  refine' ⟨fun x h => add_lt_add_right (mem_Iio.mp h) _, fun _ _ _ _ h => add_right_cancel h, fun _ h => _⟩
  simpa [add_comm a] using h

end OrderedAddCommGroup

/-!
### Multiplication and inverse in a field
-/


section LinearOrderedField

variable {k : Type u} [LinearOrderedField k]

@[simp]
theorem preimage_mul_const_Iio (a : k) {c : k} (h : 0 < c) : (fun x => x * c) ⁻¹' IioCat a = IioCat (a / c) :=
  ext fun x => (lt_div_iff h).symm

@[simp]
theorem preimage_mul_const_Ioi (a : k) {c : k} (h : 0 < c) : (fun x => x * c) ⁻¹' IoiCat a = IoiCat (a / c) :=
  ext fun x => (div_lt_iff h).symm

@[simp]
theorem preimage_mul_const_Iic (a : k) {c : k} (h : 0 < c) : (fun x => x * c) ⁻¹' IicCat a = IicCat (a / c) :=
  ext fun x => (le_div_iff h).symm

@[simp]
theorem preimage_mul_const_Ici (a : k) {c : k} (h : 0 < c) : (fun x => x * c) ⁻¹' IciCat a = IciCat (a / c) :=
  ext fun x => (div_le_iff h).symm

@[simp]
theorem preimage_mul_const_Ioo (a b : k) {c : k} (h : 0 < c) :
    (fun x => x * c) ⁻¹' IooCat a b = IooCat (a / c) (b / c) := by simp [← Ioi_inter_Iio, h]

@[simp]
theorem preimage_mul_const_Ioc (a b : k) {c : k} (h : 0 < c) :
    (fun x => x * c) ⁻¹' IocCat a b = IocCat (a / c) (b / c) := by simp [← Ioi_inter_Iic, h]

@[simp]
theorem preimage_mul_const_Ico (a b : k) {c : k} (h : 0 < c) :
    (fun x => x * c) ⁻¹' IcoCat a b = IcoCat (a / c) (b / c) := by simp [← Ici_inter_Iio, h]

@[simp]
theorem preimage_mul_const_Icc (a b : k) {c : k} (h : 0 < c) :
    (fun x => x * c) ⁻¹' IccCat a b = IccCat (a / c) (b / c) := by simp [← Ici_inter_Iic, h]

@[simp]
theorem preimage_mul_const_Iio_of_neg (a : k) {c : k} (h : c < 0) : (fun x => x * c) ⁻¹' IioCat a = IoiCat (a / c) :=
  ext fun x => (div_lt_iff_of_neg h).symm

@[simp]
theorem preimage_mul_const_Ioi_of_neg (a : k) {c : k} (h : c < 0) : (fun x => x * c) ⁻¹' IoiCat a = IioCat (a / c) :=
  ext fun x => (lt_div_iff_of_neg h).symm

@[simp]
theorem preimage_mul_const_Iic_of_neg (a : k) {c : k} (h : c < 0) : (fun x => x * c) ⁻¹' IicCat a = IciCat (a / c) :=
  ext fun x => (div_le_iff_of_neg h).symm

@[simp]
theorem preimage_mul_const_Ici_of_neg (a : k) {c : k} (h : c < 0) : (fun x => x * c) ⁻¹' IciCat a = IicCat (a / c) :=
  ext fun x => (le_div_iff_of_neg h).symm

@[simp]
theorem preimage_mul_const_Ioo_of_neg (a b : k) {c : k} (h : c < 0) :
    (fun x => x * c) ⁻¹' IooCat a b = IooCat (b / c) (a / c) := by simp [← Ioi_inter_Iio, h, inter_comm]

@[simp]
theorem preimage_mul_const_Ioc_of_neg (a b : k) {c : k} (h : c < 0) :
    (fun x => x * c) ⁻¹' IocCat a b = IcoCat (b / c) (a / c) := by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, h, inter_comm]

@[simp]
theorem preimage_mul_const_Ico_of_neg (a b : k) {c : k} (h : c < 0) :
    (fun x => x * c) ⁻¹' IcoCat a b = IocCat (b / c) (a / c) := by
  simp [← Ici_inter_Iio, ← Ioi_inter_Iic, h, inter_comm]

@[simp]
theorem preimage_mul_const_Icc_of_neg (a b : k) {c : k} (h : c < 0) :
    (fun x => x * c) ⁻¹' IccCat a b = IccCat (b / c) (a / c) := by simp [← Ici_inter_Iic, h, inter_comm]

@[simp]
theorem preimage_const_mul_Iio (a : k) {c : k} (h : 0 < c) : (· * ·) c ⁻¹' IioCat a = IioCat (a / c) :=
  ext fun x => (lt_div_iff' h).symm

@[simp]
theorem preimage_const_mul_Ioi (a : k) {c : k} (h : 0 < c) : (· * ·) c ⁻¹' IoiCat a = IoiCat (a / c) :=
  ext fun x => (div_lt_iff' h).symm

@[simp]
theorem preimage_const_mul_Iic (a : k) {c : k} (h : 0 < c) : (· * ·) c ⁻¹' IicCat a = IicCat (a / c) :=
  ext fun x => (le_div_iff' h).symm

@[simp]
theorem preimage_const_mul_Ici (a : k) {c : k} (h : 0 < c) : (· * ·) c ⁻¹' IciCat a = IciCat (a / c) :=
  ext fun x => (div_le_iff' h).symm

@[simp]
theorem preimage_const_mul_Ioo (a b : k) {c : k} (h : 0 < c) : (· * ·) c ⁻¹' IooCat a b = IooCat (a / c) (b / c) := by
  simp [← Ioi_inter_Iio, h]

@[simp]
theorem preimage_const_mul_Ioc (a b : k) {c : k} (h : 0 < c) : (· * ·) c ⁻¹' IocCat a b = IocCat (a / c) (b / c) := by
  simp [← Ioi_inter_Iic, h]

@[simp]
theorem preimage_const_mul_Ico (a b : k) {c : k} (h : 0 < c) : (· * ·) c ⁻¹' IcoCat a b = IcoCat (a / c) (b / c) := by
  simp [← Ici_inter_Iio, h]

@[simp]
theorem preimage_const_mul_Icc (a b : k) {c : k} (h : 0 < c) : (· * ·) c ⁻¹' IccCat a b = IccCat (a / c) (b / c) := by
  simp [← Ici_inter_Iic, h]

@[simp]
theorem preimage_const_mul_Iio_of_neg (a : k) {c : k} (h : c < 0) : (· * ·) c ⁻¹' IioCat a = IoiCat (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Iio_of_neg a h

@[simp]
theorem preimage_const_mul_Ioi_of_neg (a : k) {c : k} (h : c < 0) : (· * ·) c ⁻¹' IoiCat a = IioCat (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ioi_of_neg a h

@[simp]
theorem preimage_const_mul_Iic_of_neg (a : k) {c : k} (h : c < 0) : (· * ·) c ⁻¹' IicCat a = IciCat (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Iic_of_neg a h

@[simp]
theorem preimage_const_mul_Ici_of_neg (a : k) {c : k} (h : c < 0) : (· * ·) c ⁻¹' IciCat a = IicCat (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ici_of_neg a h

@[simp]
theorem preimage_const_mul_Ioo_of_neg (a b : k) {c : k} (h : c < 0) :
    (· * ·) c ⁻¹' IooCat a b = IooCat (b / c) (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ioo_of_neg a b h

@[simp]
theorem preimage_const_mul_Ioc_of_neg (a b : k) {c : k} (h : c < 0) :
    (· * ·) c ⁻¹' IocCat a b = IcoCat (b / c) (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ioc_of_neg a b h

@[simp]
theorem preimage_const_mul_Ico_of_neg (a b : k) {c : k} (h : c < 0) :
    (· * ·) c ⁻¹' IcoCat a b = IocCat (b / c) (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ico_of_neg a b h

@[simp]
theorem preimage_const_mul_Icc_of_neg (a b : k) {c : k} (h : c < 0) :
    (· * ·) c ⁻¹' IccCat a b = IccCat (b / c) (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Icc_of_neg a b h

theorem image_mul_right_Icc' (a b : k) {c : k} (h : 0 < c) : (fun x => x * c) '' IccCat a b = IccCat (a * c) (b * c) :=
  ((Units.mk0 c h.ne').mul_right.image_eq_preimage _).trans (by simp [h, division_def])

theorem image_mul_right_Icc {a b c : k} (hab : a ≤ b) (hc : 0 ≤ c) :
    (fun x => x * c) '' IccCat a b = IccCat (a * c) (b * c) := by
  cases eq_or_lt_of_le hc
  · subst c
    simp [(nonempty_Icc.2 hab).image_const]
    
  exact image_mul_right_Icc' a b ‹0 < c›

theorem image_mul_left_Icc' {a : k} (h : 0 < a) (b c : k) : (· * ·) a '' IccCat b c = IccCat (a * b) (a * c) := by
  convert image_mul_right_Icc' b c h using 1 <;> simp only [mul_comm _ a]

theorem image_mul_left_Icc {a b c : k} (ha : 0 ≤ a) (hbc : b ≤ c) : (· * ·) a '' IccCat b c = IccCat (a * b) (a * c) :=
  by convert image_mul_right_Icc hbc ha using 1 <;> simp only [mul_comm _ a]

theorem image_mul_right_Ioo (a b : k) {c : k} (h : 0 < c) : (fun x => x * c) '' IooCat a b = IooCat (a * c) (b * c) :=
  ((Units.mk0 c h.ne').mul_right.image_eq_preimage _).trans (by simp [h, division_def])

theorem image_mul_left_Ioo {a : k} (h : 0 < a) (b c : k) : (· * ·) a '' IooCat b c = IooCat (a * b) (a * c) := by
  convert image_mul_right_Ioo b c h using 1 <;> simp only [mul_comm _ a]

/-- The (pre)image under `inv` of `Ioo 0 a` is `Ioi a⁻¹`. -/
theorem inv_Ioo_0_left {a : k} (ha : 0 < a) : (IooCat 0 a)⁻¹ = IoiCat a⁻¹ := by
  ext x
  exact
    ⟨fun h => inv_inv x ▸ (inv_lt_inv ha h.1).2 h.2, fun h =>
      ⟨inv_pos.2 <| (inv_pos.2 ha).trans h, inv_inv a ▸ (inv_lt_inv ((inv_pos.2 ha).trans h) (inv_pos.2 ha)).2 h⟩⟩

theorem inv_Ioi {a : k} (ha : 0 < a) : (IoiCat a)⁻¹ = IooCat 0 a⁻¹ := by
  rw [inv_eq_iff_inv_eq, inv_Ioo_0_left (inv_pos.2 ha), inv_inv]

theorem image_const_mul_Ioi_zero {k : Type _} [LinearOrderedField k] {x : k} (hx : 0 < x) :
    (fun y => x * y) '' IoiCat (0 : k) = IoiCat 0 := by
  erw [(Units.mk0 x hx.ne').mul_left.image_eq_preimage, preimage_const_mul_Ioi 0 (inv_pos.mpr hx), zero_div]

/-!
### Images under `x ↦ a * x + b`
-/


@[simp]
theorem image_affine_Icc' {a : k} (h : 0 < a) (b c d : k) :
    (fun x => a * x + b) '' IccCat c d = IccCat (a * c + b) (a * d + b) := by
  suffices (fun x => x + b) '' ((fun x => a * x) '' Icc c d) = Icc (a * c + b) (a * d + b) by
    rwa [Set.image_image] at this
  rw [image_mul_left_Icc' h, image_add_const_Icc]

end LinearOrderedField

end Set

