/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Yury Kudryashov, Rémy Degenne
-/
import Mathbin.Algebra.Order.Group.Basic
import Mathbin.Order.RelIso

/-!
# Intervals

In any preorder `α`, we define intervals (which on each side can be either infinite, open, or
closed) using the following naming conventions:
- `i`: infinite
- `o`: open
- `c`: closed

Each interval has the name `I` + letter for left side + letter for right side. For instance,
`Ioc a b` denotes the inverval `(a, b]`.

This file contains these definitions, and basic facts on inclusion, intersection, difference of
intervals (where the precise statements may depend on the properties of the order, in particular
for some statements it should be `linear_order` or `densely_ordered`).

TODO: This is just the beginning; a lot of rules are missing
-/


open Function

open OrderDual (toDual ofDual)

variable {α β : Type _}

namespace Set

section Preorder

variable [Preorder α] {a a₁ a₂ b b₁ b₂ c x : α}

/-- Left-open right-open interval -/
def IooCat (a b : α) :=
  { x | a < x ∧ x < b }

/-- Left-closed right-open interval -/
def IcoCat (a b : α) :=
  { x | a ≤ x ∧ x < b }

/-- Left-infinite right-open interval -/
def IioCat (a : α) :=
  { x | x < a }

/-- Left-closed right-closed interval -/
def IccCat (a b : α) :=
  { x | a ≤ x ∧ x ≤ b }

/-- Left-infinite right-closed interval -/
def IicCat (b : α) :=
  { x | x ≤ b }

/-- Left-open right-closed interval -/
def IocCat (a b : α) :=
  { x | a < x ∧ x ≤ b }

/-- Left-closed right-infinite interval -/
def IciCat (a : α) :=
  { x | a ≤ x }

/-- Left-open right-infinite interval -/
def IoiCat (a : α) :=
  { x | a < x }

theorem Ioo_def (a b : α) : { x | a < x ∧ x < b } = IooCat a b :=
  rfl

theorem Ico_def (a b : α) : { x | a ≤ x ∧ x < b } = IcoCat a b :=
  rfl

theorem Iio_def (a : α) : { x | x < a } = IioCat a :=
  rfl

theorem Icc_def (a b : α) : { x | a ≤ x ∧ x ≤ b } = IccCat a b :=
  rfl

theorem Iic_def (b : α) : { x | x ≤ b } = IicCat b :=
  rfl

theorem Ioc_def (a b : α) : { x | a < x ∧ x ≤ b } = IocCat a b :=
  rfl

theorem Ici_def (a : α) : { x | a ≤ x } = IciCat a :=
  rfl

theorem Ioi_def (a : α) : { x | a < x } = IoiCat a :=
  rfl

@[simp]
theorem mem_Ioo : x ∈ IooCat a b ↔ a < x ∧ x < b :=
  Iff.rfl

@[simp]
theorem mem_Ico : x ∈ IcoCat a b ↔ a ≤ x ∧ x < b :=
  Iff.rfl

@[simp]
theorem mem_Iio : x ∈ IioCat b ↔ x < b :=
  Iff.rfl

@[simp]
theorem mem_Icc : x ∈ IccCat a b ↔ a ≤ x ∧ x ≤ b :=
  Iff.rfl

@[simp]
theorem mem_Iic : x ∈ IicCat b ↔ x ≤ b :=
  Iff.rfl

@[simp]
theorem mem_Ioc : x ∈ IocCat a b ↔ a < x ∧ x ≤ b :=
  Iff.rfl

@[simp]
theorem mem_Ici : x ∈ IciCat a ↔ a ≤ x :=
  Iff.rfl

@[simp]
theorem mem_Ioi : x ∈ IoiCat a ↔ a < x :=
  Iff.rfl

instance decidableMemIoo [Decidable (a < x ∧ x < b)] : Decidable (x ∈ IooCat a b) := by assumption

instance decidableMemIco [Decidable (a ≤ x ∧ x < b)] : Decidable (x ∈ IcoCat a b) := by assumption

instance decidableMemIio [Decidable (x < b)] : Decidable (x ∈ IioCat b) := by assumption

instance decidableMemIcc [Decidable (a ≤ x ∧ x ≤ b)] : Decidable (x ∈ IccCat a b) := by assumption

instance decidableMemIic [Decidable (x ≤ b)] : Decidable (x ∈ IicCat b) := by assumption

instance decidableMemIoc [Decidable (a < x ∧ x ≤ b)] : Decidable (x ∈ IocCat a b) := by assumption

instance decidableMemIci [Decidable (a ≤ x)] : Decidable (x ∈ IciCat a) := by assumption

instance decidableMemIoi [Decidable (a < x)] : Decidable (x ∈ IoiCat a) := by assumption

@[simp]
theorem left_mem_Ioo : a ∈ IooCat a b ↔ False := by simp [lt_irrefl]

@[simp]
theorem left_mem_Ico : a ∈ IcoCat a b ↔ a < b := by simp [le_refl]

@[simp]
theorem left_mem_Icc : a ∈ IccCat a b ↔ a ≤ b := by simp [le_refl]

@[simp]
theorem left_mem_Ioc : a ∈ IocCat a b ↔ False := by simp [lt_irrefl]

theorem left_mem_Ici : a ∈ IciCat a := by simp

@[simp]
theorem right_mem_Ioo : b ∈ IooCat a b ↔ False := by simp [lt_irrefl]

@[simp]
theorem right_mem_Ico : b ∈ IcoCat a b ↔ False := by simp [lt_irrefl]

@[simp]
theorem right_mem_Icc : b ∈ IccCat a b ↔ a ≤ b := by simp [le_refl]

@[simp]
theorem right_mem_Ioc : b ∈ IocCat a b ↔ a < b := by simp [le_refl]

theorem right_mem_Iic : a ∈ IicCat a := by simp

@[simp]
theorem dual_Ici : IciCat (toDual a) = of_dual ⁻¹' IicCat a :=
  rfl

@[simp]
theorem dual_Iic : IicCat (toDual a) = of_dual ⁻¹' IciCat a :=
  rfl

@[simp]
theorem dual_Ioi : IoiCat (toDual a) = of_dual ⁻¹' IioCat a :=
  rfl

@[simp]
theorem dual_Iio : IioCat (toDual a) = of_dual ⁻¹' IoiCat a :=
  rfl

@[simp]
theorem dual_Icc : IccCat (toDual a) (toDual b) = of_dual ⁻¹' IccCat b a :=
  Set.ext fun x => and_comm' _ _

@[simp]
theorem dual_Ioc : IocCat (toDual a) (toDual b) = of_dual ⁻¹' IcoCat b a :=
  Set.ext fun x => and_comm' _ _

@[simp]
theorem dual_Ico : IcoCat (toDual a) (toDual b) = of_dual ⁻¹' IocCat b a :=
  Set.ext fun x => and_comm' _ _

@[simp]
theorem dual_Ioo : IooCat (toDual a) (toDual b) = of_dual ⁻¹' IooCat b a :=
  Set.ext fun x => and_comm' _ _

@[simp]
theorem nonempty_Icc : (IccCat a b).Nonempty ↔ a ≤ b :=
  ⟨fun ⟨x, hx⟩ => hx.1.trans hx.2, fun h => ⟨a, left_mem_Icc.2 h⟩⟩

@[simp]
theorem nonempty_Ico : (IcoCat a b).Nonempty ↔ a < b :=
  ⟨fun ⟨x, hx⟩ => hx.1.trans_lt hx.2, fun h => ⟨a, left_mem_Ico.2 h⟩⟩

@[simp]
theorem nonempty_Ioc : (IocCat a b).Nonempty ↔ a < b :=
  ⟨fun ⟨x, hx⟩ => hx.1.trans_le hx.2, fun h => ⟨b, right_mem_Ioc.2 h⟩⟩

@[simp]
theorem nonempty_Ici : (IciCat a).Nonempty :=
  ⟨a, left_mem_Ici⟩

@[simp]
theorem nonempty_Iic : (IicCat a).Nonempty :=
  ⟨a, right_mem_Iic⟩

@[simp]
theorem nonempty_Ioo [DenselyOrdered α] : (IooCat a b).Nonempty ↔ a < b :=
  ⟨fun ⟨x, ha, hb⟩ => ha.trans hb, exists_between⟩

@[simp]
theorem nonempty_Ioi [NoMaxOrder α] : (IoiCat a).Nonempty :=
  exists_gt a

@[simp]
theorem nonempty_Iio [NoMinOrder α] : (IioCat a).Nonempty :=
  exists_lt a

theorem nonempty_Icc_subtype (h : a ≤ b) : Nonempty (IccCat a b) :=
  Nonempty.to_subtype (nonempty_Icc.mpr h)

theorem nonempty_Ico_subtype (h : a < b) : Nonempty (IcoCat a b) :=
  Nonempty.to_subtype (nonempty_Ico.mpr h)

theorem nonempty_Ioc_subtype (h : a < b) : Nonempty (IocCat a b) :=
  Nonempty.to_subtype (nonempty_Ioc.mpr h)

/-- An interval `Ici a` is nonempty. -/
instance nonempty_Ici_subtype : Nonempty (IciCat a) :=
  Nonempty.to_subtype nonempty_Ici

/-- An interval `Iic a` is nonempty. -/
instance nonempty_Iic_subtype : Nonempty (IicCat a) :=
  Nonempty.to_subtype nonempty_Iic

theorem nonempty_Ioo_subtype [DenselyOrdered α] (h : a < b) : Nonempty (IooCat a b) :=
  Nonempty.to_subtype (nonempty_Ioo.mpr h)

/-- In an order without maximal elements, the intervals `Ioi` are nonempty. -/
instance nonempty_Ioi_subtype [NoMaxOrder α] : Nonempty (IoiCat a) :=
  Nonempty.to_subtype nonempty_Ioi

/-- In an order without minimal elements, the intervals `Iio` are nonempty. -/
instance nonempty_Iio_subtype [NoMinOrder α] : Nonempty (IioCat a) :=
  Nonempty.to_subtype nonempty_Iio

instance [NoMinOrder α] : NoMinOrder (IioCat a) :=
  ⟨fun a =>
    let ⟨b, hb⟩ := exists_lt (a : α)
    ⟨⟨b, lt_trans hb a.2⟩, hb⟩⟩

instance [NoMinOrder α] : NoMinOrder (IicCat a) :=
  ⟨fun a =>
    let ⟨b, hb⟩ := exists_lt (a : α)
    ⟨⟨b, hb.le.trans a.2⟩, hb⟩⟩

instance [NoMaxOrder α] : NoMaxOrder (IoiCat a) :=
  OrderDual.no_max_order (IioCat (toDual a))

instance [NoMaxOrder α] : NoMaxOrder (IciCat a) :=
  OrderDual.no_max_order (IicCat (toDual a))

@[simp]
theorem Icc_eq_empty (h : ¬a ≤ b) : IccCat a b = ∅ :=
  eq_empty_iff_forall_not_mem.2 fun x ⟨ha, hb⟩ => h (ha.trans hb)

@[simp]
theorem Ico_eq_empty (h : ¬a < b) : IcoCat a b = ∅ :=
  eq_empty_iff_forall_not_mem.2 fun x ⟨ha, hb⟩ => h (ha.trans_lt hb)

@[simp]
theorem Ioc_eq_empty (h : ¬a < b) : IocCat a b = ∅ :=
  eq_empty_iff_forall_not_mem.2 fun x ⟨ha, hb⟩ => h (ha.trans_le hb)

@[simp]
theorem Ioo_eq_empty (h : ¬a < b) : IooCat a b = ∅ :=
  eq_empty_iff_forall_not_mem.2 fun x ⟨ha, hb⟩ => h (ha.trans hb)

@[simp]
theorem Icc_eq_empty_of_lt (h : b < a) : IccCat a b = ∅ :=
  Icc_eq_empty h.not_le

@[simp]
theorem Ico_eq_empty_of_le (h : b ≤ a) : IcoCat a b = ∅ :=
  Ico_eq_empty h.not_lt

@[simp]
theorem Ioc_eq_empty_of_le (h : b ≤ a) : IocCat a b = ∅ :=
  Ioc_eq_empty h.not_lt

@[simp]
theorem Ioo_eq_empty_of_le (h : b ≤ a) : IooCat a b = ∅ :=
  Ioo_eq_empty h.not_lt

@[simp]
theorem Ico_self (a : α) : IcoCat a a = ∅ :=
  Ico_eq_empty <| lt_irrefl _

@[simp]
theorem Ioc_self (a : α) : IocCat a a = ∅ :=
  Ioc_eq_empty <| lt_irrefl _

@[simp]
theorem Ioo_self (a : α) : IooCat a a = ∅ :=
  Ioo_eq_empty <| lt_irrefl _

theorem Ici_subset_Ici : IciCat a ⊆ IciCat b ↔ b ≤ a :=
  ⟨fun h => h <| left_mem_Ici, fun h x hx => h.trans hx⟩

theorem Iic_subset_Iic : IicCat a ⊆ IicCat b ↔ a ≤ b :=
  @Ici_subset_Ici αᵒᵈ _ _ _

theorem Ici_subset_Ioi : IciCat a ⊆ IoiCat b ↔ b < a :=
  ⟨fun h => h left_mem_Ici, fun h x hx => h.trans_le hx⟩

theorem Iic_subset_Iio : IicCat a ⊆ IioCat b ↔ a < b :=
  ⟨fun h => h right_mem_Iic, fun h x hx => lt_of_le_of_lt hx h⟩

theorem Ioo_subset_Ioo (h₁ : a₂ ≤ a₁) (h₂ : b₁ ≤ b₂) : IooCat a₁ b₁ ⊆ IooCat a₂ b₂ := fun x ⟨hx₁, hx₂⟩ =>
  ⟨h₁.trans_lt hx₁, hx₂.trans_le h₂⟩

theorem Ioo_subset_Ioo_left (h : a₁ ≤ a₂) : IooCat a₂ b ⊆ IooCat a₁ b :=
  Ioo_subset_Ioo h le_rfl

theorem Ioo_subset_Ioo_right (h : b₁ ≤ b₂) : IooCat a b₁ ⊆ IooCat a b₂ :=
  Ioo_subset_Ioo le_rfl h

theorem Ico_subset_Ico (h₁ : a₂ ≤ a₁) (h₂ : b₁ ≤ b₂) : IcoCat a₁ b₁ ⊆ IcoCat a₂ b₂ := fun x ⟨hx₁, hx₂⟩ =>
  ⟨h₁.trans hx₁, hx₂.trans_le h₂⟩

theorem Ico_subset_Ico_left (h : a₁ ≤ a₂) : IcoCat a₂ b ⊆ IcoCat a₁ b :=
  Ico_subset_Ico h le_rfl

theorem Ico_subset_Ico_right (h : b₁ ≤ b₂) : IcoCat a b₁ ⊆ IcoCat a b₂ :=
  Ico_subset_Ico le_rfl h

theorem Icc_subset_Icc (h₁ : a₂ ≤ a₁) (h₂ : b₁ ≤ b₂) : IccCat a₁ b₁ ⊆ IccCat a₂ b₂ := fun x ⟨hx₁, hx₂⟩ =>
  ⟨h₁.trans hx₁, le_trans hx₂ h₂⟩

theorem Icc_subset_Icc_left (h : a₁ ≤ a₂) : IccCat a₂ b ⊆ IccCat a₁ b :=
  Icc_subset_Icc h le_rfl

theorem Icc_subset_Icc_right (h : b₁ ≤ b₂) : IccCat a b₁ ⊆ IccCat a b₂ :=
  Icc_subset_Icc le_rfl h

theorem Icc_subset_Ioo (ha : a₂ < a₁) (hb : b₁ < b₂) : IccCat a₁ b₁ ⊆ IooCat a₂ b₂ := fun x hx =>
  ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩

theorem Icc_subset_Ici_self : IccCat a b ⊆ IciCat a := fun x => And.left

theorem Icc_subset_Iic_self : IccCat a b ⊆ IicCat b := fun x => And.right

theorem Ioc_subset_Iic_self : IocCat a b ⊆ IicCat b := fun x => And.right

theorem Ioc_subset_Ioc (h₁ : a₂ ≤ a₁) (h₂ : b₁ ≤ b₂) : IocCat a₁ b₁ ⊆ IocCat a₂ b₂ := fun x ⟨hx₁, hx₂⟩ =>
  ⟨h₁.trans_lt hx₁, hx₂.trans h₂⟩

theorem Ioc_subset_Ioc_left (h : a₁ ≤ a₂) : IocCat a₂ b ⊆ IocCat a₁ b :=
  Ioc_subset_Ioc h le_rfl

theorem Ioc_subset_Ioc_right (h : b₁ ≤ b₂) : IocCat a b₁ ⊆ IocCat a b₂ :=
  Ioc_subset_Ioc le_rfl h

theorem Ico_subset_Ioo_left (h₁ : a₁ < a₂) : IcoCat a₂ b ⊆ IooCat a₁ b := fun x => And.imp_left h₁.trans_le

theorem Ioc_subset_Ioo_right (h : b₁ < b₂) : IocCat a b₁ ⊆ IooCat a b₂ := fun x => And.imp_right fun h' => h'.trans_lt h

theorem Icc_subset_Ico_right (h₁ : b₁ < b₂) : IccCat a b₁ ⊆ IcoCat a b₂ := fun x =>
  And.imp_right fun h₂ => h₂.trans_lt h₁

theorem Ioo_subset_Ico_self : IooCat a b ⊆ IcoCat a b := fun x => And.imp_left le_of_lt

theorem Ioo_subset_Ioc_self : IooCat a b ⊆ IocCat a b := fun x => And.imp_right le_of_lt

theorem Ico_subset_Icc_self : IcoCat a b ⊆ IccCat a b := fun x => And.imp_right le_of_lt

theorem Ioc_subset_Icc_self : IocCat a b ⊆ IccCat a b := fun x => And.imp_left le_of_lt

theorem Ioo_subset_Icc_self : IooCat a b ⊆ IccCat a b :=
  Subset.trans Ioo_subset_Ico_self Ico_subset_Icc_self

theorem Ico_subset_Iio_self : IcoCat a b ⊆ IioCat b := fun x => And.right

theorem Ioo_subset_Iio_self : IooCat a b ⊆ IioCat b := fun x => And.right

theorem Ioc_subset_Ioi_self : IocCat a b ⊆ IoiCat a := fun x => And.left

theorem Ioo_subset_Ioi_self : IooCat a b ⊆ IoiCat a := fun x => And.left

theorem Ioi_subset_Ici_self : IoiCat a ⊆ IciCat a := fun x hx => le_of_lt hx

theorem Iio_subset_Iic_self : IioCat a ⊆ IicCat a := fun x hx => le_of_lt hx

theorem Ico_subset_Ici_self : IcoCat a b ⊆ IciCat a := fun x => And.left

theorem Ioi_ssubset_Ici_self : IoiCat a ⊂ IciCat a :=
  ⟨Ioi_subset_Ici_self, fun h => lt_irrefl a (h le_rfl)⟩

theorem Iio_ssubset_Iic_self : IioCat a ⊂ IicCat a :=
  @Ioi_ssubset_Ici_self αᵒᵈ _ _

theorem Icc_subset_Icc_iff (h₁ : a₁ ≤ b₁) : IccCat a₁ b₁ ⊆ IccCat a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ :=
  ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ x ⟨hx, hx'⟩ => ⟨h.trans hx, hx'.trans h'⟩⟩

theorem Icc_subset_Ioo_iff (h₁ : a₁ ≤ b₁) : IccCat a₁ b₁ ⊆ IooCat a₂ b₂ ↔ a₂ < a₁ ∧ b₁ < b₂ :=
  ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ x ⟨hx, hx'⟩ => ⟨h.trans_le hx, hx'.trans_lt h'⟩⟩

theorem Icc_subset_Ico_iff (h₁ : a₁ ≤ b₁) : IccCat a₁ b₁ ⊆ IcoCat a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ < b₂ :=
  ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ x ⟨hx, hx'⟩ => ⟨h.trans hx, hx'.trans_lt h'⟩⟩

theorem Icc_subset_Ioc_iff (h₁ : a₁ ≤ b₁) : IccCat a₁ b₁ ⊆ IocCat a₂ b₂ ↔ a₂ < a₁ ∧ b₁ ≤ b₂ :=
  ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ x ⟨hx, hx'⟩ => ⟨h.trans_le hx, hx'.trans h'⟩⟩

theorem Icc_subset_Iio_iff (h₁ : a₁ ≤ b₁) : IccCat a₁ b₁ ⊆ IioCat b₂ ↔ b₁ < b₂ :=
  ⟨fun h => h ⟨h₁, le_rfl⟩, fun h x ⟨hx, hx'⟩ => hx'.trans_lt h⟩

theorem Icc_subset_Ioi_iff (h₁ : a₁ ≤ b₁) : IccCat a₁ b₁ ⊆ IoiCat a₂ ↔ a₂ < a₁ :=
  ⟨fun h => h ⟨le_rfl, h₁⟩, fun h x ⟨hx, hx'⟩ => h.trans_le hx⟩

theorem Icc_subset_Iic_iff (h₁ : a₁ ≤ b₁) : IccCat a₁ b₁ ⊆ IicCat b₂ ↔ b₁ ≤ b₂ :=
  ⟨fun h => h ⟨h₁, le_rfl⟩, fun h x ⟨hx, hx'⟩ => hx'.trans h⟩

theorem Icc_subset_Ici_iff (h₁ : a₁ ≤ b₁) : IccCat a₁ b₁ ⊆ IciCat a₂ ↔ a₂ ≤ a₁ :=
  ⟨fun h => h ⟨le_rfl, h₁⟩, fun h x ⟨hx, hx'⟩ => h.trans hx⟩

theorem Icc_ssubset_Icc_left (hI : a₂ ≤ b₂) (ha : a₂ < a₁) (hb : b₁ ≤ b₂) : IccCat a₁ b₁ ⊂ IccCat a₂ b₂ :=
  (ssubset_iff_of_subset (Icc_subset_Icc (le_of_lt ha) hb)).mpr
    ⟨a₂, left_mem_Icc.mpr hI, not_and.mpr fun f g => lt_irrefl a₂ (ha.trans_le f)⟩

theorem Icc_ssubset_Icc_right (hI : a₂ ≤ b₂) (ha : a₂ ≤ a₁) (hb : b₁ < b₂) : IccCat a₁ b₁ ⊂ IccCat a₂ b₂ :=
  (ssubset_iff_of_subset (Icc_subset_Icc ha (le_of_lt hb))).mpr
    ⟨b₂, right_mem_Icc.mpr hI, fun f => lt_irrefl b₁ (hb.trans_le f.2)⟩

/-- If `a ≤ b`, then `(b, +∞) ⊆ (a, +∞)`. In preorders, this is just an implication. If you need
the equivalence in linear orders, use `Ioi_subset_Ioi_iff`. -/
theorem Ioi_subset_Ioi (h : a ≤ b) : IoiCat b ⊆ IoiCat a := fun x hx => h.trans_lt hx

/-- If `a ≤ b`, then `(b, +∞) ⊆ [a, +∞)`. In preorders, this is just an implication. If you need
the equivalence in dense linear orders, use `Ioi_subset_Ici_iff`. -/
theorem Ioi_subset_Ici (h : a ≤ b) : IoiCat b ⊆ IciCat a :=
  Subset.trans (Ioi_subset_Ioi h) Ioi_subset_Ici_self

/-- If `a ≤ b`, then `(-∞, a) ⊆ (-∞, b)`. In preorders, this is just an implication. If you need
the equivalence in linear orders, use `Iio_subset_Iio_iff`. -/
theorem Iio_subset_Iio (h : a ≤ b) : IioCat a ⊆ IioCat b := fun x hx => lt_of_lt_of_le hx h

/-- If `a ≤ b`, then `(-∞, a) ⊆ (-∞, b]`. In preorders, this is just an implication. If you need
the equivalence in dense linear orders, use `Iio_subset_Iic_iff`. -/
theorem Iio_subset_Iic (h : a ≤ b) : IioCat a ⊆ IicCat b :=
  Subset.trans (Iio_subset_Iio h) Iio_subset_Iic_self

theorem Ici_inter_Iic : IciCat a ∩ IicCat b = IccCat a b :=
  rfl

theorem Ici_inter_Iio : IciCat a ∩ IioCat b = IcoCat a b :=
  rfl

theorem Ioi_inter_Iic : IoiCat a ∩ IicCat b = IocCat a b :=
  rfl

theorem Ioi_inter_Iio : IoiCat a ∩ IioCat b = IooCat a b :=
  rfl

theorem Iic_inter_Ici : IicCat a ∩ IciCat b = IccCat b a :=
  inter_comm _ _

theorem Iio_inter_Ici : IioCat a ∩ IciCat b = IcoCat b a :=
  inter_comm _ _

theorem Iic_inter_Ioi : IicCat a ∩ IoiCat b = IocCat b a :=
  inter_comm _ _

theorem Iio_inter_Ioi : IioCat a ∩ IoiCat b = IooCat b a :=
  inter_comm _ _

theorem mem_Icc_of_Ioo (h : x ∈ IooCat a b) : x ∈ IccCat a b :=
  Ioo_subset_Icc_self h

theorem mem_Ico_of_Ioo (h : x ∈ IooCat a b) : x ∈ IcoCat a b :=
  Ioo_subset_Ico_self h

theorem mem_Ioc_of_Ioo (h : x ∈ IooCat a b) : x ∈ IocCat a b :=
  Ioo_subset_Ioc_self h

theorem mem_Icc_of_Ico (h : x ∈ IcoCat a b) : x ∈ IccCat a b :=
  Ico_subset_Icc_self h

theorem mem_Icc_of_Ioc (h : x ∈ IocCat a b) : x ∈ IccCat a b :=
  Ioc_subset_Icc_self h

theorem mem_Ici_of_Ioi (h : x ∈ IoiCat a) : x ∈ IciCat a :=
  Ioi_subset_Ici_self h

theorem mem_Iic_of_Iio (h : x ∈ IioCat a) : x ∈ IicCat a :=
  Iio_subset_Iic_self h

theorem Icc_eq_empty_iff : IccCat a b = ∅ ↔ ¬a ≤ b := by rw [← not_nonempty_iff_eq_empty, not_iff_not, nonempty_Icc]

theorem Ico_eq_empty_iff : IcoCat a b = ∅ ↔ ¬a < b := by rw [← not_nonempty_iff_eq_empty, not_iff_not, nonempty_Ico]

theorem Ioc_eq_empty_iff : IocCat a b = ∅ ↔ ¬a < b := by rw [← not_nonempty_iff_eq_empty, not_iff_not, nonempty_Ioc]

theorem Ioo_eq_empty_iff [DenselyOrdered α] : IooCat a b = ∅ ↔ ¬a < b := by
  rw [← not_nonempty_iff_eq_empty, not_iff_not, nonempty_Ioo]

theorem _root_.is_top.Iic_eq (h : IsTop a) : IicCat a = univ :=
  eq_univ_of_forall h

theorem _root_.is_bot.Ici_eq (h : IsBot a) : IciCat a = univ :=
  eq_univ_of_forall h

theorem _root_.is_max.Ioi_eq (h : IsMax a) : IoiCat a = ∅ :=
  eq_empty_of_subset_empty fun b => h.not_lt

theorem _root_.is_min.Iio_eq (h : IsMin a) : IioCat a = ∅ :=
  eq_empty_of_subset_empty fun b => h.not_lt

theorem Iic_inter_Ioc_of_le (h : a ≤ c) : IicCat a ∩ IocCat b c = IocCat b a :=
  ext fun x => ⟨fun H => ⟨H.2.1, H.1⟩, fun H => ⟨H.2, H.1, H.2.trans h⟩⟩

end Preorder

section PartialOrder

variable [PartialOrder α] {a b c : α}

@[simp]
theorem Icc_self (a : α) : IccCat a a = {a} :=
  Set.ext <| by simp [Icc, le_antisymm_iff, and_comm']

@[simp]
theorem Icc_eq_singleton_iff : IccCat a b = {c} ↔ a = c ∧ b = c := by
  refine' ⟨fun h => _, _⟩
  · have hab : a ≤ b := nonempty_Icc.1 (h.symm.subst <| singleton_nonempty c)
    exact ⟨eq_of_mem_singleton <| h.subst <| left_mem_Icc.2 hab, eq_of_mem_singleton <| h.subst <| right_mem_Icc.2 hab⟩
    
  · rintro ⟨rfl, rfl⟩
    exact Icc_self _
    

@[simp]
theorem Icc_diff_left : IccCat a b \ {a} = IocCat a b :=
  ext fun x => by simp [lt_iff_le_and_ne, eq_comm, and_right_comm]

@[simp]
theorem Icc_diff_right : IccCat a b \ {b} = IcoCat a b :=
  ext fun x => by simp [lt_iff_le_and_ne, and_assoc']

@[simp]
theorem Ico_diff_left : IcoCat a b \ {a} = IooCat a b :=
  ext fun x => by simp [and_right_comm, ← lt_iff_le_and_ne, eq_comm]

@[simp]
theorem Ioc_diff_right : IocCat a b \ {b} = IooCat a b :=
  ext fun x => by simp [and_assoc', ← lt_iff_le_and_ne]

@[simp]
theorem Icc_diff_both : IccCat a b \ {a, b} = IooCat a b := by
  rw [insert_eq, ← diff_diff, Icc_diff_left, Ioc_diff_right]

@[simp]
theorem Ici_diff_left : IciCat a \ {a} = IoiCat a :=
  ext fun x => by simp [lt_iff_le_and_ne, eq_comm]

@[simp]
theorem Iic_diff_right : IicCat a \ {a} = IioCat a :=
  ext fun x => by simp [lt_iff_le_and_ne]

@[simp]
theorem Ico_diff_Ioo_same (h : a < b) : IcoCat a b \ IooCat a b = {a} := by
  rw [← Ico_diff_left, diff_diff_cancel_left (singleton_subset_iff.2 <| left_mem_Ico.2 h)]

@[simp]
theorem Ioc_diff_Ioo_same (h : a < b) : IocCat a b \ IooCat a b = {b} := by
  rw [← Ioc_diff_right, diff_diff_cancel_left (singleton_subset_iff.2 <| right_mem_Ioc.2 h)]

@[simp]
theorem Icc_diff_Ico_same (h : a ≤ b) : IccCat a b \ IcoCat a b = {b} := by
  rw [← Icc_diff_right, diff_diff_cancel_left (singleton_subset_iff.2 <| right_mem_Icc.2 h)]

@[simp]
theorem Icc_diff_Ioc_same (h : a ≤ b) : IccCat a b \ IocCat a b = {a} := by
  rw [← Icc_diff_left, diff_diff_cancel_left (singleton_subset_iff.2 <| left_mem_Icc.2 h)]

@[simp]
theorem Icc_diff_Ioo_same (h : a ≤ b) : IccCat a b \ IooCat a b = {a, b} := by
  rw [← Icc_diff_both, diff_diff_cancel_left]
  simp [insert_subset, h]

@[simp]
theorem Ici_diff_Ioi_same : IciCat a \ IoiCat a = {a} := by
  rw [← Ici_diff_left, diff_diff_cancel_left (singleton_subset_iff.2 left_mem_Ici)]

@[simp]
theorem Iic_diff_Iio_same : IicCat a \ IioCat a = {a} := by
  rw [← Iic_diff_right, diff_diff_cancel_left (singleton_subset_iff.2 right_mem_Iic)]

@[simp]
theorem Ioi_union_left : IoiCat a ∪ {a} = IciCat a :=
  ext fun x => by simp [eq_comm, le_iff_eq_or_lt]

@[simp]
theorem Iio_union_right : IioCat a ∪ {a} = IicCat a :=
  ext fun x => le_iff_lt_or_eq.symm

theorem Ioo_union_left (hab : a < b) : IooCat a b ∪ {a} = IcoCat a b := by
  rw [← Ico_diff_left, diff_union_self, union_eq_self_of_subset_right (singleton_subset_iff.2 <| left_mem_Ico.2 hab)]

theorem Ioo_union_right (hab : a < b) : IooCat a b ∪ {b} = IocCat a b := by
  simpa only [dual_Ioo, dual_Ico] using Ioo_union_left hab.dual

theorem Ioc_union_left (hab : a ≤ b) : IocCat a b ∪ {a} = IccCat a b := by
  rw [← Icc_diff_left, diff_union_self, union_eq_self_of_subset_right (singleton_subset_iff.2 <| left_mem_Icc.2 hab)]

theorem Ico_union_right (hab : a ≤ b) : IcoCat a b ∪ {b} = IccCat a b := by
  simpa only [dual_Ioc, dual_Icc] using Ioc_union_left hab.dual

@[simp]
theorem Ico_insert_right (h : a ≤ b) : insert b (IcoCat a b) = IccCat a b := by
  rw [insert_eq, union_comm, Ico_union_right h]

@[simp]
theorem Ioc_insert_left (h : a ≤ b) : insert a (IocCat a b) = IccCat a b := by
  rw [insert_eq, union_comm, Ioc_union_left h]

@[simp]
theorem Ioo_insert_left (h : a < b) : insert a (IooCat a b) = IcoCat a b := by
  rw [insert_eq, union_comm, Ioo_union_left h]

@[simp]
theorem Ioo_insert_right (h : a < b) : insert b (IooCat a b) = IocCat a b := by
  rw [insert_eq, union_comm, Ioo_union_right h]

@[simp]
theorem Iio_insert : insert a (IioCat a) = IicCat a :=
  ext fun _ => le_iff_eq_or_lt.symm

@[simp]
theorem Ioi_insert : insert a (IoiCat a) = IciCat a :=
  ext fun _ => (or_congr_left eq_comm).trans le_iff_eq_or_lt.symm

theorem mem_Ici_Ioi_of_subset_of_subset {s : Set α} (ho : IoiCat a ⊆ s) (hc : s ⊆ IciCat a) :
    s ∈ ({IciCat a, IoiCat a} : Set (Set α)) :=
  Classical.by_cases
    (fun h : a ∈ s => Or.inl <| Subset.antisymm hc <| by rw [← Ioi_union_left, union_subset_iff] <;> simp [*]) fun h =>
    Or.inr <| Subset.antisymm (fun x hx => lt_of_le_of_ne (hc hx) fun heq => h <| HEq.symm ▸ hx) ho

theorem mem_Iic_Iio_of_subset_of_subset {s : Set α} (ho : IioCat a ⊆ s) (hc : s ⊆ IicCat a) :
    s ∈ ({IicCat a, IioCat a} : Set (Set α)) :=
  @mem_Ici_Ioi_of_subset_of_subset αᵒᵈ _ a s ho hc

/- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:61:9: parse error -/
theorem mem_Icc_Ico_Ioc_Ioo_of_subset_of_subset {s : Set α} (ho : IooCat a b ⊆ s) (hc : s ⊆ IccCat a b) :
    s ∈ ({IccCat a b, IcoCat a b, IocCat a b, IooCat a b} : Set (Set α)) := by
  classical
  by_cases ha:a ∈ s <;> by_cases hb:b ∈ s
  · refine' Or.inl (subset.antisymm hc _)
    rwa [← Ico_diff_left, diff_singleton_subset_iff, insert_eq_of_mem ha, ← Icc_diff_right, diff_singleton_subset_iff,
      insert_eq_of_mem hb] at ho
    
  · refine' Or.inr <| Or.inl <| subset.antisymm _ _
    · rw [← Icc_diff_right]
      exact subset_diff_singleton hc hb
      
    · rwa [← Ico_diff_left, diff_singleton_subset_iff, insert_eq_of_mem ha] at ho
      
    
  · refine' Or.inr <| Or.inr <| Or.inl <| subset.antisymm _ _
    · rw [← Icc_diff_left]
      exact subset_diff_singleton hc ha
      
    · rwa [← Ioc_diff_right, diff_singleton_subset_iff, insert_eq_of_mem hb] at ho
      
    
  · refine' Or.inr <| Or.inr <| Or.inr <| subset.antisymm _ ho
    rw [← Ico_diff_left, ← Icc_diff_right]
    apply_rules [subset_diff_singleton]
    

theorem eq_left_or_mem_Ioo_of_mem_Ico {x : α} (hmem : x ∈ IcoCat a b) : x = a ∨ x ∈ IooCat a b :=
  hmem.1.eq_or_gt.imp_right fun h => ⟨h, hmem.2⟩

theorem eq_right_or_mem_Ioo_of_mem_Ioc {x : α} (hmem : x ∈ IocCat a b) : x = b ∨ x ∈ IooCat a b :=
  hmem.2.eq_or_lt.imp_right <| And.intro hmem.1

theorem eq_endpoints_or_mem_Ioo_of_mem_Icc {x : α} (hmem : x ∈ IccCat a b) : x = a ∨ x = b ∨ x ∈ IooCat a b :=
  hmem.1.eq_or_gt.imp_right fun h => eq_right_or_mem_Ioo_of_mem_Ioc ⟨h, hmem.2⟩

theorem _root_.is_max.Ici_eq (h : IsMax a) : IciCat a = {a} :=
  eq_singleton_iff_unique_mem.2 ⟨left_mem_Ici, fun b => h.eq_of_ge⟩

theorem _root_.is_min.Iic_eq (h : IsMin a) : IicCat a = {a} :=
  h.toDual.Ici_eq

theorem Ici_injective : Injective (IciCat : α → Set α) := fun a b => eq_of_forall_ge_iff ∘ Set.ext_iff.1

theorem Iic_injective : Injective (IicCat : α → Set α) := fun a b => eq_of_forall_le_iff ∘ Set.ext_iff.1

theorem Ici_inj : IciCat a = IciCat b ↔ a = b :=
  Ici_injective.eq_iff

theorem Iic_inj : IicCat a = IicCat b ↔ a = b :=
  Iic_injective.eq_iff

end PartialOrder

section OrderTop

@[simp]
theorem Ici_top [PartialOrder α] [OrderTop α] : IciCat (⊤ : α) = {⊤} :=
  is_max_top.Ici_eq

variable [Preorder α] [OrderTop α] {a : α}

@[simp]
theorem Ioi_top : IoiCat (⊤ : α) = ∅ :=
  is_max_top.Ioi_eq

@[simp]
theorem Iic_top : IicCat (⊤ : α) = univ :=
  is_top_top.Iic_eq

@[simp]
theorem Icc_top : IccCat a ⊤ = IciCat a := by simp [← Ici_inter_Iic]

@[simp]
theorem Ioc_top : IocCat a ⊤ = IoiCat a := by simp [← Ioi_inter_Iic]

end OrderTop

section OrderBot

@[simp]
theorem Iic_bot [PartialOrder α] [OrderBot α] : IicCat (⊥ : α) = {⊥} :=
  is_min_bot.Iic_eq

variable [Preorder α] [OrderBot α] {a : α}

@[simp]
theorem Iio_bot : IioCat (⊥ : α) = ∅ :=
  is_min_bot.Iio_eq

@[simp]
theorem Ici_bot : IciCat (⊥ : α) = univ :=
  is_bot_bot.Ici_eq

@[simp]
theorem Icc_bot : IccCat ⊥ a = IicCat a := by simp [← Ici_inter_Iic]

@[simp]
theorem Ico_bot : IcoCat ⊥ a = IioCat a := by simp [← Ici_inter_Iio]

end OrderBot

theorem Icc_bot_top [PartialOrder α] [BoundedOrder α] : IccCat (⊥ : α) ⊤ = univ := by simp

section LinearOrder

variable [LinearOrder α] {a a₁ a₂ b b₁ b₂ c d : α}

theorem not_mem_Ici : c ∉ IciCat a ↔ c < a :=
  not_le

theorem not_mem_Iic : c ∉ IicCat b ↔ b < c :=
  not_le

theorem not_mem_Icc_of_lt (ha : c < a) : c ∉ IccCat a b :=
  not_mem_subset Icc_subset_Ici_self <| not_mem_Ici.mpr ha

theorem not_mem_Icc_of_gt (hb : b < c) : c ∉ IccCat a b :=
  not_mem_subset Icc_subset_Iic_self <| not_mem_Iic.mpr hb

theorem not_mem_Ico_of_lt (ha : c < a) : c ∉ IcoCat a b :=
  not_mem_subset Ico_subset_Ici_self <| not_mem_Ici.mpr ha

theorem not_mem_Ioc_of_gt (hb : b < c) : c ∉ IocCat a b :=
  not_mem_subset Ioc_subset_Iic_self <| not_mem_Iic.mpr hb

theorem not_mem_Ioi : c ∉ IoiCat a ↔ c ≤ a :=
  not_lt

theorem not_mem_Iio : c ∉ IioCat b ↔ b ≤ c :=
  not_lt

theorem not_mem_Ioc_of_le (ha : c ≤ a) : c ∉ IocCat a b :=
  not_mem_subset Ioc_subset_Ioi_self <| not_mem_Ioi.mpr ha

theorem not_mem_Ico_of_ge (hb : b ≤ c) : c ∉ IcoCat a b :=
  not_mem_subset Ico_subset_Iio_self <| not_mem_Iio.mpr hb

theorem not_mem_Ioo_of_le (ha : c ≤ a) : c ∉ IooCat a b :=
  not_mem_subset Ioo_subset_Ioi_self <| not_mem_Ioi.mpr ha

theorem not_mem_Ioo_of_ge (hb : b ≤ c) : c ∉ IooCat a b :=
  not_mem_subset Ioo_subset_Iio_self <| not_mem_Iio.mpr hb

@[simp]
theorem compl_Iic : IicCat aᶜ = IoiCat a :=
  ext fun _ => not_le

@[simp]
theorem compl_Ici : IciCat aᶜ = IioCat a :=
  ext fun _ => not_le

@[simp]
theorem compl_Iio : IioCat aᶜ = IciCat a :=
  ext fun _ => not_lt

@[simp]
theorem compl_Ioi : IoiCat aᶜ = IicCat a :=
  ext fun _ => not_lt

@[simp]
theorem Ici_diff_Ici : IciCat a \ IciCat b = IcoCat a b := by rw [diff_eq, compl_Ici, Ici_inter_Iio]

@[simp]
theorem Ici_diff_Ioi : IciCat a \ IoiCat b = IccCat a b := by rw [diff_eq, compl_Ioi, Ici_inter_Iic]

@[simp]
theorem Ioi_diff_Ioi : IoiCat a \ IoiCat b = IocCat a b := by rw [diff_eq, compl_Ioi, Ioi_inter_Iic]

@[simp]
theorem Ioi_diff_Ici : IoiCat a \ IciCat b = IooCat a b := by rw [diff_eq, compl_Ici, Ioi_inter_Iio]

@[simp]
theorem Iic_diff_Iic : IicCat b \ IicCat a = IocCat a b := by rw [diff_eq, compl_Iic, inter_comm, Ioi_inter_Iic]

@[simp]
theorem Iio_diff_Iic : IioCat b \ IicCat a = IooCat a b := by rw [diff_eq, compl_Iic, inter_comm, Ioi_inter_Iio]

@[simp]
theorem Iic_diff_Iio : IicCat b \ IioCat a = IccCat a b := by rw [diff_eq, compl_Iio, inter_comm, Ici_inter_Iic]

@[simp]
theorem Iio_diff_Iio : IioCat b \ IioCat a = IcoCat a b := by rw [diff_eq, compl_Iio, inter_comm, Ici_inter_Iio]

theorem Ioi_injective : Injective (IoiCat : α → Set α) := fun a b => eq_of_forall_gt_iff ∘ Set.ext_iff.1

theorem Iio_injective : Injective (IioCat : α → Set α) := fun a b => eq_of_forall_lt_iff ∘ Set.ext_iff.1

theorem Ioi_inj : IoiCat a = IoiCat b ↔ a = b :=
  Ioi_injective.eq_iff

theorem Iio_inj : IioCat a = IioCat b ↔ a = b :=
  Iio_injective.eq_iff

theorem Ico_subset_Ico_iff (h₁ : a₁ < b₁) : IcoCat a₁ b₁ ⊆ IcoCat a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ :=
  ⟨fun h =>
    have : a₂ ≤ a₁ ∧ a₁ < b₂ := h ⟨le_rfl, h₁⟩
    ⟨this.1, le_of_not_lt fun h' => lt_irrefl b₂ (h ⟨this.2.le, h'⟩).2⟩,
    fun ⟨h₁, h₂⟩ => Ico_subset_Ico h₁ h₂⟩

theorem Ioc_subset_Ioc_iff (h₁ : a₁ < b₁) : IocCat a₁ b₁ ⊆ IocCat a₂ b₂ ↔ b₁ ≤ b₂ ∧ a₂ ≤ a₁ := by
  convert @Ico_subset_Ico_iff αᵒᵈ _ b₁ b₂ a₁ a₂ h₁ <;> exact (@dual_Ico α _ _ _).symm

theorem Ioo_subset_Ioo_iff [DenselyOrdered α] (h₁ : a₁ < b₁) : IooCat a₁ b₁ ⊆ IooCat a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ :=
  ⟨fun h => by
    rcases exists_between h₁ with ⟨x, xa, xb⟩
    constructor <;> refine' le_of_not_lt fun h' => _
    · have ab := (h ⟨xa, xb⟩).1.trans xb
      exact lt_irrefl _ (h ⟨h', ab⟩).1
      
    · have ab := xa.trans (h ⟨xa, xb⟩).2
      exact lt_irrefl _ (h ⟨ab, h'⟩).2
      ,
    fun ⟨h₁, h₂⟩ => Ioo_subset_Ioo h₁ h₂⟩

theorem Ico_eq_Ico_iff (h : a₁ < b₁ ∨ a₂ < b₂) : IcoCat a₁ b₁ = IcoCat a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ :=
  ⟨fun e => by
    simp [subset.antisymm_iff] at e
    simp [le_antisymm_iff]
    cases h <;>
      simp [Ico_subset_Ico_iff h] at e <;> [rcases e with ⟨⟨h₁, h₂⟩, e'⟩, rcases e with ⟨e', ⟨h₁, h₂⟩⟩] <;>
        have := (Ico_subset_Ico_iff <| h₁.trans_lt <| h.trans_le h₂).1 e' <;> tauto,
    fun ⟨h₁, h₂⟩ => by rw [h₁, h₂]⟩

open Classical

@[simp]
theorem Ioi_subset_Ioi_iff : IoiCat b ⊆ IoiCat a ↔ a ≤ b := by
  refine' ⟨fun h => _, fun h => Ioi_subset_Ioi h⟩
  by_contra ba
  exact lt_irrefl _ (h (not_le.mp ba))

@[simp]
theorem Ioi_subset_Ici_iff [DenselyOrdered α] : IoiCat b ⊆ IciCat a ↔ a ≤ b := by
  refine' ⟨fun h => _, fun h => Ioi_subset_Ici h⟩
  by_contra ba
  obtain ⟨c, bc, ca⟩ : ∃ c, b < c ∧ c < a := exists_between (not_le.mp ba)
  exact lt_irrefl _ (ca.trans_le (h bc))

@[simp]
theorem Iio_subset_Iio_iff : IioCat a ⊆ IioCat b ↔ a ≤ b := by
  refine' ⟨fun h => _, fun h => Iio_subset_Iio h⟩
  by_contra ab
  exact lt_irrefl _ (h (not_le.mp ab))

@[simp]
theorem Iio_subset_Iic_iff [DenselyOrdered α] : IioCat a ⊆ IicCat b ↔ a ≤ b := by
  rw [← diff_eq_empty, Iio_diff_Iic, Ioo_eq_empty_iff, not_lt]

/-! ### Unions of adjacent intervals -/


/-! #### Two infinite intervals -/


theorem Iic_union_Ioi_of_le (h : a ≤ b) : IicCat b ∪ IoiCat a = univ :=
  eq_univ_of_forall fun x => (h.lt_or_le x).symm

theorem Iio_union_Ici_of_le (h : a ≤ b) : IioCat b ∪ IciCat a = univ :=
  eq_univ_of_forall fun x => (h.le_or_lt x).symm

theorem Iic_union_Ici_of_le (h : a ≤ b) : IicCat b ∪ IciCat a = univ :=
  eq_univ_of_forall fun x => (h.le_or_le x).symm

theorem Iio_union_Ioi_of_lt (h : a < b) : IioCat b ∪ IoiCat a = univ :=
  eq_univ_of_forall fun x => (h.lt_or_lt x).symm

@[simp]
theorem Iic_union_Ici : IicCat a ∪ IciCat a = univ :=
  Iic_union_Ici_of_le le_rfl

@[simp]
theorem Iio_union_Ici : IioCat a ∪ IciCat a = univ :=
  Iio_union_Ici_of_le le_rfl

@[simp]
theorem Iic_union_Ioi : IicCat a ∪ IoiCat a = univ :=
  Iic_union_Ioi_of_le le_rfl

@[simp]
theorem Iio_union_Ioi : IioCat a ∪ IoiCat a = {a}ᶜ :=
  ext fun x => lt_or_lt_iff_ne

/-! #### A finite and an infinite interval -/


theorem Ioo_union_Ioi' (h₁ : c < b) : IooCat a b ∪ IoiCat c = IoiCat (min a c) := by
  ext1 x
  simp_rw [mem_union, mem_Ioo, mem_Ioi, min_lt_iff]
  by_cases hc:c < x
  · tauto
    
  · have hxb : x < b := (le_of_not_gt hc).trans_lt h₁
    tauto
    

theorem Ioo_union_Ioi (h : c < max a b) : IooCat a b ∪ IoiCat c = IoiCat (min a c) := by
  cases' le_total a b with hab hab <;> simp [hab] at h
  · exact Ioo_union_Ioi' h
    
  · rw [min_comm]
    simp [*, min_eq_left_of_lt]
    

theorem Ioi_subset_Ioo_union_Ici : IoiCat a ⊆ IooCat a b ∪ IciCat b := fun x hx =>
  (lt_or_le x b).elim (fun hxb => Or.inl ⟨hx, hxb⟩) fun hxb => Or.inr hxb

@[simp]
theorem Ioo_union_Ici_eq_Ioi (h : a < b) : IooCat a b ∪ IciCat b = IoiCat a :=
  Subset.antisymm (fun x hx => hx.elim And.left h.trans_le) Ioi_subset_Ioo_union_Ici

theorem Ici_subset_Ico_union_Ici : IciCat a ⊆ IcoCat a b ∪ IciCat b := fun x hx =>
  (lt_or_le x b).elim (fun hxb => Or.inl ⟨hx, hxb⟩) fun hxb => Or.inr hxb

@[simp]
theorem Ico_union_Ici_eq_Ici (h : a ≤ b) : IcoCat a b ∪ IciCat b = IciCat a :=
  Subset.antisymm (fun x hx => hx.elim And.left h.trans) Ici_subset_Ico_union_Ici

theorem Ico_union_Ici' (h₁ : c ≤ b) : IcoCat a b ∪ IciCat c = IciCat (min a c) := by
  ext1 x
  simp_rw [mem_union, mem_Ico, mem_Ici, min_le_iff]
  by_cases hc:c ≤ x
  · tauto
    
  · have hxb : x < b := (lt_of_not_ge hc).trans_le h₁
    tauto
    

theorem Ico_union_Ici (h : c ≤ max a b) : IcoCat a b ∪ IciCat c = IciCat (min a c) := by
  cases' le_total a b with hab hab <;> simp [hab] at h
  · exact Ico_union_Ici' h
    
  · simp [*]
    

theorem Ioi_subset_Ioc_union_Ioi : IoiCat a ⊆ IocCat a b ∪ IoiCat b := fun x hx =>
  (le_or_lt x b).elim (fun hxb => Or.inl ⟨hx, hxb⟩) fun hxb => Or.inr hxb

@[simp]
theorem Ioc_union_Ioi_eq_Ioi (h : a ≤ b) : IocCat a b ∪ IoiCat b = IoiCat a :=
  Subset.antisymm (fun x hx => hx.elim And.left h.trans_lt) Ioi_subset_Ioc_union_Ioi

theorem Ioc_union_Ioi' (h₁ : c ≤ b) : IocCat a b ∪ IoiCat c = IoiCat (min a c) := by
  ext1 x
  simp_rw [mem_union, mem_Ioc, mem_Ioi, min_lt_iff]
  by_cases hc:c < x
  · tauto
    
  · have hxb : x ≤ b := (le_of_not_gt hc).trans h₁
    tauto
    

theorem Ioc_union_Ioi (h : c ≤ max a b) : IocCat a b ∪ IoiCat c = IoiCat (min a c) := by
  cases' le_total a b with hab hab <;> simp [hab] at h
  · exact Ioc_union_Ioi' h
    
  · simp [*]
    

theorem Ici_subset_Icc_union_Ioi : IciCat a ⊆ IccCat a b ∪ IoiCat b := fun x hx =>
  (le_or_lt x b).elim (fun hxb => Or.inl ⟨hx, hxb⟩) fun hxb => Or.inr hxb

@[simp]
theorem Icc_union_Ioi_eq_Ici (h : a ≤ b) : IccCat a b ∪ IoiCat b = IciCat a :=
  Subset.antisymm (fun x hx => (hx.elim And.left) fun hx' => h.trans <| le_of_lt hx') Ici_subset_Icc_union_Ioi

theorem Ioi_subset_Ioc_union_Ici : IoiCat a ⊆ IocCat a b ∪ IciCat b :=
  Subset.trans Ioi_subset_Ioo_union_Ici (union_subset_union_left _ Ioo_subset_Ioc_self)

@[simp]
theorem Ioc_union_Ici_eq_Ioi (h : a < b) : IocCat a b ∪ IciCat b = IoiCat a :=
  Subset.antisymm (fun x hx => hx.elim And.left h.trans_le) Ioi_subset_Ioc_union_Ici

theorem Ici_subset_Icc_union_Ici : IciCat a ⊆ IccCat a b ∪ IciCat b :=
  Subset.trans Ici_subset_Ico_union_Ici (union_subset_union_left _ Ico_subset_Icc_self)

@[simp]
theorem Icc_union_Ici_eq_Ici (h : a ≤ b) : IccCat a b ∪ IciCat b = IciCat a :=
  Subset.antisymm (fun x hx => hx.elim And.left h.trans) Ici_subset_Icc_union_Ici

theorem Icc_union_Ici' (h₁ : c ≤ b) : IccCat a b ∪ IciCat c = IciCat (min a c) := by
  ext1 x
  simp_rw [mem_union, mem_Icc, mem_Ici, min_le_iff]
  by_cases hc:c ≤ x
  · tauto
    
  · have hxb : x ≤ b := (le_of_not_ge hc).trans h₁
    tauto
    

theorem Icc_union_Ici (h : c ≤ max a b) : IccCat a b ∪ IciCat c = IciCat (min a c) := by
  cases' le_or_lt a b with hab hab <;> simp [hab] at h
  · exact Icc_union_Ici' h
    
  · cases h
    · simp [*]
      
    · have hca : c ≤ a := h.trans hab.le
      simp [*]
      
    

/-! #### An infinite and a finite interval -/


theorem Iic_subset_Iio_union_Icc : IicCat b ⊆ IioCat a ∪ IccCat a b := fun x hx =>
  (lt_or_le x a).elim (fun hxa => Or.inl hxa) fun hxa => Or.inr ⟨hxa, hx⟩

@[simp]
theorem Iio_union_Icc_eq_Iic (h : a ≤ b) : IioCat a ∪ IccCat a b = IicCat b :=
  Subset.antisymm (fun x hx => hx.elim (fun hx => (le_of_lt hx).trans h) And.right) Iic_subset_Iio_union_Icc

theorem Iio_subset_Iio_union_Ico : IioCat b ⊆ IioCat a ∪ IcoCat a b := fun x hx =>
  (lt_or_le x a).elim (fun hxa => Or.inl hxa) fun hxa => Or.inr ⟨hxa, hx⟩

@[simp]
theorem Iio_union_Ico_eq_Iio (h : a ≤ b) : IioCat a ∪ IcoCat a b = IioCat b :=
  Subset.antisymm (fun x hx => hx.elim (fun hx' => lt_of_lt_of_le hx' h) And.right) Iio_subset_Iio_union_Ico

theorem Iio_union_Ico' (h₁ : c ≤ b) : IioCat b ∪ IcoCat c d = IioCat (max b d) := by
  ext1 x
  simp_rw [mem_union, mem_Iio, mem_Ico, lt_max_iff]
  by_cases hc:c ≤ x
  · tauto
    
  · have hxb : x < b := (lt_of_not_ge hc).trans_le h₁
    tauto
    

theorem Iio_union_Ico (h : min c d ≤ b) : IioCat b ∪ IcoCat c d = IioCat (max b d) := by
  cases' le_total c d with hcd hcd <;> simp [hcd] at h
  · exact Iio_union_Ico' h
    
  · simp [*]
    

theorem Iic_subset_Iic_union_Ioc : IicCat b ⊆ IicCat a ∪ IocCat a b := fun x hx =>
  (le_or_lt x a).elim (fun hxa => Or.inl hxa) fun hxa => Or.inr ⟨hxa, hx⟩

@[simp]
theorem Iic_union_Ioc_eq_Iic (h : a ≤ b) : IicCat a ∪ IocCat a b = IicCat b :=
  Subset.antisymm (fun x hx => hx.elim (fun hx' => le_trans hx' h) And.right) Iic_subset_Iic_union_Ioc

theorem Iic_union_Ioc' (h₁ : c < b) : IicCat b ∪ IocCat c d = IicCat (max b d) := by
  ext1 x
  simp_rw [mem_union, mem_Iic, mem_Ioc, le_max_iff]
  by_cases hc:c < x
  · tauto
    
  · have hxb : x ≤ b := (le_of_not_gt hc).trans h₁.le
    tauto
    

theorem Iic_union_Ioc (h : min c d < b) : IicCat b ∪ IocCat c d = IicCat (max b d) := by
  cases' le_total c d with hcd hcd <;> simp [hcd] at h
  · exact Iic_union_Ioc' h
    
  · rw [max_comm]
    simp [*, max_eq_right_of_lt h]
    

theorem Iio_subset_Iic_union_Ioo : IioCat b ⊆ IicCat a ∪ IooCat a b := fun x hx =>
  (le_or_lt x a).elim (fun hxa => Or.inl hxa) fun hxa => Or.inr ⟨hxa, hx⟩

@[simp]
theorem Iic_union_Ioo_eq_Iio (h : a < b) : IicCat a ∪ IooCat a b = IioCat b :=
  Subset.antisymm (fun x hx => hx.elim (fun hx' => lt_of_le_of_lt hx' h) And.right) Iio_subset_Iic_union_Ioo

theorem Iio_union_Ioo' (h₁ : c < b) : IioCat b ∪ IooCat c d = IioCat (max b d) := by
  ext x
  cases' lt_or_le x b with hba hba
  · simp [hba, h₁]
    
  · simp only [mem_Iio, mem_union, mem_Ioo, lt_max_iff]
    refine' or_congr Iff.rfl ⟨And.right, _⟩
    exact fun h₂ => ⟨h₁.trans_le hba, h₂⟩
    

theorem Iio_union_Ioo (h : min c d < b) : IioCat b ∪ IooCat c d = IioCat (max b d) := by
  cases' le_total c d with hcd hcd <;> simp [hcd] at h
  · exact Iio_union_Ioo' h
    
  · rw [max_comm]
    simp [*, max_eq_right_of_lt h]
    

theorem Iic_subset_Iic_union_Icc : IicCat b ⊆ IicCat a ∪ IccCat a b :=
  Subset.trans Iic_subset_Iic_union_Ioc (union_subset_union_right _ Ioc_subset_Icc_self)

@[simp]
theorem Iic_union_Icc_eq_Iic (h : a ≤ b) : IicCat a ∪ IccCat a b = IicCat b :=
  Subset.antisymm (fun x hx => hx.elim (fun hx' => le_trans hx' h) And.right) Iic_subset_Iic_union_Icc

theorem Iic_union_Icc' (h₁ : c ≤ b) : IicCat b ∪ IccCat c d = IicCat (max b d) := by
  ext1 x
  simp_rw [mem_union, mem_Iic, mem_Icc, le_max_iff]
  by_cases hc:c ≤ x
  · tauto
    
  · have hxb : x ≤ b := (le_of_not_ge hc).trans h₁
    tauto
    

theorem Iic_union_Icc (h : min c d ≤ b) : IicCat b ∪ IccCat c d = IicCat (max b d) := by
  cases' le_or_lt c d with hcd hcd <;> simp [hcd] at h
  · exact Iic_union_Icc' h
    
  · cases h
    · have hdb : d ≤ b := hcd.le.trans h
      simp [*]
      
    · simp [*]
      
    

theorem Iio_subset_Iic_union_Ico : IioCat b ⊆ IicCat a ∪ IcoCat a b :=
  Subset.trans Iio_subset_Iic_union_Ioo (union_subset_union_right _ Ioo_subset_Ico_self)

@[simp]
theorem Iic_union_Ico_eq_Iio (h : a < b) : IicCat a ∪ IcoCat a b = IioCat b :=
  Subset.antisymm (fun x hx => hx.elim (fun hx' => lt_of_le_of_lt hx' h) And.right) Iio_subset_Iic_union_Ico

/-! #### Two finite intervals, `I?o` and `Ic?` -/


theorem Ioo_subset_Ioo_union_Ico : IooCat a c ⊆ IooCat a b ∪ IcoCat b c := fun x hx =>
  (lt_or_le x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
theorem Ioo_union_Ico_eq_Ioo (h₁ : a < b) (h₂ : b ≤ c) : IooCat a b ∪ IcoCat b c = IooCat a c :=
  Subset.antisymm (fun x hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_le h₂⟩) fun hx => ⟨h₁.trans_le hx.1, hx.2⟩)
    Ioo_subset_Ioo_union_Ico

theorem Ico_subset_Ico_union_Ico : IcoCat a c ⊆ IcoCat a b ∪ IcoCat b c := fun x hx =>
  (lt_or_le x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
theorem Ico_union_Ico_eq_Ico (h₁ : a ≤ b) (h₂ : b ≤ c) : IcoCat a b ∪ IcoCat b c = IcoCat a c :=
  Subset.antisymm (fun x hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_le h₂⟩) fun hx => ⟨h₁.trans hx.1, hx.2⟩)
    Ico_subset_Ico_union_Ico

theorem Ico_union_Ico' (h₁ : c ≤ b) (h₂ : a ≤ d) : IcoCat a b ∪ IcoCat c d = IcoCat (min a c) (max b d) := by
  ext1 x
  simp_rw [mem_union, mem_Ico, min_le_iff, lt_max_iff]
  by_cases hc:c ≤ x <;> by_cases hd:x < d
  · tauto
    
  · have hax : a ≤ x := h₂.trans (le_of_not_gt hd)
    tauto
    
  · have hxb : x < b := (lt_of_not_ge hc).trans_le h₁
    tauto
    
  · tauto
    

theorem Ico_union_Ico (h₁ : min a b ≤ max c d) (h₂ : min c d ≤ max a b) :
    IcoCat a b ∪ IcoCat c d = IcoCat (min a c) (max b d) := by
  cases' le_total a b with hab hab <;> cases' le_total c d with hcd hcd <;> simp [hab, hcd] at h₁ h₂
  · exact Ico_union_Ico' h₂ h₁
    
  all_goals simp [*]

theorem Icc_subset_Ico_union_Icc : IccCat a c ⊆ IcoCat a b ∪ IccCat b c := fun x hx =>
  (lt_or_le x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
theorem Ico_union_Icc_eq_Icc (h₁ : a ≤ b) (h₂ : b ≤ c) : IcoCat a b ∪ IccCat b c = IccCat a c :=
  Subset.antisymm (fun x hx => hx.elim (fun hx => ⟨hx.1, hx.2.le.trans h₂⟩) fun hx => ⟨h₁.trans hx.1, hx.2⟩)
    Icc_subset_Ico_union_Icc

theorem Ioc_subset_Ioo_union_Icc : IocCat a c ⊆ IooCat a b ∪ IccCat b c := fun x hx =>
  (lt_or_le x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
theorem Ioo_union_Icc_eq_Ioc (h₁ : a < b) (h₂ : b ≤ c) : IooCat a b ∪ IccCat b c = IocCat a c :=
  Subset.antisymm (fun x hx => hx.elim (fun hx => ⟨hx.1, hx.2.le.trans h₂⟩) fun hx => ⟨h₁.trans_le hx.1, hx.2⟩)
    Ioc_subset_Ioo_union_Icc

/-! #### Two finite intervals, `I?c` and `Io?` -/


theorem Ioo_subset_Ioc_union_Ioo : IooCat a c ⊆ IocCat a b ∪ IooCat b c := fun x hx =>
  (le_or_lt x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
theorem Ioc_union_Ioo_eq_Ioo (h₁ : a ≤ b) (h₂ : b < c) : IocCat a b ∪ IooCat b c = IooCat a c :=
  Subset.antisymm (fun x hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_lt h₂⟩) fun hx => ⟨h₁.trans_lt hx.1, hx.2⟩)
    Ioo_subset_Ioc_union_Ioo

theorem Ico_subset_Icc_union_Ioo : IcoCat a c ⊆ IccCat a b ∪ IooCat b c := fun x hx =>
  (le_or_lt x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
theorem Icc_union_Ioo_eq_Ico (h₁ : a ≤ b) (h₂ : b < c) : IccCat a b ∪ IooCat b c = IcoCat a c :=
  Subset.antisymm (fun x hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_lt h₂⟩) fun hx => ⟨h₁.trans hx.1.le, hx.2⟩)
    Ico_subset_Icc_union_Ioo

theorem Icc_subset_Icc_union_Ioc : IccCat a c ⊆ IccCat a b ∪ IocCat b c := fun x hx =>
  (le_or_lt x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
theorem Icc_union_Ioc_eq_Icc (h₁ : a ≤ b) (h₂ : b ≤ c) : IccCat a b ∪ IocCat b c = IccCat a c :=
  Subset.antisymm (fun x hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans h₂⟩) fun hx => ⟨h₁.trans hx.1.le, hx.2⟩)
    Icc_subset_Icc_union_Ioc

theorem Ioc_subset_Ioc_union_Ioc : IocCat a c ⊆ IocCat a b ∪ IocCat b c := fun x hx =>
  (le_or_lt x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
theorem Ioc_union_Ioc_eq_Ioc (h₁ : a ≤ b) (h₂ : b ≤ c) : IocCat a b ∪ IocCat b c = IocCat a c :=
  Subset.antisymm (fun x hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans h₂⟩) fun hx => ⟨h₁.trans_lt hx.1, hx.2⟩)
    Ioc_subset_Ioc_union_Ioc

theorem Ioc_union_Ioc' (h₁ : c ≤ b) (h₂ : a ≤ d) : IocCat a b ∪ IocCat c d = IocCat (min a c) (max b d) := by
  ext1 x
  simp_rw [mem_union, mem_Ioc, min_lt_iff, le_max_iff]
  by_cases hc:c < x <;> by_cases hd:x ≤ d
  · tauto
    
  · have hax : a < x := h₂.trans_lt (lt_of_not_ge hd)
    tauto
    
  · have hxb : x ≤ b := (le_of_not_gt hc).trans h₁
    tauto
    
  · tauto
    

theorem Ioc_union_Ioc (h₁ : min a b ≤ max c d) (h₂ : min c d ≤ max a b) :
    IocCat a b ∪ IocCat c d = IocCat (min a c) (max b d) := by
  cases' le_total a b with hab hab <;> cases' le_total c d with hcd hcd <;> simp [hab, hcd] at h₁ h₂
  · exact Ioc_union_Ioc' h₂ h₁
    
  all_goals simp [*]

/-! #### Two finite intervals with a common point -/


theorem Ioo_subset_Ioc_union_Ico : IooCat a c ⊆ IocCat a b ∪ IcoCat b c :=
  Subset.trans Ioo_subset_Ioc_union_Ioo (union_subset_union_right _ Ioo_subset_Ico_self)

@[simp]
theorem Ioc_union_Ico_eq_Ioo (h₁ : a < b) (h₂ : b < c) : IocCat a b ∪ IcoCat b c = IooCat a c :=
  Subset.antisymm (fun x hx => hx.elim (fun hx' => ⟨hx'.1, hx'.2.trans_lt h₂⟩) fun hx' => ⟨h₁.trans_le hx'.1, hx'.2⟩)
    Ioo_subset_Ioc_union_Ico

theorem Ico_subset_Icc_union_Ico : IcoCat a c ⊆ IccCat a b ∪ IcoCat b c :=
  Subset.trans Ico_subset_Icc_union_Ioo (union_subset_union_right _ Ioo_subset_Ico_self)

@[simp]
theorem Icc_union_Ico_eq_Ico (h₁ : a ≤ b) (h₂ : b < c) : IccCat a b ∪ IcoCat b c = IcoCat a c :=
  Subset.antisymm (fun x hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_lt h₂⟩) fun hx => ⟨h₁.trans hx.1, hx.2⟩)
    Ico_subset_Icc_union_Ico

theorem Icc_subset_Icc_union_Icc : IccCat a c ⊆ IccCat a b ∪ IccCat b c :=
  Subset.trans Icc_subset_Icc_union_Ioc (union_subset_union_right _ Ioc_subset_Icc_self)

@[simp]
theorem Icc_union_Icc_eq_Icc (h₁ : a ≤ b) (h₂ : b ≤ c) : IccCat a b ∪ IccCat b c = IccCat a c :=
  Subset.antisymm (fun x hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans h₂⟩) fun hx => ⟨h₁.trans hx.1, hx.2⟩)
    Icc_subset_Icc_union_Icc

theorem Icc_union_Icc' (h₁ : c ≤ b) (h₂ : a ≤ d) : IccCat a b ∪ IccCat c d = IccCat (min a c) (max b d) := by
  ext1 x
  simp_rw [mem_union, mem_Icc, min_le_iff, le_max_iff]
  by_cases hc:c ≤ x <;> by_cases hd:x ≤ d
  · tauto
    
  · have hax : a ≤ x := h₂.trans (le_of_not_ge hd)
    tauto
    
  · have hxb : x ≤ b := (le_of_not_ge hc).trans h₁
    tauto
    
  · tauto
    

/-- We cannot replace `<` by `≤` in the hypotheses.
Otherwise for `b < a = d < c` the l.h.s. is `∅` and the r.h.s. is `{a}`.
-/
theorem Icc_union_Icc (h₁ : min a b < max c d) (h₂ : min c d < max a b) :
    IccCat a b ∪ IccCat c d = IccCat (min a c) (max b d) := by
  cases' le_or_lt a b with hab hab <;>
    cases' le_or_lt c d with hcd hcd <;>
      simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, min_eq_left_of_lt, min_eq_right_of_lt,
        max_eq_left_of_lt, max_eq_right_of_lt, hab, hcd] at h₁ h₂
  · exact Icc_union_Icc' h₂.le h₁.le
    
  all_goals simp [*, min_eq_left_of_lt, max_eq_left_of_lt, min_eq_right_of_lt, max_eq_right_of_lt]

theorem Ioc_subset_Ioc_union_Icc : IocCat a c ⊆ IocCat a b ∪ IccCat b c :=
  Subset.trans Ioc_subset_Ioc_union_Ioc (union_subset_union_right _ Ioc_subset_Icc_self)

@[simp]
theorem Ioc_union_Icc_eq_Ioc (h₁ : a < b) (h₂ : b ≤ c) : IocCat a b ∪ IccCat b c = IocCat a c :=
  Subset.antisymm (fun x hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans h₂⟩) fun hx => ⟨h₁.trans_le hx.1, hx.2⟩)
    Ioc_subset_Ioc_union_Icc

theorem Ioo_union_Ioo' (h₁ : c < b) (h₂ : a < d) : IooCat a b ∪ IooCat c d = IooCat (min a c) (max b d) := by
  ext1 x
  simp_rw [mem_union, mem_Ioo, min_lt_iff, lt_max_iff]
  by_cases hc:c < x <;> by_cases hd:x < d
  · tauto
    
  · have hax : a < x := h₂.trans_le (le_of_not_lt hd)
    tauto
    
  · have hxb : x < b := (le_of_not_lt hc).trans_lt h₁
    tauto
    
  · tauto
    

theorem Ioo_union_Ioo (h₁ : min a b < max c d) (h₂ : min c d < max a b) :
    IooCat a b ∪ IooCat c d = IooCat (min a c) (max b d) := by
  cases' le_total a b with hab hab <;>
    cases' le_total c d with hcd hcd <;>
      simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, hab, hcd] at h₁ h₂
  · exact Ioo_union_Ioo' h₂ h₁
    
  all_goals
    simp [*, min_eq_left_of_lt, min_eq_right_of_lt, max_eq_left_of_lt, max_eq_right_of_lt, le_of_lt h₂, le_of_lt h₁]

end LinearOrder

section Lattice

section Inf

variable [SemilatticeInf α]

@[simp]
theorem Iic_inter_Iic {a b : α} : IicCat a ∩ IicCat b = IicCat (a ⊓ b) := by
  ext x
  simp [Iic]

@[simp]
theorem Ioc_inter_Iic (a b c : α) : IocCat a b ∩ IicCat c = IocCat a (b ⊓ c) := by
  rw [← Ioi_inter_Iic, ← Ioi_inter_Iic, inter_assoc, Iic_inter_Iic]

end Inf

section Sup

variable [SemilatticeSup α]

@[simp]
theorem Ici_inter_Ici {a b : α} : IciCat a ∩ IciCat b = IciCat (a ⊔ b) := by
  ext x
  simp [Ici]

@[simp]
theorem Ico_inter_Ici (a b c : α) : IcoCat a b ∩ IciCat c = IcoCat (a ⊔ c) b := by
  rw [← Ici_inter_Iio, ← Ici_inter_Iio, ← Ici_inter_Ici, inter_right_comm]

end Sup

section Both

variable [Lattice α] {a b c a₁ a₂ b₁ b₂ : α}

theorem Icc_inter_Icc : IccCat a₁ b₁ ∩ IccCat a₂ b₂ = IccCat (a₁ ⊔ a₂) (b₁ ⊓ b₂) := by
  simp only [Ici_inter_Iic.symm, Ici_inter_Ici.symm, Iic_inter_Iic.symm] <;> ac_rfl

@[simp]
theorem Icc_inter_Icc_eq_singleton (hab : a ≤ b) (hbc : b ≤ c) : IccCat a b ∩ IccCat b c = {b} := by
  rw [Icc_inter_Icc, sup_of_le_right hab, inf_of_le_left hbc, Icc_self]

end Both

end Lattice

section LinearOrder

variable [LinearOrder α] {a a₁ a₂ b b₁ b₂ c d : α}

@[simp]
theorem Ioi_inter_Ioi : IoiCat a ∩ IoiCat b = IoiCat (a ⊔ b) :=
  ext fun _ => sup_lt_iff.symm

@[simp]
theorem Iio_inter_Iio : IioCat a ∩ IioCat b = IioCat (a ⊓ b) :=
  ext fun _ => lt_inf_iff.symm

theorem Ico_inter_Ico : IcoCat a₁ b₁ ∩ IcoCat a₂ b₂ = IcoCat (a₁ ⊔ a₂) (b₁ ⊓ b₂) := by
  simp only [Ici_inter_Iio.symm, Ici_inter_Ici.symm, Iio_inter_Iio.symm] <;> ac_rfl

theorem Ioc_inter_Ioc : IocCat a₁ b₁ ∩ IocCat a₂ b₂ = IocCat (a₁ ⊔ a₂) (b₁ ⊓ b₂) := by
  simp only [Ioi_inter_Iic.symm, Ioi_inter_Ioi.symm, Iic_inter_Iic.symm] <;> ac_rfl

theorem Ioo_inter_Ioo : IooCat a₁ b₁ ∩ IooCat a₂ b₂ = IooCat (a₁ ⊔ a₂) (b₁ ⊓ b₂) := by
  simp only [Ioi_inter_Iio.symm, Ioi_inter_Ioi.symm, Iio_inter_Iio.symm] <;> ac_rfl

theorem Ioc_inter_Ioo_of_left_lt (h : b₁ < b₂) : IocCat a₁ b₁ ∩ IooCat a₂ b₂ = IocCat (max a₁ a₂) b₁ :=
  ext fun x => by simp [and_assoc', @and_left_comm (x ≤ _), and_iff_left_iff_imp.2 fun h' => lt_of_le_of_lt h' h]

theorem Ioc_inter_Ioo_of_right_le (h : b₂ ≤ b₁) : IocCat a₁ b₁ ∩ IooCat a₂ b₂ = IooCat (max a₁ a₂) b₂ :=
  ext fun x => by simp [and_assoc', @and_left_comm (x ≤ _), and_iff_right_iff_imp.2 fun h' => (le_of_lt h').trans h]

theorem Ioo_inter_Ioc_of_left_le (h : b₁ ≤ b₂) : IooCat a₁ b₁ ∩ IocCat a₂ b₂ = IooCat (max a₁ a₂) b₁ := by
  rw [inter_comm, Ioc_inter_Ioo_of_right_le h, max_comm]

theorem Ioo_inter_Ioc_of_right_lt (h : b₂ < b₁) : IooCat a₁ b₁ ∩ IocCat a₂ b₂ = IocCat (max a₁ a₂) b₂ := by
  rw [inter_comm, Ioc_inter_Ioo_of_left_lt h, max_comm]

@[simp]
theorem Ico_diff_Iio : IcoCat a b \ IioCat c = IcoCat (max a c) b := by
  rw [diff_eq, compl_Iio, Ico_inter_Ici, sup_eq_max]

@[simp]
theorem Ioc_diff_Ioi : IocCat a b \ IoiCat c = IocCat a (min b c) :=
  ext <| by simp (config := { contextual := true }) [iff_def]

@[simp]
theorem Ioc_inter_Ioi : IocCat a b ∩ IoiCat c = IocCat (a ⊔ c) b := by
  rw [← Ioi_inter_Iic, inter_assoc, inter_comm, inter_assoc, Ioi_inter_Ioi, inter_comm, Ioi_inter_Iic, sup_comm]

@[simp]
theorem Ico_inter_Iio : IcoCat a b ∩ IioCat c = IcoCat a (min b c) :=
  ext <| by simp (config := { contextual := true }) [iff_def]

@[simp]
theorem Ioc_diff_Iic : IocCat a b \ IicCat c = IocCat (max a c) b := by
  rw [diff_eq, compl_Iic, Ioc_inter_Ioi, sup_eq_max]

@[simp]
theorem Ioc_union_Ioc_right : IocCat a b ∪ IocCat a c = IocCat a (max b c) := by
  rw [Ioc_union_Ioc, min_self] <;> exact (min_le_left _ _).trans (le_max_left _ _)

@[simp]
theorem Ioc_union_Ioc_left : IocCat a c ∪ IocCat b c = IocCat (min a b) c := by
  rw [Ioc_union_Ioc, max_self] <;> exact (min_le_right _ _).trans (le_max_right _ _)

@[simp]
theorem Ioc_union_Ioc_symm : IocCat a b ∪ IocCat b a = IocCat (min a b) (max a b) := by
  rw [max_comm]
  apply Ioc_union_Ioc <;> rw [max_comm] <;> exact min_le_max

@[simp]
theorem Ioc_union_Ioc_union_Ioc_cycle :
    IocCat a b ∪ IocCat b c ∪ IocCat c a = IocCat (min a (min b c)) (max a (max b c)) := by
  rw [Ioc_union_Ioc, Ioc_union_Ioc]
  ac_rfl
  all_goals
    solve_by_elim (config := { max_depth := 5 }) [min_le_of_left_le, min_le_of_right_le, le_max_of_le_left,
      le_max_of_le_right, le_refl]

end LinearOrder

/-!
### Closed intervals in `α × β`
-/


section Prod

variable [Preorder α] [Preorder β]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem Iic_prod_Iic (a : α) (b : β) : IicCat a ×ˢ IicCat b = IicCat (a, b) :=
  rfl

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem Ici_prod_Ici (a : α) (b : β) : IciCat a ×ˢ IciCat b = IciCat (a, b) :=
  rfl

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Ici_prod_eq (a : α × β) : IciCat a = IciCat a.1 ×ˢ IciCat a.2 :=
  rfl

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Iic_prod_eq (a : α × β) : IicCat a = IicCat a.1 ×ˢ IicCat a.2 :=
  rfl

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem Icc_prod_Icc (a₁ a₂ : α) (b₁ b₂ : β) : IccCat a₁ a₂ ×ˢ IccCat b₁ b₂ = IccCat (a₁, b₁) (a₂, b₂) := by
  ext ⟨x, y⟩
  simp [and_assoc, and_comm', and_left_comm]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Icc_prod_eq (a b : α × β) : IccCat a b = IccCat a.1 b.1 ×ˢ IccCat a.2 b.2 := by simp

end Prod

/-! ### Lemmas about membership of arithmetic operations -/


section OrderedCommGroup

variable [OrderedCommGroup α] {a b c d : α}

/-! `inv_mem_Ixx_iff`, `sub_mem_Ixx_iff` -/


@[to_additive]
theorem inv_mem_Icc_iff : a⁻¹ ∈ Set.IccCat c d ↔ a ∈ Set.IccCat d⁻¹ c⁻¹ :=
  (and_comm' _ _).trans <| and_congr inv_le' le_inv'

@[to_additive]
theorem inv_mem_Ico_iff : a⁻¹ ∈ Set.IcoCat c d ↔ a ∈ Set.IocCat d⁻¹ c⁻¹ :=
  (and_comm' _ _).trans <| and_congr inv_lt' le_inv'

@[to_additive]
theorem inv_mem_Ioc_iff : a⁻¹ ∈ Set.IocCat c d ↔ a ∈ Set.IcoCat d⁻¹ c⁻¹ :=
  (and_comm' _ _).trans <| and_congr inv_le' lt_inv'

@[to_additive]
theorem inv_mem_Ioo_iff : a⁻¹ ∈ Set.IooCat c d ↔ a ∈ Set.IooCat d⁻¹ c⁻¹ :=
  (and_comm' _ _).trans <| and_congr inv_lt' lt_inv'

end OrderedCommGroup

section OrderedAddCommGroup

variable [OrderedAddCommGroup α] {a b c d : α}

/-! `add_mem_Ixx_iff_left` -/


theorem add_mem_Icc_iff_left : a + b ∈ Set.IccCat c d ↔ a ∈ Set.IccCat (c - b) (d - b) :=
  (and_congr sub_le_iff_le_add le_sub_iff_add_le).symm

theorem add_mem_Ico_iff_left : a + b ∈ Set.IcoCat c d ↔ a ∈ Set.IcoCat (c - b) (d - b) :=
  (and_congr sub_le_iff_le_add lt_sub_iff_add_lt).symm

theorem add_mem_Ioc_iff_left : a + b ∈ Set.IocCat c d ↔ a ∈ Set.IocCat (c - b) (d - b) :=
  (and_congr sub_lt_iff_lt_add le_sub_iff_add_le).symm

theorem add_mem_Ioo_iff_left : a + b ∈ Set.IooCat c d ↔ a ∈ Set.IooCat (c - b) (d - b) :=
  (and_congr sub_lt_iff_lt_add lt_sub_iff_add_lt).symm

/-! `add_mem_Ixx_iff_right` -/


theorem add_mem_Icc_iff_right : a + b ∈ Set.IccCat c d ↔ b ∈ Set.IccCat (c - a) (d - a) :=
  (and_congr sub_le_iff_le_add' le_sub_iff_add_le').symm

theorem add_mem_Ico_iff_right : a + b ∈ Set.IcoCat c d ↔ b ∈ Set.IcoCat (c - a) (d - a) :=
  (and_congr sub_le_iff_le_add' lt_sub_iff_add_lt').symm

theorem add_mem_Ioc_iff_right : a + b ∈ Set.IocCat c d ↔ b ∈ Set.IocCat (c - a) (d - a) :=
  (and_congr sub_lt_iff_lt_add' le_sub_iff_add_le').symm

theorem add_mem_Ioo_iff_right : a + b ∈ Set.IooCat c d ↔ b ∈ Set.IooCat (c - a) (d - a) :=
  (and_congr sub_lt_iff_lt_add' lt_sub_iff_add_lt').symm

/-! `sub_mem_Ixx_iff_left` -/


theorem sub_mem_Icc_iff_left : a - b ∈ Set.IccCat c d ↔ a ∈ Set.IccCat (c + b) (d + b) :=
  and_congr le_sub_iff_add_le sub_le_iff_le_add

theorem sub_mem_Ico_iff_left : a - b ∈ Set.IcoCat c d ↔ a ∈ Set.IcoCat (c + b) (d + b) :=
  and_congr le_sub_iff_add_le sub_lt_iff_lt_add

theorem sub_mem_Ioc_iff_left : a - b ∈ Set.IocCat c d ↔ a ∈ Set.IocCat (c + b) (d + b) :=
  and_congr lt_sub_iff_add_lt sub_le_iff_le_add

theorem sub_mem_Ioo_iff_left : a - b ∈ Set.IooCat c d ↔ a ∈ Set.IooCat (c + b) (d + b) :=
  and_congr lt_sub_iff_add_lt sub_lt_iff_lt_add

/-! `sub_mem_Ixx_iff_right` -/


theorem sub_mem_Icc_iff_right : a - b ∈ Set.IccCat c d ↔ b ∈ Set.IccCat (a - d) (a - c) :=
  (and_comm' _ _).trans <| and_congr sub_le le_sub

theorem sub_mem_Ico_iff_right : a - b ∈ Set.IcoCat c d ↔ b ∈ Set.IocCat (a - d) (a - c) :=
  (and_comm' _ _).trans <| and_congr sub_lt le_sub

theorem sub_mem_Ioc_iff_right : a - b ∈ Set.IocCat c d ↔ b ∈ Set.IcoCat (a - d) (a - c) :=
  (and_comm' _ _).trans <| and_congr sub_le lt_sub

theorem sub_mem_Ioo_iff_right : a - b ∈ Set.IooCat c d ↔ b ∈ Set.IooCat (a - d) (a - c) :=
  (and_comm' _ _).trans <| and_congr sub_lt lt_sub

-- I think that symmetric intervals deserve attention and API: they arise all the time,
-- for instance when considering metric balls in `ℝ`.
theorem mem_Icc_iff_abs_le {R : Type _} [LinearOrderedAddCommGroup R] {x y z : R} :
    abs (x - y) ≤ z ↔ y ∈ IccCat (x - z) (x + z) :=
  abs_le.trans <| (and_comm' _ _).trans <| and_congr sub_le neg_le_sub_iff_le_add

end OrderedAddCommGroup

section LinearOrderedAddCommGroup

variable [LinearOrderedAddCommGroup α]

/-- If we remove a smaller interval from a larger, the result is nonempty -/
theorem nonempty_Ico_sdiff {x dx y dy : α} (h : dy < dx) (hx : 0 < dx) :
    Nonempty ↥(IcoCat x (x + dx) \ IcoCat y (y + dy)) := by
  cases' lt_or_le x y with h' h'
  · use x
    simp [*, not_le.2 h']
    
  · use max x (x + dy)
    simp [*, le_refl]
    

end LinearOrderedAddCommGroup

end Set

open Set

namespace OrderIso

section Preorder

variable [Preorder α] [Preorder β]

@[simp]
theorem preimage_Iic (e : α ≃o β) (b : β) : e ⁻¹' IicCat b = IicCat (e.symm b) := by
  ext x
  simp [← e.le_iff_le]

@[simp]
theorem preimage_Ici (e : α ≃o β) (b : β) : e ⁻¹' IciCat b = IciCat (e.symm b) := by
  ext x
  simp [← e.le_iff_le]

@[simp]
theorem preimage_Iio (e : α ≃o β) (b : β) : e ⁻¹' IioCat b = IioCat (e.symm b) := by
  ext x
  simp [← e.lt_iff_lt]

@[simp]
theorem preimage_Ioi (e : α ≃o β) (b : β) : e ⁻¹' IoiCat b = IoiCat (e.symm b) := by
  ext x
  simp [← e.lt_iff_lt]

@[simp]
theorem preimage_Icc (e : α ≃o β) (a b : β) : e ⁻¹' IccCat a b = IccCat (e.symm a) (e.symm b) := by
  simp [← Ici_inter_Iic]

@[simp]
theorem preimage_Ico (e : α ≃o β) (a b : β) : e ⁻¹' IcoCat a b = IcoCat (e.symm a) (e.symm b) := by
  simp [← Ici_inter_Iio]

@[simp]
theorem preimage_Ioc (e : α ≃o β) (a b : β) : e ⁻¹' IocCat a b = IocCat (e.symm a) (e.symm b) := by
  simp [← Ioi_inter_Iic]

@[simp]
theorem preimage_Ioo (e : α ≃o β) (a b : β) : e ⁻¹' IooCat a b = IooCat (e.symm a) (e.symm b) := by
  simp [← Ioi_inter_Iio]

@[simp]
theorem image_Iic (e : α ≃o β) (a : α) : e '' IicCat a = IicCat (e a) := by
  rw [e.image_eq_preimage, e.symm.preimage_Iic, e.symm_symm]

@[simp]
theorem image_Ici (e : α ≃o β) (a : α) : e '' IciCat a = IciCat (e a) :=
  e.dual.image_Iic a

@[simp]
theorem image_Iio (e : α ≃o β) (a : α) : e '' IioCat a = IioCat (e a) := by
  rw [e.image_eq_preimage, e.symm.preimage_Iio, e.symm_symm]

@[simp]
theorem image_Ioi (e : α ≃o β) (a : α) : e '' IoiCat a = IoiCat (e a) :=
  e.dual.image_Iio a

@[simp]
theorem image_Ioo (e : α ≃o β) (a b : α) : e '' IooCat a b = IooCat (e a) (e b) := by
  rw [e.image_eq_preimage, e.symm.preimage_Ioo, e.symm_symm]

@[simp]
theorem image_Ioc (e : α ≃o β) (a b : α) : e '' IocCat a b = IocCat (e a) (e b) := by
  rw [e.image_eq_preimage, e.symm.preimage_Ioc, e.symm_symm]

@[simp]
theorem image_Ico (e : α ≃o β) (a b : α) : e '' IcoCat a b = IcoCat (e a) (e b) := by
  rw [e.image_eq_preimage, e.symm.preimage_Ico, e.symm_symm]

@[simp]
theorem image_Icc (e : α ≃o β) (a b : α) : e '' IccCat a b = IccCat (e a) (e b) := by
  rw [e.image_eq_preimage, e.symm.preimage_Icc, e.symm_symm]

end Preorder

/-- Order isomorphism between `Iic (⊤ : α)` and `α` when `α` has a top element -/
def iicTop [Preorder α] [OrderTop α] : Set.IicCat (⊤ : α) ≃o α :=
  { @Equiv.subtypeUnivEquiv α (Set.IicCat (⊤ : α)) fun x => le_top with map_rel_iff' := fun x y => by rfl }

/-- Order isomorphism between `Ici (⊥ : α)` and `α` when `α` has a bottom element -/
def iciBot [Preorder α] [OrderBot α] : Set.IciCat (⊥ : α) ≃o α :=
  { @Equiv.subtypeUnivEquiv α (Set.IciCat (⊥ : α)) fun x => bot_le with map_rel_iff' := fun x y => by rfl }

end OrderIso

/-! ### Lemmas about intervals in dense orders -/


section Dense

variable (α) [Preorder α] [DenselyOrdered α] {x y : α}

instance : NoMinOrder (Set.IooCat x y) :=
  ⟨fun ⟨a, ha₁, ha₂⟩ => by
    rcases exists_between ha₁ with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, hb₁, hb₂.trans ha₂⟩, hb₂⟩⟩

instance : NoMinOrder (Set.IocCat x y) :=
  ⟨fun ⟨a, ha₁, ha₂⟩ => by
    rcases exists_between ha₁ with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, hb₁, hb₂.le.trans ha₂⟩, hb₂⟩⟩

instance : NoMinOrder (Set.IoiCat x) :=
  ⟨fun ⟨a, ha⟩ => by
    rcases exists_between ha with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, hb₁⟩, hb₂⟩⟩

instance : NoMaxOrder (Set.IooCat x y) :=
  ⟨fun ⟨a, ha₁, ha₂⟩ => by
    rcases exists_between ha₂ with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, ha₁.trans hb₁, hb₂⟩, hb₁⟩⟩

instance : NoMaxOrder (Set.IcoCat x y) :=
  ⟨fun ⟨a, ha₁, ha₂⟩ => by
    rcases exists_between ha₂ with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, ha₁.trans hb₁.le, hb₂⟩, hb₁⟩⟩

instance : NoMaxOrder (Set.IioCat x) :=
  ⟨fun ⟨a, ha⟩ => by
    rcases exists_between ha with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, hb₂⟩, hb₁⟩⟩

end Dense

