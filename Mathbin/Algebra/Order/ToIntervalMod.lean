/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathbin.Algebra.Periodic

/-!
# Reducing to an interval modulo its length

This file defines operations that reduce a number (in an `archimedean`
`linear_ordered_add_comm_group`) to a number in a given interval, modulo the length of that
interval.

## Main definitions

* `to_Ico_div a hb x` (where `hb : 0 < b`): The unique integer such that this multiple of `b`,
  added to `x`, is in `Ico a (a + b)`.
* `to_Ico_mod a hb x` (where `hb : 0 < b`): Reduce `x` to the interval `Ico a (a + b)`.
* `to_Ioc_div a hb x` (where `hb : 0 < b`): The unique integer such that this multiple of `b`,
  added to `x`, is in `Ioc a (a + b)`.
* `to_Ioc_mod a hb x` (where `hb : 0 < b`): Reduce `x` to the interval `Ioc a (a + b)`.

-/


noncomputable section

section LinearOrderedAddCommGroup

variable {α : Type _} [LinearOrderedAddCommGroup α] [Archimedean α]

/-- The unique integer such that this multiple of `b`, added to `x`, is in `Ico a (a + b)`. -/
def toIcoDiv (a : α) {b : α} (hb : 0 < b) (x : α) : ℤ :=
  (exists_unique_add_zsmul_mem_Ico hb x a).some

theorem add_to_Ico_div_zsmul_mem_Ico (a : α) {b : α} (hb : 0 < b) (x : α) :
    x + toIcoDiv a hb x • b ∈ Set.Ico a (a + b) :=
  (exists_unique_add_zsmul_mem_Ico hb x a).some_spec.1

theorem eq_to_Ico_div_of_add_zsmul_mem_Ico {a b x : α} (hb : 0 < b) {y : ℤ} (hy : x + y • b ∈ Set.Ico a (a + b)) :
    y = toIcoDiv a hb x :=
  (exists_unique_add_zsmul_mem_Ico hb x a).some_spec.2 y hy

/-- The unique integer such that this multiple of `b`, added to `x`, is in `Ioc a (a + b)`. -/
def toIocDiv (a : α) {b : α} (hb : 0 < b) (x : α) : ℤ :=
  (exists_unique_add_zsmul_mem_Ioc hb x a).some

theorem add_to_Ioc_div_zsmul_mem_Ioc (a : α) {b : α} (hb : 0 < b) (x : α) :
    x + toIocDiv a hb x • b ∈ Set.Ioc a (a + b) :=
  (exists_unique_add_zsmul_mem_Ioc hb x a).some_spec.1

theorem eq_to_Ioc_div_of_add_zsmul_mem_Ioc {a b x : α} (hb : 0 < b) {y : ℤ} (hy : x + y • b ∈ Set.Ioc a (a + b)) :
    y = toIocDiv a hb x :=
  (exists_unique_add_zsmul_mem_Ioc hb x a).some_spec.2 y hy

/-- Reduce `x` to the interval `Ico a (a + b)`. -/
def toIcoMod (a : α) {b : α} (hb : 0 < b) (x : α) : α :=
  x + toIcoDiv a hb x • b

/-- Reduce `x` to the interval `Ioc a (a + b)`. -/
def toIocMod (a : α) {b : α} (hb : 0 < b) (x : α) : α :=
  x + toIocDiv a hb x • b

theorem to_Ico_mod_mem_Ico (a : α) {b : α} (hb : 0 < b) (x : α) : toIcoMod a hb x ∈ Set.Ico a (a + b) :=
  add_to_Ico_div_zsmul_mem_Ico a hb x

theorem to_Ioc_mod_mem_Ioc (a : α) {b : α} (hb : 0 < b) (x : α) : toIocMod a hb x ∈ Set.Ioc a (a + b) :=
  add_to_Ioc_div_zsmul_mem_Ioc a hb x

theorem left_le_to_Ico_mod (a : α) {b : α} (hb : 0 < b) (x : α) : a ≤ toIcoMod a hb x :=
  (Set.mem_Ico.1 (to_Ico_mod_mem_Ico a hb x)).1

theorem left_lt_to_Ioc_mod (a : α) {b : α} (hb : 0 < b) (x : α) : a < toIocMod a hb x :=
  (Set.mem_Ioc.1 (to_Ioc_mod_mem_Ioc a hb x)).1

theorem to_Ico_mod_lt_right (a : α) {b : α} (hb : 0 < b) (x : α) : toIcoMod a hb x < a + b :=
  (Set.mem_Ico.1 (to_Ico_mod_mem_Ico a hb x)).2

theorem to_Ioc_mod_le_right (a : α) {b : α} (hb : 0 < b) (x : α) : toIocMod a hb x ≤ a + b :=
  (Set.mem_Ioc.1 (to_Ioc_mod_mem_Ioc a hb x)).2

@[simp]
theorem self_add_to_Ico_div_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) : x + toIcoDiv a hb x • b = toIcoMod a hb x :=
  rfl

@[simp]
theorem self_add_to_Ioc_div_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) : x + toIocDiv a hb x • b = toIocMod a hb x :=
  rfl

@[simp]
theorem to_Ico_div_zsmul_add_self (a : α) {b : α} (hb : 0 < b) (x : α) : toIcoDiv a hb x • b + x = toIcoMod a hb x := by
  rw [add_commₓ, toIcoMod]

@[simp]
theorem to_Ioc_div_zsmul_add_self (a : α) {b : α} (hb : 0 < b) (x : α) : toIocDiv a hb x • b + x = toIocMod a hb x := by
  rw [add_commₓ, toIocMod]

@[simp]
theorem to_Ico_mod_sub_self (a : α) {b : α} (hb : 0 < b) (x : α) : toIcoMod a hb x - x = toIcoDiv a hb x • b := by
  rw [toIcoMod, add_sub_cancel']

@[simp]
theorem to_Ioc_mod_sub_self (a : α) {b : α} (hb : 0 < b) (x : α) : toIocMod a hb x - x = toIocDiv a hb x • b := by
  rw [toIocMod, add_sub_cancel']

@[simp]
theorem self_sub_to_Ico_mod (a : α) {b : α} (hb : 0 < b) (x : α) : x - toIcoMod a hb x = -toIcoDiv a hb x • b := by
  rw [toIcoMod, sub_add_cancel', neg_smul]

@[simp]
theorem self_sub_to_Ioc_mod (a : α) {b : α} (hb : 0 < b) (x : α) : x - toIocMod a hb x = -toIocDiv a hb x • b := by
  rw [toIocMod, sub_add_cancel', neg_smul]

@[simp]
theorem to_Ico_mod_sub_to_Ico_div_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) :
    toIcoMod a hb x - toIcoDiv a hb x • b = x := by
  rw [toIcoMod, add_sub_cancel]

@[simp]
theorem to_Ioc_mod_sub_to_Ioc_div_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) :
    toIocMod a hb x - toIocDiv a hb x • b = x := by
  rw [toIocMod, add_sub_cancel]

@[simp]
theorem to_Ico_div_zsmul_sub_to_Ico_mod (a : α) {b : α} (hb : 0 < b) (x : α) :
    toIcoDiv a hb x • b - toIcoMod a hb x = -x := by
  rw [← neg_sub, to_Ico_mod_sub_to_Ico_div_zsmul]

@[simp]
theorem to_Ioc_div_zsmul_sub_to_Ioc_mod (a : α) {b : α} (hb : 0 < b) (x : α) :
    toIocDiv a hb x • b - toIocMod a hb x = -x := by
  rw [← neg_sub, to_Ioc_mod_sub_to_Ioc_div_zsmul]

theorem to_Ico_mod_eq_iff {a b x y : α} (hb : 0 < b) :
    toIcoMod a hb x = y ↔ a ≤ y ∧ y < a + b ∧ ∃ z : ℤ, y - x = z • b := by
  refine'
    ⟨fun h =>
      ⟨h ▸ left_le_to_Ico_mod a hb x, h ▸ to_Ico_mod_lt_right a hb x, toIcoDiv a hb x, h ▸ to_Ico_mod_sub_self a hb x⟩,
      fun h => _⟩
  rcases h with ⟨ha, hab, z, hz⟩
  rw [sub_eq_iff_eq_add'] at hz
  subst hz
  rw [eq_to_Ico_div_of_add_zsmul_mem_Ico hb (Set.mem_Ico.2 ⟨ha, hab⟩)]
  rfl

theorem to_Ioc_mod_eq_iff {a b x y : α} (hb : 0 < b) :
    toIocMod a hb x = y ↔ a < y ∧ y ≤ a + b ∧ ∃ z : ℤ, y - x = z • b := by
  refine'
    ⟨fun h =>
      ⟨h ▸ left_lt_to_Ioc_mod a hb x, h ▸ to_Ioc_mod_le_right a hb x, toIocDiv a hb x, h ▸ to_Ioc_mod_sub_self a hb x⟩,
      fun h => _⟩
  rcases h with ⟨ha, hab, z, hz⟩
  rw [sub_eq_iff_eq_add'] at hz
  subst hz
  rw [eq_to_Ioc_div_of_add_zsmul_mem_Ioc hb (Set.mem_Ioc.2 ⟨ha, hab⟩)]
  rfl

@[simp]
theorem to_Ico_div_apply_left (a : α) {b : α} (hb : 0 < b) : toIcoDiv a hb a = 0 := by
  refine' (eq_to_Ico_div_of_add_zsmul_mem_Ico hb _).symm
  simp [← hb]

@[simp]
theorem to_Ioc_div_apply_left (a : α) {b : α} (hb : 0 < b) : toIocDiv a hb a = 1 := by
  refine' (eq_to_Ioc_div_of_add_zsmul_mem_Ioc hb _).symm
  simp [← hb]

@[simp]
theorem to_Ico_mod_apply_left (a : α) {b : α} (hb : 0 < b) : toIcoMod a hb a = a := by
  rw [to_Ico_mod_eq_iff hb]
  refine' ⟨le_reflₓ _, lt_add_of_pos_right _ hb, 0, _⟩
  simp

@[simp]
theorem to_Ioc_mod_apply_left (a : α) {b : α} (hb : 0 < b) : toIocMod a hb a = a + b := by
  rw [to_Ioc_mod_eq_iff hb]
  refine' ⟨lt_add_of_pos_right _ hb, le_reflₓ _, 1, _⟩
  simp

theorem to_Ico_div_apply_right (a : α) {b : α} (hb : 0 < b) : toIcoDiv a hb (a + b) = -1 := by
  refine' (eq_to_Ico_div_of_add_zsmul_mem_Ico hb _).symm
  simp [← hb]

theorem to_Ioc_div_apply_right (a : α) {b : α} (hb : 0 < b) : toIocDiv a hb (a + b) = 0 := by
  refine' (eq_to_Ioc_div_of_add_zsmul_mem_Ioc hb _).symm
  simp [← hb]

theorem to_Ico_mod_apply_right (a : α) {b : α} (hb : 0 < b) : toIcoMod a hb (a + b) = a := by
  rw [to_Ico_mod_eq_iff hb]
  refine' ⟨le_reflₓ _, lt_add_of_pos_right _ hb, -1, _⟩
  simp

theorem to_Ioc_mod_apply_right (a : α) {b : α} (hb : 0 < b) : toIocMod a hb (a + b) = a + b := by
  rw [to_Ioc_mod_eq_iff hb]
  refine' ⟨lt_add_of_pos_right _ hb, le_reflₓ _, 0, _⟩
  simp

@[simp]
theorem to_Ico_div_add_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
    toIcoDiv a hb (x + m • b) = toIcoDiv a hb x - m := by
  refine' (eq_to_Ico_div_of_add_zsmul_mem_Ico hb _).symm
  convert add_to_Ico_div_zsmul_mem_Ico a hb x using 1
  simp [← sub_smul]

@[simp]
theorem to_Ioc_div_add_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
    toIocDiv a hb (x + m • b) = toIocDiv a hb x - m := by
  refine' (eq_to_Ioc_div_of_add_zsmul_mem_Ioc hb _).symm
  convert add_to_Ioc_div_zsmul_mem_Ioc a hb x using 1
  simp [← sub_smul]

@[simp]
theorem to_Ico_div_zsmul_add (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
    toIcoDiv a hb (m • b + x) = toIcoDiv a hb x - m := by
  rw [add_commₓ, to_Ico_div_add_zsmul]

@[simp]
theorem to_Ioc_div_zsmul_add (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
    toIocDiv a hb (m • b + x) = toIocDiv a hb x - m := by
  rw [add_commₓ, to_Ioc_div_add_zsmul]

@[simp]
theorem to_Ico_div_sub_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
    toIcoDiv a hb (x - m • b) = toIcoDiv a hb x + m := by
  rw [sub_eq_add_neg, ← neg_smul, to_Ico_div_add_zsmul, sub_neg_eq_add]

@[simp]
theorem to_Ioc_div_sub_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
    toIocDiv a hb (x - m • b) = toIocDiv a hb x + m := by
  rw [sub_eq_add_neg, ← neg_smul, to_Ioc_div_add_zsmul, sub_neg_eq_add]

@[simp]
theorem to_Ico_div_add_right (a : α) {b : α} (hb : 0 < b) (x : α) : toIcoDiv a hb (x + b) = toIcoDiv a hb x - 1 := by
  convert to_Ico_div_add_zsmul a hb x 1
  exact (one_zsmul _).symm

@[simp]
theorem to_Ioc_div_add_right (a : α) {b : α} (hb : 0 < b) (x : α) : toIocDiv a hb (x + b) = toIocDiv a hb x - 1 := by
  convert to_Ioc_div_add_zsmul a hb x 1
  exact (one_zsmul _).symm

@[simp]
theorem to_Ico_div_add_left (a : α) {b : α} (hb : 0 < b) (x : α) : toIcoDiv a hb (b + x) = toIcoDiv a hb x - 1 := by
  rw [add_commₓ, to_Ico_div_add_right]

@[simp]
theorem to_Ioc_div_add_left (a : α) {b : α} (hb : 0 < b) (x : α) : toIocDiv a hb (b + x) = toIocDiv a hb x - 1 := by
  rw [add_commₓ, to_Ioc_div_add_right]

@[simp]
theorem to_Ico_div_sub (a : α) {b : α} (hb : 0 < b) (x : α) : toIcoDiv a hb (x - b) = toIcoDiv a hb x + 1 := by
  convert to_Ico_div_sub_zsmul a hb x 1
  exact (one_zsmul _).symm

@[simp]
theorem to_Ioc_div_sub (a : α) {b : α} (hb : 0 < b) (x : α) : toIocDiv a hb (x - b) = toIocDiv a hb x + 1 := by
  convert to_Ioc_div_sub_zsmul a hb x 1
  exact (one_zsmul _).symm

@[simp]
theorem to_Ico_mod_add_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
    toIcoMod a hb (x + m • b) = toIcoMod a hb x := by
  rw [toIcoMod, to_Ico_div_add_zsmul, toIcoMod, sub_smul]
  abel

@[simp]
theorem to_Ioc_mod_add_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
    toIocMod a hb (x + m • b) = toIocMod a hb x := by
  rw [toIocMod, to_Ioc_div_add_zsmul, toIocMod, sub_smul]
  abel

@[simp]
theorem to_Ico_mod_zsmul_add (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
    toIcoMod a hb (m • b + x) = toIcoMod a hb x := by
  rw [add_commₓ, to_Ico_mod_add_zsmul]

@[simp]
theorem to_Ioc_mod_zsmul_add (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
    toIocMod a hb (m • b + x) = toIocMod a hb x := by
  rw [add_commₓ, to_Ioc_mod_add_zsmul]

@[simp]
theorem to_Ico_mod_sub_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
    toIcoMod a hb (x - m • b) = toIcoMod a hb x := by
  rw [sub_eq_add_neg, ← neg_smul, to_Ico_mod_add_zsmul]

@[simp]
theorem to_Ioc_mod_sub_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
    toIocMod a hb (x - m • b) = toIocMod a hb x := by
  rw [sub_eq_add_neg, ← neg_smul, to_Ioc_mod_add_zsmul]

@[simp]
theorem to_Ico_mod_add_right (a : α) {b : α} (hb : 0 < b) (x : α) : toIcoMod a hb (x + b) = toIcoMod a hb x := by
  convert to_Ico_mod_add_zsmul a hb x 1
  exact (one_zsmul _).symm

@[simp]
theorem to_Ioc_mod_add_right (a : α) {b : α} (hb : 0 < b) (x : α) : toIocMod a hb (x + b) = toIocMod a hb x := by
  convert to_Ioc_mod_add_zsmul a hb x 1
  exact (one_zsmul _).symm

@[simp]
theorem to_Ico_mod_add_left (a : α) {b : α} (hb : 0 < b) (x : α) : toIcoMod a hb (b + x) = toIcoMod a hb x := by
  rw [add_commₓ, to_Ico_mod_add_right]

@[simp]
theorem to_Ioc_mod_add_left (a : α) {b : α} (hb : 0 < b) (x : α) : toIocMod a hb (b + x) = toIocMod a hb x := by
  rw [add_commₓ, to_Ioc_mod_add_right]

@[simp]
theorem to_Ico_mod_sub (a : α) {b : α} (hb : 0 < b) (x : α) : toIcoMod a hb (x - b) = toIcoMod a hb x := by
  convert to_Ico_mod_sub_zsmul a hb x 1
  exact (one_zsmul _).symm

@[simp]
theorem to_Ioc_mod_sub (a : α) {b : α} (hb : 0 < b) (x : α) : toIocMod a hb (x - b) = toIocMod a hb x := by
  convert to_Ioc_mod_sub_zsmul a hb x 1
  exact (one_zsmul _).symm

theorem to_Ico_mod_eq_to_Ico_mod (a : α) {b x y : α} (hb : 0 < b) :
    toIcoMod a hb x = toIcoMod a hb y ↔ ∃ z : ℤ, y - x = z • b := by
  refine' ⟨fun h => ⟨toIcoDiv a hb x - toIcoDiv a hb y, _⟩, fun h => _⟩
  · conv_lhs => rw [← to_Ico_mod_sub_to_Ico_div_zsmul a hb x, ← to_Ico_mod_sub_to_Ico_div_zsmul a hb y]
    rw [h, sub_smul]
    abel
    
  · rcases h with ⟨z, hz⟩
    rw [sub_eq_iff_eq_add] at hz
    rw [hz, to_Ico_mod_zsmul_add]
    

theorem to_Ioc_mod_eq_to_Ioc_mod (a : α) {b x y : α} (hb : 0 < b) :
    toIocMod a hb x = toIocMod a hb y ↔ ∃ z : ℤ, y - x = z • b := by
  refine' ⟨fun h => ⟨toIocDiv a hb x - toIocDiv a hb y, _⟩, fun h => _⟩
  · conv_lhs => rw [← to_Ioc_mod_sub_to_Ioc_div_zsmul a hb x, ← to_Ioc_mod_sub_to_Ioc_div_zsmul a hb y]
    rw [h, sub_smul]
    abel
    
  · rcases h with ⟨z, hz⟩
    rw [sub_eq_iff_eq_add] at hz
    rw [hz, to_Ioc_mod_zsmul_add]
    

theorem to_Ico_mod_eq_self {a b x : α} (hb : 0 < b) : toIcoMod a hb x = x ↔ a ≤ x ∧ x < a + b := by
  rw [to_Ico_mod_eq_iff]
  refine' ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, 0, _⟩⟩
  simp

theorem to_Ioc_mod_eq_self {a b x : α} (hb : 0 < b) : toIocMod a hb x = x ↔ a < x ∧ x ≤ a + b := by
  rw [to_Ioc_mod_eq_iff]
  refine' ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, 0, _⟩⟩
  simp

@[simp]
theorem to_Ico_mod_to_Ico_mod (a₁ a₂ : α) {b : α} (hb : 0 < b) (x : α) :
    toIcoMod a₁ hb (toIcoMod a₂ hb x) = toIcoMod a₁ hb x := by
  rw [to_Ico_mod_eq_to_Ico_mod]
  exact ⟨-toIcoDiv a₂ hb x, self_sub_to_Ico_mod a₂ hb x⟩

@[simp]
theorem to_Ico_mod_to_Ioc_mod (a₁ a₂ : α) {b : α} (hb : 0 < b) (x : α) :
    toIcoMod a₁ hb (toIocMod a₂ hb x) = toIcoMod a₁ hb x := by
  rw [to_Ico_mod_eq_to_Ico_mod]
  exact ⟨-toIocDiv a₂ hb x, self_sub_to_Ioc_mod a₂ hb x⟩

@[simp]
theorem to_Ioc_mod_to_Ioc_mod (a₁ a₂ : α) {b : α} (hb : 0 < b) (x : α) :
    toIocMod a₁ hb (toIocMod a₂ hb x) = toIocMod a₁ hb x := by
  rw [to_Ioc_mod_eq_to_Ioc_mod]
  exact ⟨-toIocDiv a₂ hb x, self_sub_to_Ioc_mod a₂ hb x⟩

@[simp]
theorem to_Ioc_mod_to_Ico_mod (a₁ a₂ : α) {b : α} (hb : 0 < b) (x : α) :
    toIocMod a₁ hb (toIcoMod a₂ hb x) = toIocMod a₁ hb x := by
  rw [to_Ioc_mod_eq_to_Ioc_mod]
  exact ⟨-toIcoDiv a₂ hb x, self_sub_to_Ico_mod a₂ hb x⟩

theorem to_Ico_mod_periodic (a : α) {b : α} (hb : 0 < b) : Function.Periodic (toIcoMod a hb) b :=
  to_Ico_mod_add_right a hb

theorem to_Ioc_mod_periodic (a : α) {b : α} (hb : 0 < b) : Function.Periodic (toIocMod a hb) b :=
  to_Ioc_mod_add_right a hb

end LinearOrderedAddCommGroup

section LinearOrderedField

variable {α : Type _} [LinearOrderedField α] [FloorRing α]

attribute [local instance] FloorRing.archimedean

theorem to_Ico_div_eq_neg_floor (a : α) {b : α} (hb : 0 < b) (x : α) : toIcoDiv a hb x = -⌊(x - a) / b⌋ := by
  refine' (eq_to_Ico_div_of_add_zsmul_mem_Ico hb _).symm
  rw [Set.mem_Ico, zsmul_eq_mul, Int.cast_neg, neg_mul, ← sub_nonneg, add_commₓ, add_sub_assoc, add_commₓ, ←
    sub_eq_add_neg]
  refine' ⟨Int.sub_floor_div_mul_nonneg _ hb, _⟩
  rw [add_commₓ a, ← sub_lt_iff_lt_add, add_sub_assoc, add_commₓ, ← sub_eq_add_neg]
  exact Int.sub_floor_div_mul_lt _ hb

theorem to_Ioc_div_eq_floor (a : α) {b : α} (hb : 0 < b) (x : α) : toIocDiv a hb x = ⌊(a + b - x) / b⌋ := by
  refine' (eq_to_Ioc_div_of_add_zsmul_mem_Ioc hb _).symm
  rw [Set.mem_Ioc, zsmul_eq_mul, ← sub_nonneg, sub_add_eq_sub_sub]
  refine' ⟨_, Int.sub_floor_div_mul_nonneg _ hb⟩
  rw [← add_lt_add_iff_right b, add_assocₓ, add_commₓ x, ← sub_lt_iff_lt_add, add_commₓ (_ * _), ← sub_lt_iff_lt_add]
  exact Int.sub_floor_div_mul_lt _ hb

theorem to_Ico_div_zero_one (x : α) : toIcoDiv (0 : α) zero_lt_one x = -⌊x⌋ := by
  simp [← to_Ico_div_eq_neg_floor]

theorem to_Ico_mod_eq_add_fract_mul (a : α) {b : α} (hb : 0 < b) (x : α) :
    toIcoMod a hb x = a + Int.fract ((x - a) / b) * b := by
  rw [toIcoMod, to_Ico_div_eq_neg_floor, Int.fract]
  field_simp [← hb.ne.symm]
  ring

theorem to_Ioc_mod_eq_sub_fract_mul (a : α) {b : α} (hb : 0 < b) (x : α) :
    toIocMod a hb x = a + b - Int.fract ((a + b - x) / b) * b := by
  rw [toIocMod, to_Ioc_div_eq_floor, Int.fract]
  field_simp [← hb.ne.symm]
  ring

theorem to_Ico_mod_zero_one (x : α) : toIcoMod (0 : α) zero_lt_one x = Int.fract x := by
  simp [← to_Ico_mod_eq_add_fract_mul]

end LinearOrderedField

