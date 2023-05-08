/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers

! This file was ported from Lean 3 source module algebra.order.to_interval_mod
! leanprover-community/mathlib commit ba2eb7043b3799f585e466e4679dfb11fb1c53ec
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Module.Basic
import Mathbin.Algebra.Order.Archimedean
import Mathbin.Algebra.Periodic
import Mathbin.Data.Int.SuccPred
import Mathbin.GroupTheory.QuotientGroup

/-!
# Reducing to an interval modulo its length

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines operations that reduce a number (in an `archimedean`
`linear_ordered_add_comm_group`) to a number in a given interval, modulo the length of that
interval.

## Main definitions

* `to_Ico_div hp a b` (where `hp : 0 < p`): The unique integer such that this multiple of `p`,
  subtracted from `b`, is in `Ico a (a + p)`.
* `to_Ico_mod hp a b` (where `hp : 0 < p`): Reduce `b` to the interval `Ico a (a + p)`.
* `to_Ioc_div hp a b` (where `hp : 0 < p`): The unique integer such that this multiple of `p`,
  subtracted from `b`, is in `Ioc a (a + p)`.
* `to_Ioc_mod hp a b` (where `hp : 0 < p`): Reduce `b` to the interval `Ioc a (a + p)`.
* `a ≡ b [PMOD p]`: `a` and `b` are congruent modulo a multiple of `p`. See also `smodeq` which is a
  more general version in arbitrary submodules. This is notation for `add_comm_group.modeq p a b`.

## TODO

Unify `smodeq` and `add_comm_group.modeq`, which were originally developed independently.
-/


noncomputable section

section LinearOrderedAddCommGroup

variable {α : Type _} [LinearOrderedAddCommGroup α] [hα : Archimedean α] {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

include hα

/--
The unique integer such that this multiple of `p`, subtracted from `b`, is in `Ico a (a + p)`. -/
def toIcoDiv (a b : α) : ℤ :=
  (existsUnique_sub_zsmul_mem_Ico hp b a).some
#align to_Ico_div toIcoDiv

theorem sub_toIcoDiv_zsmul_mem_Ico (a b : α) : b - toIcoDiv hp a b • p ∈ Set.Ico a (a + p) :=
  (existsUnique_sub_zsmul_mem_Ico hp b a).choose_spec.1
#align sub_to_Ico_div_zsmul_mem_Ico sub_toIcoDiv_zsmul_mem_Ico

theorem toIcoDiv_eq_of_sub_zsmul_mem_Ico (h : b - n • p ∈ Set.Ico a (a + p)) :
    toIcoDiv hp a b = n :=
  ((existsUnique_sub_zsmul_mem_Ico hp b a).choose_spec.2 _ h).symm
#align to_Ico_div_eq_of_sub_zsmul_mem_Ico toIcoDiv_eq_of_sub_zsmul_mem_Ico

/--
The unique integer such that this multiple of `p`, subtracted from `b`, is in `Ioc a (a + p)`. -/
def toIocDiv (a b : α) : ℤ :=
  (existsUnique_sub_zsmul_mem_Ioc hp b a).some
#align to_Ioc_div toIocDiv

theorem sub_toIocDiv_zsmul_mem_Ioc (a b : α) : b - toIocDiv hp a b • p ∈ Set.Ioc a (a + p) :=
  (existsUnique_sub_zsmul_mem_Ioc hp b a).choose_spec.1
#align sub_to_Ioc_div_zsmul_mem_Ioc sub_toIocDiv_zsmul_mem_Ioc

theorem toIocDiv_eq_of_sub_zsmul_mem_Ioc (h : b - n • p ∈ Set.Ioc a (a + p)) :
    toIocDiv hp a b = n :=
  ((existsUnique_sub_zsmul_mem_Ioc hp b a).choose_spec.2 _ h).symm
#align to_Ioc_div_eq_of_sub_zsmul_mem_Ioc toIocDiv_eq_of_sub_zsmul_mem_Ioc

/-- Reduce `b` to the interval `Ico a (a + p)`. -/
def toIcoMod (a b : α) : α :=
  b - toIcoDiv hp a b • p
#align to_Ico_mod toIcoMod

/-- Reduce `b` to the interval `Ioc a (a + p)`. -/
def toIocMod (a b : α) : α :=
  b - toIocDiv hp a b • p
#align to_Ioc_mod toIocMod

theorem toIcoMod_mem_Ico (a b : α) : toIcoMod hp a b ∈ Set.Ico a (a + p) :=
  sub_toIcoDiv_zsmul_mem_Ico hp a b
#align to_Ico_mod_mem_Ico toIcoMod_mem_Ico

theorem toIcoMod_mem_Ico' (b : α) : toIcoMod hp 0 b ∈ Set.Ico 0 p :=
  by
  convert toIcoMod_mem_Ico hp 0 b
  exact (zero_add p).symm
#align to_Ico_mod_mem_Ico' toIcoMod_mem_Ico'

theorem toIocMod_mem_Ioc (a b : α) : toIocMod hp a b ∈ Set.Ioc a (a + p) :=
  sub_toIocDiv_zsmul_mem_Ioc hp a b
#align to_Ioc_mod_mem_Ioc toIocMod_mem_Ioc

theorem left_le_toIcoMod (a b : α) : a ≤ toIcoMod hp a b :=
  (Set.mem_Ico.1 (toIcoMod_mem_Ico hp a b)).1
#align left_le_to_Ico_mod left_le_toIcoMod

theorem left_lt_toIocMod (a b : α) : a < toIocMod hp a b :=
  (Set.mem_Ioc.1 (toIocMod_mem_Ioc hp a b)).1
#align left_lt_to_Ioc_mod left_lt_toIocMod

theorem toIcoMod_lt_right (a b : α) : toIcoMod hp a b < a + p :=
  (Set.mem_Ico.1 (toIcoMod_mem_Ico hp a b)).2
#align to_Ico_mod_lt_right toIcoMod_lt_right

theorem toIocMod_le_right (a b : α) : toIocMod hp a b ≤ a + p :=
  (Set.mem_Ioc.1 (toIocMod_mem_Ioc hp a b)).2
#align to_Ioc_mod_le_right toIocMod_le_right

@[simp]
theorem self_sub_toIcoDiv_zsmul (a b : α) : b - toIcoDiv hp a b • p = toIcoMod hp a b :=
  rfl
#align self_sub_to_Ico_div_zsmul self_sub_toIcoDiv_zsmul

@[simp]
theorem self_sub_toIocDiv_zsmul (a b : α) : b - toIocDiv hp a b • p = toIocMod hp a b :=
  rfl
#align self_sub_to_Ioc_div_zsmul self_sub_toIocDiv_zsmul

@[simp]
theorem toIcoDiv_zsmul_sub_self (a b : α) : toIcoDiv hp a b • p - b = -toIcoMod hp a b := by
  rw [toIcoMod, neg_sub]
#align to_Ico_div_zsmul_sub_self toIcoDiv_zsmul_sub_self

@[simp]
theorem toIocDiv_zsmul_sub_self (a b : α) : toIocDiv hp a b • p - b = -toIocMod hp a b := by
  rw [toIocMod, neg_sub]
#align to_Ioc_div_zsmul_sub_self toIocDiv_zsmul_sub_self

@[simp]
theorem toIcoMod_sub_self (a b : α) : toIcoMod hp a b - b = -toIcoDiv hp a b • p := by
  rw [toIcoMod, sub_sub_cancel_left, neg_smul]
#align to_Ico_mod_sub_self toIcoMod_sub_self

@[simp]
theorem toIocMod_sub_self (a b : α) : toIocMod hp a b - b = -toIocDiv hp a b • p := by
  rw [toIocMod, sub_sub_cancel_left, neg_smul]
#align to_Ioc_mod_sub_self toIocMod_sub_self

@[simp]
theorem self_sub_toIcoMod (a b : α) : b - toIcoMod hp a b = toIcoDiv hp a b • p := by
  rw [toIcoMod, sub_sub_cancel]
#align self_sub_to_Ico_mod self_sub_toIcoMod

@[simp]
theorem self_sub_toIocMod (a b : α) : b - toIocMod hp a b = toIocDiv hp a b • p := by
  rw [toIocMod, sub_sub_cancel]
#align self_sub_to_Ioc_mod self_sub_toIocMod

@[simp]
theorem toIcoMod_add_toIcoDiv_zsmul (a b : α) : toIcoMod hp a b + toIcoDiv hp a b • p = b := by
  rw [toIcoMod, sub_add_cancel]
#align to_Ico_mod_add_to_Ico_div_zsmul toIcoMod_add_toIcoDiv_zsmul

@[simp]
theorem toIocMod_add_toIocDiv_zsmul (a b : α) : toIocMod hp a b + toIocDiv hp a b • p = b := by
  rw [toIocMod, sub_add_cancel]
#align to_Ioc_mod_add_to_Ioc_div_zsmul toIocMod_add_toIocDiv_zsmul

@[simp]
theorem toIcoDiv_zsmul_sub_toIcoMod (a b : α) : toIcoDiv hp a b • p + toIcoMod hp a b = b := by
  rw [add_comm, toIcoMod_add_toIcoDiv_zsmul]
#align to_Ico_div_zsmul_sub_to_Ico_mod toIcoDiv_zsmul_sub_toIcoMod

@[simp]
theorem toIocDiv_zsmul_sub_toIocMod (a b : α) : toIocDiv hp a b • p + toIocMod hp a b = b := by
  rw [add_comm, toIocMod_add_toIocDiv_zsmul]
#align to_Ioc_div_zsmul_sub_to_Ioc_mod toIocDiv_zsmul_sub_toIocMod

theorem toIcoMod_eq_iff : toIcoMod hp a b = c ↔ c ∈ Set.Ico a (a + p) ∧ ∃ z : ℤ, b = c + z • p :=
  by
  refine'
    ⟨fun h =>
      ⟨h ▸ toIcoMod_mem_Ico hp a b, toIcoDiv hp a b, h ▸ (toIcoMod_add_toIcoDiv_zsmul _ _ _).symm⟩,
      _⟩
  simp_rw [← @sub_eq_iff_eq_add]
  rintro ⟨hc, n, rfl⟩
  rw [← toIcoDiv_eq_of_sub_zsmul_mem_Ico hp hc, toIcoMod]
#align to_Ico_mod_eq_iff toIcoMod_eq_iff

theorem toIocMod_eq_iff : toIocMod hp a b = c ↔ c ∈ Set.Ioc a (a + p) ∧ ∃ z : ℤ, b = c + z • p :=
  by
  refine'
    ⟨fun h =>
      ⟨h ▸ toIocMod_mem_Ioc hp a b, toIocDiv hp a b, h ▸ (toIocMod_add_toIocDiv_zsmul hp _ _).symm⟩,
      _⟩
  simp_rw [← @sub_eq_iff_eq_add]
  rintro ⟨hc, n, rfl⟩
  rw [← toIocDiv_eq_of_sub_zsmul_mem_Ioc hp hc, toIocMod]
#align to_Ioc_mod_eq_iff toIocMod_eq_iff

@[simp]
theorem toIcoDiv_apply_left (a : α) : toIcoDiv hp a a = 0 :=
  toIcoDiv_eq_of_sub_zsmul_mem_Ico hp <| by simp [hp]
#align to_Ico_div_apply_left toIcoDiv_apply_left

@[simp]
theorem toIocDiv_apply_left (a : α) : toIocDiv hp a a = -1 :=
  toIocDiv_eq_of_sub_zsmul_mem_Ioc hp <| by simp [hp]
#align to_Ioc_div_apply_left toIocDiv_apply_left

@[simp]
theorem toIcoMod_apply_left (a : α) : toIcoMod hp a a = a :=
  by
  rw [toIcoMod_eq_iff hp, Set.left_mem_Ico]
  exact ⟨lt_add_of_pos_right _ hp, 0, by simp⟩
#align to_Ico_mod_apply_left toIcoMod_apply_left

@[simp]
theorem toIocMod_apply_left (a : α) : toIocMod hp a a = a + p :=
  by
  rw [toIocMod_eq_iff hp, Set.right_mem_Ioc]
  exact ⟨lt_add_of_pos_right _ hp, -1, by simp⟩
#align to_Ioc_mod_apply_left toIocMod_apply_left

theorem toIcoDiv_apply_right (a : α) : toIcoDiv hp a (a + p) = 1 :=
  toIcoDiv_eq_of_sub_zsmul_mem_Ico hp <| by simp [hp]
#align to_Ico_div_apply_right toIcoDiv_apply_right

theorem toIocDiv_apply_right (a : α) : toIocDiv hp a (a + p) = 0 :=
  toIocDiv_eq_of_sub_zsmul_mem_Ioc hp <| by simp [hp]
#align to_Ioc_div_apply_right toIocDiv_apply_right

theorem toIcoMod_apply_right (a : α) : toIcoMod hp a (a + p) = a :=
  by
  rw [toIcoMod_eq_iff hp, Set.left_mem_Ico]
  exact ⟨lt_add_of_pos_right _ hp, 1, by simp⟩
#align to_Ico_mod_apply_right toIcoMod_apply_right

theorem toIocMod_apply_right (a : α) : toIocMod hp a (a + p) = a + p :=
  by
  rw [toIocMod_eq_iff hp, Set.right_mem_Ioc]
  exact ⟨lt_add_of_pos_right _ hp, 0, by simp⟩
#align to_Ioc_mod_apply_right toIocMod_apply_right

@[simp]
theorem toIcoDiv_add_zsmul (a b : α) (m : ℤ) : toIcoDiv hp a (b + m • p) = toIcoDiv hp a b + m :=
  toIcoDiv_eq_of_sub_zsmul_mem_Ico hp <| by
    simpa only [add_smul, add_sub_add_right_eq_sub] using sub_toIcoDiv_zsmul_mem_Ico hp a b
#align to_Ico_div_add_zsmul toIcoDiv_add_zsmul

@[simp]
theorem toIcoDiv_add_zsmul' (a b : α) (m : ℤ) : toIcoDiv hp (a + m • p) b = toIcoDiv hp a b - m :=
  by
  refine' toIcoDiv_eq_of_sub_zsmul_mem_Ico _ _
  rw [sub_smul, ← sub_add, add_right_comm]
  simpa using sub_toIcoDiv_zsmul_mem_Ico hp a b
#align to_Ico_div_add_zsmul' toIcoDiv_add_zsmul'

@[simp]
theorem toIocDiv_add_zsmul (a b : α) (m : ℤ) : toIocDiv hp a (b + m • p) = toIocDiv hp a b + m :=
  toIocDiv_eq_of_sub_zsmul_mem_Ioc hp <| by
    simpa only [add_smul, add_sub_add_right_eq_sub] using sub_toIocDiv_zsmul_mem_Ioc hp a b
#align to_Ioc_div_add_zsmul toIocDiv_add_zsmul

@[simp]
theorem toIocDiv_add_zsmul' (a b : α) (m : ℤ) : toIocDiv hp (a + m • p) b = toIocDiv hp a b - m :=
  by
  refine' toIocDiv_eq_of_sub_zsmul_mem_Ioc _ _
  rw [sub_smul, ← sub_add, add_right_comm]
  simpa using sub_toIocDiv_zsmul_mem_Ioc hp a b
#align to_Ioc_div_add_zsmul' toIocDiv_add_zsmul'

@[simp]
theorem toIcoDiv_zsmul_add (a b : α) (m : ℤ) : toIcoDiv hp a (m • p + b) = m + toIcoDiv hp a b := by
  rw [add_comm, toIcoDiv_add_zsmul, add_comm]
#align to_Ico_div_zsmul_add toIcoDiv_zsmul_add

/-! Note we omit `to_Ico_div_zsmul_add'` as `-m + to_Ico_div hp a b` is not very convenient. -/


@[simp]
theorem toIocDiv_zsmul_add (a b : α) (m : ℤ) : toIocDiv hp a (m • p + b) = m + toIocDiv hp a b := by
  rw [add_comm, toIocDiv_add_zsmul, add_comm]
#align to_Ioc_div_zsmul_add toIocDiv_zsmul_add

/-! Note we omit `to_Ioc_div_zsmul_add'` as `-m + to_Ioc_div hp a b` is not very convenient. -/


@[simp]
theorem toIcoDiv_sub_zsmul (a b : α) (m : ℤ) : toIcoDiv hp a (b - m • p) = toIcoDiv hp a b - m := by
  rw [sub_eq_add_neg, ← neg_smul, toIcoDiv_add_zsmul, sub_eq_add_neg]
#align to_Ico_div_sub_zsmul toIcoDiv_sub_zsmul

@[simp]
theorem toIcoDiv_sub_zsmul' (a b : α) (m : ℤ) : toIcoDiv hp (a - m • p) b = toIcoDiv hp a b + m :=
  by rw [sub_eq_add_neg, ← neg_smul, toIcoDiv_add_zsmul', sub_neg_eq_add]
#align to_Ico_div_sub_zsmul' toIcoDiv_sub_zsmul'

@[simp]
theorem toIocDiv_sub_zsmul (a b : α) (m : ℤ) : toIocDiv hp a (b - m • p) = toIocDiv hp a b - m := by
  rw [sub_eq_add_neg, ← neg_smul, toIocDiv_add_zsmul, sub_eq_add_neg]
#align to_Ioc_div_sub_zsmul toIocDiv_sub_zsmul

@[simp]
theorem toIocDiv_sub_zsmul' (a b : α) (m : ℤ) : toIocDiv hp (a - m • p) b = toIocDiv hp a b + m :=
  by rw [sub_eq_add_neg, ← neg_smul, toIocDiv_add_zsmul', sub_neg_eq_add]
#align to_Ioc_div_sub_zsmul' toIocDiv_sub_zsmul'

@[simp]
theorem toIcoDiv_add_right (a b : α) : toIcoDiv hp a (b + p) = toIcoDiv hp a b + 1 := by
  simpa only [one_zsmul] using toIcoDiv_add_zsmul hp a b 1
#align to_Ico_div_add_right toIcoDiv_add_right

@[simp]
theorem toIcoDiv_add_right' (a b : α) : toIcoDiv hp (a + p) b = toIcoDiv hp a b - 1 := by
  simpa only [one_zsmul] using toIcoDiv_add_zsmul' hp a b 1
#align to_Ico_div_add_right' toIcoDiv_add_right'

@[simp]
theorem toIocDiv_add_right (a b : α) : toIocDiv hp a (b + p) = toIocDiv hp a b + 1 := by
  simpa only [one_zsmul] using toIocDiv_add_zsmul hp a b 1
#align to_Ioc_div_add_right toIocDiv_add_right

@[simp]
theorem toIocDiv_add_right' (a b : α) : toIocDiv hp (a + p) b = toIocDiv hp a b - 1 := by
  simpa only [one_zsmul] using toIocDiv_add_zsmul' hp a b 1
#align to_Ioc_div_add_right' toIocDiv_add_right'

@[simp]
theorem toIcoDiv_add_left (a b : α) : toIcoDiv hp a (p + b) = toIcoDiv hp a b + 1 := by
  rw [add_comm, toIcoDiv_add_right]
#align to_Ico_div_add_left toIcoDiv_add_left

@[simp]
theorem toIcoDiv_add_left' (a b : α) : toIcoDiv hp (p + a) b = toIcoDiv hp a b - 1 := by
  rw [add_comm, toIcoDiv_add_right']
#align to_Ico_div_add_left' toIcoDiv_add_left'

@[simp]
theorem toIocDiv_add_left (a b : α) : toIocDiv hp a (p + b) = toIocDiv hp a b + 1 := by
  rw [add_comm, toIocDiv_add_right]
#align to_Ioc_div_add_left toIocDiv_add_left

@[simp]
theorem toIocDiv_add_left' (a b : α) : toIocDiv hp (p + a) b = toIocDiv hp a b - 1 := by
  rw [add_comm, toIocDiv_add_right']
#align to_Ioc_div_add_left' toIocDiv_add_left'

@[simp]
theorem toIcoDiv_sub (a b : α) : toIcoDiv hp a (b - p) = toIcoDiv hp a b - 1 := by
  simpa only [one_zsmul] using toIcoDiv_sub_zsmul hp a b 1
#align to_Ico_div_sub toIcoDiv_sub

@[simp]
theorem toIcoDiv_sub' (a b : α) : toIcoDiv hp (a - p) b = toIcoDiv hp a b + 1 := by
  simpa only [one_zsmul] using toIcoDiv_sub_zsmul' hp a b 1
#align to_Ico_div_sub' toIcoDiv_sub'

@[simp]
theorem toIocDiv_sub (a b : α) : toIocDiv hp a (b - p) = toIocDiv hp a b - 1 := by
  simpa only [one_zsmul] using toIocDiv_sub_zsmul hp a b 1
#align to_Ioc_div_sub toIocDiv_sub

@[simp]
theorem toIocDiv_sub' (a b : α) : toIocDiv hp (a - p) b = toIocDiv hp a b + 1 := by
  simpa only [one_zsmul] using toIocDiv_sub_zsmul' hp a b 1
#align to_Ioc_div_sub' toIocDiv_sub'

theorem toIcoDiv_sub_eq_toIcoDiv_add (a b c : α) : toIcoDiv hp a (b - c) = toIcoDiv hp (a + c) b :=
  by
  apply toIcoDiv_eq_of_sub_zsmul_mem_Ico
  rw [← sub_right_comm, Set.sub_mem_Ico_iff_left, add_right_comm]
  exact sub_toIcoDiv_zsmul_mem_Ico hp (a + c) b
#align to_Ico_div_sub_eq_to_Ico_div_add toIcoDiv_sub_eq_toIcoDiv_add

theorem toIocDiv_sub_eq_toIocDiv_add (a b c : α) : toIocDiv hp a (b - c) = toIocDiv hp (a + c) b :=
  by
  apply toIocDiv_eq_of_sub_zsmul_mem_Ioc
  rw [← sub_right_comm, Set.sub_mem_Ioc_iff_left, add_right_comm]
  exact sub_toIocDiv_zsmul_mem_Ioc hp (a + c) b
#align to_Ioc_div_sub_eq_to_Ioc_div_add toIocDiv_sub_eq_toIocDiv_add

theorem toIcoDiv_sub_eq_toIcoDiv_add' (a b c : α) : toIcoDiv hp (a - c) b = toIcoDiv hp a (b + c) :=
  by rw [← sub_neg_eq_add, toIcoDiv_sub_eq_toIcoDiv_add, sub_eq_add_neg]
#align to_Ico_div_sub_eq_to_Ico_div_add' toIcoDiv_sub_eq_toIcoDiv_add'

theorem toIocDiv_sub_eq_toIocDiv_add' (a b c : α) : toIocDiv hp (a - c) b = toIocDiv hp a (b + c) :=
  by rw [← sub_neg_eq_add, toIocDiv_sub_eq_toIocDiv_add, sub_eq_add_neg]
#align to_Ioc_div_sub_eq_to_Ioc_div_add' toIocDiv_sub_eq_toIocDiv_add'

theorem toIcoDiv_neg (a b : α) : toIcoDiv hp a (-b) = -(toIocDiv hp (-a) b + 1) :=
  by
  suffices toIcoDiv hp a (-b) = -toIocDiv hp (-(a + p)) b by
    rwa [neg_add, ← sub_eq_add_neg, toIocDiv_sub_eq_toIocDiv_add', toIocDiv_add_right] at this
  rw [← neg_eq_iff_eq_neg, eq_comm]
  apply toIocDiv_eq_of_sub_zsmul_mem_Ioc
  obtain ⟨hc, ho⟩ := sub_toIcoDiv_zsmul_mem_Ico hp a (-b)
  rw [← neg_lt_neg_iff, neg_sub' (-b), neg_neg, ← neg_smul] at ho
  rw [← neg_le_neg_iff, neg_sub' (-b), neg_neg, ← neg_smul] at hc
  refine' ⟨ho, hc.trans_eq _⟩
  rw [neg_add, neg_add_cancel_right]
#align to_Ico_div_neg toIcoDiv_neg

theorem toIcoDiv_neg' (a b : α) : toIcoDiv hp (-a) b = -(toIocDiv hp a (-b) + 1) := by
  simpa only [neg_neg] using toIcoDiv_neg hp (-a) (-b)
#align to_Ico_div_neg' toIcoDiv_neg'

theorem toIocDiv_neg (a b : α) : toIocDiv hp a (-b) = -(toIcoDiv hp (-a) b + 1) := by
  rw [← neg_neg b, toIcoDiv_neg, neg_neg, neg_neg, neg_add', neg_neg, add_sub_cancel]
#align to_Ioc_div_neg toIocDiv_neg

theorem toIocDiv_neg' (a b : α) : toIocDiv hp (-a) b = -(toIcoDiv hp a (-b) + 1) := by
  simpa only [neg_neg] using toIocDiv_neg hp (-a) (-b)
#align to_Ioc_div_neg' toIocDiv_neg'

@[simp]
theorem toIcoMod_add_zsmul (a b : α) (m : ℤ) : toIcoMod hp a (b + m • p) = toIcoMod hp a b :=
  by
  rw [toIcoMod, toIcoDiv_add_zsmul, toIcoMod, add_smul]
  abel
#align to_Ico_mod_add_zsmul toIcoMod_add_zsmul

@[simp]
theorem toIcoMod_add_zsmul' (a b : α) (m : ℤ) :
    toIcoMod hp (a + m • p) b = toIcoMod hp a b + m • p := by
  simp only [toIcoMod, toIcoDiv_add_zsmul', sub_smul, sub_add]
#align to_Ico_mod_add_zsmul' toIcoMod_add_zsmul'

@[simp]
theorem toIocMod_add_zsmul (a b : α) (m : ℤ) : toIocMod hp a (b + m • p) = toIocMod hp a b :=
  by
  rw [toIocMod, toIocDiv_add_zsmul, toIocMod, add_smul]
  abel
#align to_Ioc_mod_add_zsmul toIocMod_add_zsmul

@[simp]
theorem toIocMod_add_zsmul' (a b : α) (m : ℤ) :
    toIocMod hp (a + m • p) b = toIocMod hp a b + m • p := by
  simp only [toIocMod, toIocDiv_add_zsmul', sub_smul, sub_add]
#align to_Ioc_mod_add_zsmul' toIocMod_add_zsmul'

@[simp]
theorem toIcoMod_zsmul_add (a b : α) (m : ℤ) : toIcoMod hp a (m • p + b) = toIcoMod hp a b := by
  rw [add_comm, toIcoMod_add_zsmul]
#align to_Ico_mod_zsmul_add toIcoMod_zsmul_add

@[simp]
theorem toIcoMod_zsmul_add' (a b : α) (m : ℤ) :
    toIcoMod hp (m • p + a) b = m • p + toIcoMod hp a b := by
  rw [add_comm, toIcoMod_add_zsmul', add_comm]
#align to_Ico_mod_zsmul_add' toIcoMod_zsmul_add'

@[simp]
theorem toIocMod_zsmul_add (a b : α) (m : ℤ) : toIocMod hp a (m • p + b) = toIocMod hp a b := by
  rw [add_comm, toIocMod_add_zsmul]
#align to_Ioc_mod_zsmul_add toIocMod_zsmul_add

@[simp]
theorem toIocMod_zsmul_add' (a b : α) (m : ℤ) :
    toIocMod hp (m • p + a) b = m • p + toIocMod hp a b := by
  rw [add_comm, toIocMod_add_zsmul', add_comm]
#align to_Ioc_mod_zsmul_add' toIocMod_zsmul_add'

@[simp]
theorem toIcoMod_sub_zsmul (a b : α) (m : ℤ) : toIcoMod hp a (b - m • p) = toIcoMod hp a b := by
  rw [sub_eq_add_neg, ← neg_smul, toIcoMod_add_zsmul]
#align to_Ico_mod_sub_zsmul toIcoMod_sub_zsmul

@[simp]
theorem toIcoMod_sub_zsmul' (a b : α) (m : ℤ) :
    toIcoMod hp (a - m • p) b = toIcoMod hp a b - m • p := by
  simp_rw [sub_eq_add_neg, ← neg_smul, toIcoMod_add_zsmul']
#align to_Ico_mod_sub_zsmul' toIcoMod_sub_zsmul'

@[simp]
theorem toIocMod_sub_zsmul (a b : α) (m : ℤ) : toIocMod hp a (b - m • p) = toIocMod hp a b := by
  rw [sub_eq_add_neg, ← neg_smul, toIocMod_add_zsmul]
#align to_Ioc_mod_sub_zsmul toIocMod_sub_zsmul

@[simp]
theorem toIocMod_sub_zsmul' (a b : α) (m : ℤ) :
    toIocMod hp (a - m • p) b = toIocMod hp a b - m • p := by
  simp_rw [sub_eq_add_neg, ← neg_smul, toIocMod_add_zsmul']
#align to_Ioc_mod_sub_zsmul' toIocMod_sub_zsmul'

@[simp]
theorem toIcoMod_add_right (a b : α) : toIcoMod hp a (b + p) = toIcoMod hp a b := by
  simpa only [one_zsmul] using toIcoMod_add_zsmul hp a b 1
#align to_Ico_mod_add_right toIcoMod_add_right

@[simp]
theorem toIcoMod_add_right' (a b : α) : toIcoMod hp (a + p) b = toIcoMod hp a b + p := by
  simpa only [one_zsmul] using toIcoMod_add_zsmul' hp a b 1
#align to_Ico_mod_add_right' toIcoMod_add_right'

@[simp]
theorem toIocMod_add_right (a b : α) : toIocMod hp a (b + p) = toIocMod hp a b := by
  simpa only [one_zsmul] using toIocMod_add_zsmul hp a b 1
#align to_Ioc_mod_add_right toIocMod_add_right

@[simp]
theorem toIocMod_add_right' (a b : α) : toIocMod hp (a + p) b = toIocMod hp a b + p := by
  simpa only [one_zsmul] using toIocMod_add_zsmul' hp a b 1
#align to_Ioc_mod_add_right' toIocMod_add_right'

@[simp]
theorem toIcoMod_add_left (a b : α) : toIcoMod hp a (p + b) = toIcoMod hp a b := by
  rw [add_comm, toIcoMod_add_right]
#align to_Ico_mod_add_left toIcoMod_add_left

@[simp]
theorem toIcoMod_add_left' (a b : α) : toIcoMod hp (p + a) b = p + toIcoMod hp a b := by
  rw [add_comm, toIcoMod_add_right', add_comm]
#align to_Ico_mod_add_left' toIcoMod_add_left'

@[simp]
theorem toIocMod_add_left (a b : α) : toIocMod hp a (p + b) = toIocMod hp a b := by
  rw [add_comm, toIocMod_add_right]
#align to_Ioc_mod_add_left toIocMod_add_left

@[simp]
theorem toIocMod_add_left' (a b : α) : toIocMod hp (p + a) b = p + toIocMod hp a b := by
  rw [add_comm, toIocMod_add_right', add_comm]
#align to_Ioc_mod_add_left' toIocMod_add_left'

@[simp]
theorem toIcoMod_sub (a b : α) : toIcoMod hp a (b - p) = toIcoMod hp a b := by
  simpa only [one_zsmul] using toIcoMod_sub_zsmul hp a b 1
#align to_Ico_mod_sub toIcoMod_sub

@[simp]
theorem toIcoMod_sub' (a b : α) : toIcoMod hp (a - p) b = toIcoMod hp a b - p := by
  simpa only [one_zsmul] using toIcoMod_sub_zsmul' hp a b 1
#align to_Ico_mod_sub' toIcoMod_sub'

@[simp]
theorem toIocMod_sub (a b : α) : toIocMod hp a (b - p) = toIocMod hp a b := by
  simpa only [one_zsmul] using toIocMod_sub_zsmul hp a b 1
#align to_Ioc_mod_sub toIocMod_sub

@[simp]
theorem toIocMod_sub' (a b : α) : toIocMod hp (a - p) b = toIocMod hp a b - p := by
  simpa only [one_zsmul] using toIocMod_sub_zsmul' hp a b 1
#align to_Ioc_mod_sub' toIocMod_sub'

theorem toIcoMod_sub_eq_sub (a b c : α) : toIcoMod hp a (b - c) = toIcoMod hp (a + c) b - c := by
  simp_rw [toIcoMod, toIcoDiv_sub_eq_toIcoDiv_add, sub_right_comm]
#align to_Ico_mod_sub_eq_sub toIcoMod_sub_eq_sub

theorem toIocMod_sub_eq_sub (a b c : α) : toIocMod hp a (b - c) = toIocMod hp (a + c) b - c := by
  simp_rw [toIocMod, toIocDiv_sub_eq_toIocDiv_add, sub_right_comm]
#align to_Ioc_mod_sub_eq_sub toIocMod_sub_eq_sub

theorem toIcoMod_add_right_eq_add (a b c : α) : toIcoMod hp a (b + c) = toIcoMod hp (a - c) b + c :=
  by simp_rw [toIcoMod, toIcoDiv_sub_eq_toIcoDiv_add', sub_add_eq_add_sub]
#align to_Ico_mod_add_right_eq_add toIcoMod_add_right_eq_add

theorem toIocMod_add_right_eq_add (a b c : α) : toIocMod hp a (b + c) = toIocMod hp (a - c) b + c :=
  by simp_rw [toIocMod, toIocDiv_sub_eq_toIocDiv_add', sub_add_eq_add_sub]
#align to_Ioc_mod_add_right_eq_add toIocMod_add_right_eq_add

theorem toIcoMod_neg (a b : α) : toIcoMod hp a (-b) = p - toIocMod hp (-a) b :=
  by
  simp_rw [toIcoMod, toIocMod, toIcoDiv_neg, neg_smul, add_smul]
  abel
#align to_Ico_mod_neg toIcoMod_neg

theorem toIcoMod_neg' (a b : α) : toIcoMod hp (-a) b = p - toIocMod hp a (-b) := by
  simpa only [neg_neg] using toIcoMod_neg hp (-a) (-b)
#align to_Ico_mod_neg' toIcoMod_neg'

theorem toIocMod_neg (a b : α) : toIocMod hp a (-b) = p - toIcoMod hp (-a) b :=
  by
  simp_rw [toIocMod, toIcoMod, toIocDiv_neg, neg_smul, add_smul]
  abel
#align to_Ioc_mod_neg toIocMod_neg

theorem toIocMod_neg' (a b : α) : toIocMod hp (-a) b = p - toIcoMod hp a (-b) := by
  simpa only [neg_neg] using toIocMod_neg hp (-a) (-b)
#align to_Ioc_mod_neg' toIocMod_neg'

theorem toIcoMod_eq_toIcoMod : toIcoMod hp a b = toIcoMod hp a c ↔ ∃ n : ℤ, c - b = n • p :=
  by
  refine' ⟨fun h => ⟨toIcoDiv hp a c - toIcoDiv hp a b, _⟩, fun h => _⟩
  · conv_lhs => rw [← toIcoMod_add_toIcoDiv_zsmul hp a b, ← toIcoMod_add_toIcoDiv_zsmul hp a c]
    rw [h, sub_smul]
    abel
  · rcases h with ⟨z, hz⟩
    rw [sub_eq_iff_eq_add] at hz
    rw [hz, toIcoMod_zsmul_add]
#align to_Ico_mod_eq_to_Ico_mod toIcoMod_eq_toIcoMod

theorem toIocMod_eq_toIocMod : toIocMod hp a b = toIocMod hp a c ↔ ∃ n : ℤ, c - b = n • p :=
  by
  refine' ⟨fun h => ⟨toIocDiv hp a c - toIocDiv hp a b, _⟩, fun h => _⟩
  · conv_lhs => rw [← toIocMod_add_toIocDiv_zsmul hp a b, ← toIocMod_add_toIocDiv_zsmul hp a c]
    rw [h, sub_smul]
    abel
  · rcases h with ⟨z, hz⟩
    rw [sub_eq_iff_eq_add] at hz
    rw [hz, toIocMod_zsmul_add]
#align to_Ioc_mod_eq_to_Ioc_mod toIocMod_eq_toIocMod

/-! ### Links between the `Ico` and `Ioc` variants applied to the same element -/


section IcoIoc

namespace AddCommGroup

variable (a b)

omit hα

/-- `add_comm_group.modeq p a b` means that `b` does not lie in the open interval `(a, a + p)`
modulo `p`.

Equivalently (as shown below), `b` is congruent to `a` modulo `p`, or `to_Ico_mod hp a` disagrees
with `to_Ioc_mod hp a` at `b`, or `to_Ico_div hp a` disagrees with `to_Ioc_div hp a` at `b`. -/
def Modeq (p a b : α) : Prop :=
  ∀ z : ℤ, b - z • p ∉ Set.Ioo a (a + p)
#align add_comm_group.modeq AddCommGroup.Modeq

include hα

-- mathport name: «expr ≡ [PMOD ]»
notation:50 a " ≡ " b " [PMOD " p "]" => Modeq p a b

theorem tFAE_modeq :
    TFAE
      [a ≡ b [PMOD p], toIcoMod hp a b ≠ toIocMod hp a b, toIcoMod hp a b + p = toIocMod hp a b,
        toIcoMod hp a b = a] :=
  by
  rw [modeq]
  tfae_have 2 → 1
  · rw [← not_exists, not_imp_not]
    exact fun ⟨i, hi⟩ =>
      ((toIcoMod_eq_iff hp).2 ⟨Set.Ioo_subset_Ico_self hi, i, (sub_add_cancel b _).symm⟩).trans
        ((toIocMod_eq_iff hp).2 ⟨Set.Ioo_subset_Ioc_self hi, i, (sub_add_cancel b _).symm⟩).symm
  tfae_have 3 → 2
  · intro h
    rw [← h, Ne, eq_comm, add_right_eq_self]
    exact hp.ne'
  tfae_have 4 → 3
  · intro h
    rw [h, eq_comm, toIocMod_eq_iff, Set.right_mem_Ioc]
    refine' ⟨lt_add_of_pos_right a hp, toIcoDiv hp a b - 1, _⟩
    rw [sub_one_zsmul, add_add_add_comm, add_right_neg, add_zero]
    conv_lhs => rw [← toIcoMod_add_toIcoDiv_zsmul hp a b, h]
  tfae_have 1 → 4
  · rw [← not_exists, not_imp_comm]
    have h' := toIcoMod_mem_Ico hp a b
    exact fun h => ⟨_, h'.1.lt_of_ne' h, h'.2⟩
  tfae_finish
#align add_comm_group.tfae_modeq AddCommGroup.tFAE_modeq

variable {a b}

theorem modeq_iff_toIcoMod_ne_toIocMod : a ≡ b [PMOD p] ↔ toIcoMod hp a b ≠ toIocMod hp a b :=
  (tFAE_modeq hp a b).out 0 1
#align add_comm_group.modeq_iff_to_Ico_mod_ne_to_Ioc_mod AddCommGroup.modeq_iff_toIcoMod_ne_toIocMod

theorem modeq_iff_toIcoMod_add_period_eq_toIocMod :
    a ≡ b [PMOD p] ↔ toIcoMod hp a b + p = toIocMod hp a b :=
  (tFAE_modeq hp a b).out 0 2
#align add_comm_group.modeq_iff_to_Ico_mod_add_period_eq_to_Ioc_mod AddCommGroup.modeq_iff_toIcoMod_add_period_eq_toIocMod

theorem modeq_iff_toIcoMod_eq_left : a ≡ b [PMOD p] ↔ toIcoMod hp a b = a :=
  (tFAE_modeq hp a b).out 0 3
#align add_comm_group.modeq_iff_to_Ico_mod_eq_left AddCommGroup.modeq_iff_toIcoMod_eq_left

theorem not_modeq_iff_toIcoMod_eq_toIocMod : ¬a ≡ b [PMOD p] ↔ toIcoMod hp a b = toIocMod hp a b :=
  (modeq_iff_toIcoMod_ne_toIocMod _).not_left
#align add_comm_group.not_modeq_iff_to_Ico_mod_eq_to_Ioc_mod AddCommGroup.not_modeq_iff_toIcoMod_eq_toIocMod

theorem modeq_iff_toIocMod_eq_right : a ≡ b [PMOD p] ↔ toIocMod hp a b = a + p :=
  by
  rw [modeq_iff_to_Ico_mod_ne_to_Ioc_mod hp, Ne, toIcoMod_eq_iff hp, not_iff_comm]
  obtain ⟨h₁, h₂⟩ := toIocMod_mem_Ioc hp a b
  exact
    ⟨fun h => ⟨⟨h₁.le, h₂.lt_of_ne h⟩, _, (toIocMod_add_toIocDiv_zsmul _ _ _).symm⟩, fun h =>
      h.1.2.Ne⟩
#align add_comm_group.modeq_iff_to_Ioc_mod_eq_right AddCommGroup.modeq_iff_toIocMod_eq_right

theorem not_modeq_iff_toIcoDiv_eq_toIocDiv : ¬a ≡ b [PMOD p] ↔ toIcoDiv hp a b = toIocDiv hp a b :=
  by
  rw [not_modeq_iff_to_Ico_mod_eq_to_Ioc_mod hp, toIcoMod, toIocMod, sub_right_inj,
    (zsmul_strictMono_left hp).Injective.eq_iff]
#align add_comm_group.not_modeq_iff_to_Ico_div_eq_to_Ioc_div AddCommGroup.not_modeq_iff_toIcoDiv_eq_toIocDiv

theorem modeq_iff_toIcoDiv_eq_toIocDiv_add_one :
    a ≡ b [PMOD p] ↔ toIcoDiv hp a b = toIocDiv hp a b + 1 := by
  rw [modeq_iff_to_Ico_mod_add_period_eq_to_Ioc_mod hp, toIcoMod, toIocMod, ← eq_sub_iff_add_eq,
    sub_sub, sub_right_inj, ← add_one_zsmul, (zsmul_strictMono_left hp).Injective.eq_iff]
#align add_comm_group.modeq_iff_to_Ico_div_eq_to_Ioc_div_add_one AddCommGroup.modeq_iff_toIcoDiv_eq_toIocDiv_add_one

include hp

theorem modeq_iff_eq_add_zsmul : a ≡ b [PMOD p] ↔ ∃ z : ℤ, b = a + z • p :=
  by
  rw [modeq_iff_to_Ico_mod_eq_left hp]
  constructor <;> intro h
  · rw [← h]
    exact ⟨_, (toIcoMod_add_toIcoDiv_zsmul _ _ _).symm⟩
  · rw [toIcoMod_eq_iff, Set.left_mem_Ico]
    exact ⟨lt_add_of_pos_right a hp, h⟩
#align add_comm_group.modeq_iff_eq_add_zsmul AddCommGroup.modeq_iff_eq_add_zsmul

theorem not_modeq_iff_ne_add_zsmul : ¬a ≡ b [PMOD p] ↔ ∀ z : ℤ, b ≠ a + z • p := by
  rw [modeq_iff_eq_add_zsmul hp, not_exists]
#align add_comm_group.not_modeq_iff_ne_add_zsmul AddCommGroup.not_modeq_iff_ne_add_zsmul

theorem modeq_iff_eq_mod_zmultiples : a ≡ b [PMOD p] ↔ (b : α ⧸ AddSubgroup.zmultiples p) = a := by
  simp_rw [modeq_iff_eq_add_zsmul hp, QuotientAddGroup.eq_iff_sub_mem,
    AddSubgroup.mem_zmultiples_iff, eq_sub_iff_add_eq', eq_comm]
#align add_comm_group.modeq_iff_eq_mod_zmultiples AddCommGroup.modeq_iff_eq_mod_zmultiples

theorem not_modeq_iff_ne_mod_zmultiples :
    ¬a ≡ b [PMOD p] ↔ (b : α ⧸ AddSubgroup.zmultiples p) ≠ a :=
  (modeq_iff_eq_mod_zmultiples hp).Not
#align add_comm_group.not_modeq_iff_ne_mod_zmultiples AddCommGroup.not_modeq_iff_ne_mod_zmultiples

end AddCommGroup

theorem Ico_eq_locus_Ioc_eq_unionᵢ_Ioo :
    { b | toIcoMod hp a b = toIocMod hp a b } = ⋃ z : ℤ, Set.Ioo (a + z • p) (a + p + z • p) := by
  ext1;
  simp_rw [Set.mem_setOf, Set.mem_unionᵢ, ← Set.sub_mem_Ioo_iff_left, ←
    AddCommGroup.not_modeq_iff_toIcoMod_eq_toIocMod, AddCommGroup.Modeq, not_forall,
    Classical.not_not]
#align Ico_eq_locus_Ioc_eq_Union_Ioo Ico_eq_locus_Ioc_eq_unionᵢ_Ioo

theorem toIocDiv_wcovby_toIcoDiv (a b : α) : toIocDiv hp a b ⩿ toIcoDiv hp a b :=
  by
  suffices toIocDiv hp a b = toIcoDiv hp a b ∨ toIocDiv hp a b + 1 = toIcoDiv hp a b by
    rwa [wcovby_iff_eq_or_covby, ← Order.succ_eq_iff_covby]
  rw [eq_comm, ← AddCommGroup.not_modeq_iff_toIcoDiv_eq_toIocDiv, eq_comm, ←
    AddCommGroup.modeq_iff_toIcoDiv_eq_toIocDiv_add_one]
  exact em' _
#align to_Ioc_div_wcovby_to_Ico_div toIocDiv_wcovby_toIcoDiv

theorem toIcoMod_le_toIocMod (a b : α) : toIcoMod hp a b ≤ toIocMod hp a b :=
  by
  rw [toIcoMod, toIocMod, sub_le_sub_iff_left]
  exact zsmul_mono_left hp.le (toIocDiv_wcovby_toIcoDiv _ _ _).le
#align to_Ico_mod_le_to_Ioc_mod toIcoMod_le_toIocMod

theorem toIocMod_le_toIcoMod_add (a b : α) : toIocMod hp a b ≤ toIcoMod hp a b + p :=
  by
  rw [toIcoMod, toIocMod, sub_add, sub_le_sub_iff_left, sub_le_iff_le_add, ← add_one_zsmul,
    (zsmul_strictMono_left hp).le_iff_le]
  apply (toIocDiv_wcovby_toIcoDiv _ _ _).le_succ
#align to_Ioc_mod_le_to_Ico_mod_add toIocMod_le_toIcoMod_add

end IcoIoc

theorem toIcoMod_eq_self : toIcoMod hp a b = b ↔ b ∈ Set.Ico a (a + p) :=
  by
  rw [toIcoMod_eq_iff, and_iff_left]
  exact ⟨0, by simp⟩
#align to_Ico_mod_eq_self toIcoMod_eq_self

theorem toIocMod_eq_self : toIocMod hp a b = b ↔ b ∈ Set.Ioc a (a + p) :=
  by
  rw [toIocMod_eq_iff, and_iff_left]
  exact ⟨0, by simp⟩
#align to_Ioc_mod_eq_self toIocMod_eq_self

@[simp]
theorem toIcoMod_toIcoMod (a₁ a₂ b : α) : toIcoMod hp a₁ (toIcoMod hp a₂ b) = toIcoMod hp a₁ b :=
  (toIcoMod_eq_toIcoMod _).2 ⟨toIcoDiv hp a₂ b, self_sub_toIcoMod hp a₂ b⟩
#align to_Ico_mod_to_Ico_mod toIcoMod_toIcoMod

@[simp]
theorem toIcoMod_toIocMod (a₁ a₂ b : α) : toIcoMod hp a₁ (toIocMod hp a₂ b) = toIcoMod hp a₁ b :=
  (toIcoMod_eq_toIcoMod _).2 ⟨toIocDiv hp a₂ b, self_sub_toIocMod hp a₂ b⟩
#align to_Ico_mod_to_Ioc_mod toIcoMod_toIocMod

@[simp]
theorem toIocMod_toIocMod (a₁ a₂ b : α) : toIocMod hp a₁ (toIocMod hp a₂ b) = toIocMod hp a₁ b :=
  (toIocMod_eq_toIocMod _).2 ⟨toIocDiv hp a₂ b, self_sub_toIocMod hp a₂ b⟩
#align to_Ioc_mod_to_Ioc_mod toIocMod_toIocMod

@[simp]
theorem toIocMod_toIcoMod (a₁ a₂ b : α) : toIocMod hp a₁ (toIcoMod hp a₂ b) = toIocMod hp a₁ b :=
  (toIocMod_eq_toIocMod _).2 ⟨toIcoDiv hp a₂ b, self_sub_toIcoMod hp a₂ b⟩
#align to_Ioc_mod_to_Ico_mod toIocMod_toIcoMod

theorem toIcoMod_periodic (a : α) : Function.Periodic (toIcoMod hp a) p :=
  toIcoMod_add_right hp a
#align to_Ico_mod_periodic toIcoMod_periodic

theorem toIocMod_periodic (a : α) : Function.Periodic (toIocMod hp a) p :=
  toIocMod_add_right hp a
#align to_Ioc_mod_periodic toIocMod_periodic

/-- `to_Ico_mod` as an equiv from the quotient. -/
@[simps symm_apply]
def quotientAddGroup.equivIcoMod (a : α) : α ⧸ AddSubgroup.zmultiples p ≃ Set.Ico a (a + p)
    where
  toFun b :=
    ⟨(toIcoMod_periodic hp a).lift b, QuotientAddGroup.induction_on' b <| toIcoMod_mem_Ico hp a⟩
  invFun := coe
  right_inv b := Subtype.ext <| (toIcoMod_eq_self hp).mpr b.Prop
  left_inv b := by
    induction b using QuotientAddGroup.induction_on'
    dsimp
    rw [QuotientAddGroup.eq_iff_sub_mem, toIcoMod_sub_self]
    apply AddSubgroup.zsmul_mem_zmultiples
#align quotient_add_group.equiv_Ico_mod quotientAddGroup.equivIcoMod

@[simp]
theorem quotientAddGroup.equivIcoMod_coe (a b : α) :
    quotientAddGroup.equivIcoMod hp a ↑b = ⟨toIcoMod hp a b, toIcoMod_mem_Ico hp a _⟩ :=
  rfl
#align quotient_add_group.equiv_Ico_mod_coe quotientAddGroup.equivIcoMod_coe

/-- `to_Ioc_mod` as an equiv  from the quotient. -/
@[simps symm_apply]
def quotientAddGroup.equivIocMod (a : α) : α ⧸ AddSubgroup.zmultiples p ≃ Set.Ioc a (a + p)
    where
  toFun b :=
    ⟨(toIocMod_periodic hp a).lift b, QuotientAddGroup.induction_on' b <| toIocMod_mem_Ioc hp a⟩
  invFun := coe
  right_inv b := Subtype.ext <| (toIocMod_eq_self hp).mpr b.Prop
  left_inv b := by
    induction b using QuotientAddGroup.induction_on'
    dsimp
    rw [QuotientAddGroup.eq_iff_sub_mem, toIocMod_sub_self]
    apply AddSubgroup.zsmul_mem_zmultiples
#align quotient_add_group.equiv_Ioc_mod quotientAddGroup.equivIocMod

@[simp]
theorem quotientAddGroup.equivIocMod_coe (a b : α) :
    quotientAddGroup.equivIocMod hp a ↑b = ⟨toIocMod hp a b, toIocMod_mem_Ioc hp a _⟩ :=
  rfl
#align quotient_add_group.equiv_Ioc_mod_coe quotientAddGroup.equivIocMod_coe

end LinearOrderedAddCommGroup

section LinearOrderedField

variable {α : Type _} [LinearOrderedField α] [FloorRing α] {p : α} (hp : 0 < p)

theorem toIcoDiv_eq_floor (a b : α) : toIcoDiv hp a b = ⌊(b - a) / p⌋ :=
  by
  refine' toIcoDiv_eq_of_sub_zsmul_mem_Ico hp _
  rw [Set.mem_Ico, zsmul_eq_mul, ← sub_nonneg, add_comm, sub_right_comm, ← sub_lt_iff_lt_add,
    sub_right_comm _ _ a]
  exact ⟨Int.sub_floor_div_mul_nonneg _ hp, Int.sub_floor_div_mul_lt _ hp⟩
#align to_Ico_div_eq_floor toIcoDiv_eq_floor

theorem toIocDiv_eq_neg_floor (a b : α) : toIocDiv hp a b = -⌊(a + p - b) / p⌋ :=
  by
  refine' toIocDiv_eq_of_sub_zsmul_mem_Ioc hp _
  rw [Set.mem_Ioc, zsmul_eq_mul, Int.cast_neg, neg_mul, sub_neg_eq_add, ← sub_nonneg,
    sub_add_eq_sub_sub]
  refine' ⟨_, Int.sub_floor_div_mul_nonneg _ hp⟩
  rw [← add_lt_add_iff_right p, add_assoc, add_comm b, ← sub_lt_iff_lt_add, add_comm (_ * _), ←
    sub_lt_iff_lt_add]
  exact Int.sub_floor_div_mul_lt _ hp
#align to_Ioc_div_eq_neg_floor toIocDiv_eq_neg_floor

theorem toIcoDiv_zero_one (b : α) : toIcoDiv (zero_lt_one' α) 0 b = ⌊b⌋ := by
  simp [toIcoDiv_eq_floor]
#align to_Ico_div_zero_one toIcoDiv_zero_one

theorem toIcoMod_eq_add_fract_mul (a b : α) : toIcoMod hp a b = a + Int.fract ((b - a) / p) * p :=
  by
  rw [toIcoMod, toIcoDiv_eq_floor, Int.fract]
  field_simp [hp.ne.symm]
  ring
#align to_Ico_mod_eq_add_fract_mul toIcoMod_eq_add_fract_mul

theorem toIcoMod_eq_fract_mul (b : α) : toIcoMod hp 0 b = Int.fract (b / p) * p := by
  simp [toIcoMod_eq_add_fract_mul]
#align to_Ico_mod_eq_fract_mul toIcoMod_eq_fract_mul

theorem toIocMod_eq_sub_fract_mul (a b : α) :
    toIocMod hp a b = a + p - Int.fract ((a + p - b) / p) * p :=
  by
  rw [toIocMod, toIocDiv_eq_neg_floor, Int.fract]
  field_simp [hp.ne.symm]
  ring
#align to_Ioc_mod_eq_sub_fract_mul toIocMod_eq_sub_fract_mul

theorem toIcoMod_zero_one (b : α) : toIcoMod (zero_lt_one' α) 0 b = Int.fract b := by
  simp [toIcoMod_eq_add_fract_mul]
#align to_Ico_mod_zero_one toIcoMod_zero_one

end LinearOrderedField

/-! ### Lemmas about unions of translates of intervals -/


section Union

open Set Int

section LinearOrderedAddCommGroup

variable {α : Type _} [LinearOrderedAddCommGroup α] [Archimedean α] {p : α} (hp : 0 < p) (a : α)

include hp

theorem unionᵢ_Ioc_add_zsmul : (⋃ n : ℤ, Ioc (a + n • p) (a + (n + 1) • p)) = univ :=
  by
  refine' eq_univ_iff_forall.mpr fun b => mem_Union.mpr _
  rcases sub_toIocDiv_zsmul_mem_Ioc hp a b with ⟨hl, hr⟩
  refine' ⟨toIocDiv hp a b, ⟨lt_sub_iff_add_lt.mp hl, _⟩⟩
  rw [add_smul, one_smul, ← add_assoc]
  convert sub_le_iff_le_add.mp hr using 1; abel
#align Union_Ioc_add_zsmul unionᵢ_Ioc_add_zsmul

theorem unionᵢ_Ico_add_zsmul : (⋃ n : ℤ, Ico (a + n • p) (a + (n + 1) • p)) = univ :=
  by
  refine' eq_univ_iff_forall.mpr fun b => mem_Union.mpr _
  rcases sub_toIcoDiv_zsmul_mem_Ico hp a b with ⟨hl, hr⟩
  refine' ⟨toIcoDiv hp a b, ⟨le_sub_iff_add_le.mp hl, _⟩⟩
  rw [add_smul, one_smul, ← add_assoc]
  convert sub_lt_iff_lt_add.mp hr using 1; abel
#align Union_Ico_add_zsmul unionᵢ_Ico_add_zsmul

theorem unionᵢ_Icc_add_zsmul : (⋃ n : ℤ, Icc (a + n • p) (a + (n + 1) • p)) = univ := by
  simpa only [unionᵢ_Ioc_add_zsmul hp a, univ_subset_iff] using
    Union_mono fun n : ℤ => (Ioc_subset_Icc_self : Ioc (a + n • p) (a + (n + 1) • p) ⊆ Icc _ _)
#align Union_Icc_add_zsmul unionᵢ_Icc_add_zsmul

theorem unionᵢ_Ioc_zsmul : (⋃ n : ℤ, Ioc (n • p) ((n + 1) • p)) = univ := by
  simpa only [zero_add] using unionᵢ_Ioc_add_zsmul hp 0
#align Union_Ioc_zsmul unionᵢ_Ioc_zsmul

theorem unionᵢ_Ico_zsmul : (⋃ n : ℤ, Ico (n • p) ((n + 1) • p)) = univ := by
  simpa only [zero_add] using unionᵢ_Ico_add_zsmul hp 0
#align Union_Ico_zsmul unionᵢ_Ico_zsmul

theorem unionᵢ_Icc_zsmul : (⋃ n : ℤ, Icc (n • p) ((n + 1) • p)) = univ := by
  simpa only [zero_add] using unionᵢ_Icc_add_zsmul hp 0
#align Union_Icc_zsmul unionᵢ_Icc_zsmul

end LinearOrderedAddCommGroup

section LinearOrderedRing

variable {α : Type _} [LinearOrderedRing α] [Archimedean α] (a : α)

theorem unionᵢ_Ioc_add_int_cast : (⋃ n : ℤ, Ioc (a + n) (a + n + 1)) = Set.univ := by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    unionᵢ_Ioc_add_zsmul zero_lt_one a
#align Union_Ioc_add_int_cast unionᵢ_Ioc_add_int_cast

theorem unionᵢ_Ico_add_int_cast : (⋃ n : ℤ, Ico (a + n) (a + n + 1)) = Set.univ := by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    unionᵢ_Ico_add_zsmul zero_lt_one a
#align Union_Ico_add_int_cast unionᵢ_Ico_add_int_cast

theorem unionᵢ_Icc_add_int_cast : (⋃ n : ℤ, Icc (a + n) (a + n + 1)) = Set.univ := by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    unionᵢ_Icc_add_zsmul zero_lt_one a
#align Union_Icc_add_int_cast unionᵢ_Icc_add_int_cast

variable (α)

theorem unionᵢ_Ioc_int_cast : (⋃ n : ℤ, Ioc (n : α) (n + 1)) = Set.univ := by
  simpa only [zero_add] using unionᵢ_Ioc_add_int_cast (0 : α)
#align Union_Ioc_int_cast unionᵢ_Ioc_int_cast

theorem unionᵢ_Ico_int_cast : (⋃ n : ℤ, Ico (n : α) (n + 1)) = Set.univ := by
  simpa only [zero_add] using unionᵢ_Ico_add_int_cast (0 : α)
#align Union_Ico_int_cast unionᵢ_Ico_int_cast

theorem unionᵢ_Icc_int_cast : (⋃ n : ℤ, Icc (n : α) (n + 1)) = Set.univ := by
  simpa only [zero_add] using unionᵢ_Icc_add_int_cast (0 : α)
#align Union_Icc_int_cast unionᵢ_Icc_int_cast

end LinearOrderedRing

end Union

