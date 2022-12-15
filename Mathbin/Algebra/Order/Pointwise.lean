/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies

! This file was ported from Lean 3 source module algebra.order.pointwise
! leanprover-community/mathlib commit aba57d4d3dae35460225919dcd82fe91355162f9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Bounds
import Mathbin.Data.Set.Pointwise.Smul

/-!
# Pointwise operations on ordered algebraic objects

This file contains lemmas about the effect of pointwise operations on sets with an order structure.

## TODO

`Sup (s • t) = Sup s • Sup t` and `Inf (s • t) = Inf s • Inf t` hold as well but
`covariant_class` is currently not polymorphic enough to state it.
-/


open Function Set

open Pointwise

variable {α : Type _}

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α]

section One

variable [One α]

@[simp, to_additive]
theorem cSup_one : sup (1 : Set α) = 1 :=
  cSup_singleton _
#align cSup_one cSup_one

@[simp, to_additive]
theorem cInf_one : inf (1 : Set α) = 1 :=
  cInf_singleton _
#align cInf_one cInf_one

end One

section Group

variable [Group α] [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
  {s t : Set α}

@[to_additive]
theorem cSup_inv (hs₀ : s.Nonempty) (hs₁ : BddBelow s) : sup s⁻¹ = (inf s)⁻¹ := by
  rw [← image_inv]
  exact ((OrderIso.inv α).map_cInf' hs₀ hs₁).symm
#align cSup_inv cSup_inv

@[to_additive]
theorem cInf_inv (hs₀ : s.Nonempty) (hs₁ : BddAbove s) : inf s⁻¹ = (sup s)⁻¹ := by
  rw [← image_inv]
  exact ((OrderIso.inv α).map_cSup' hs₀ hs₁).symm
#align cInf_inv cInf_inv

@[to_additive]
theorem cSup_mul (hs₀ : s.Nonempty) (hs₁ : BddAbove s) (ht₀ : t.Nonempty) (ht₁ : BddAbove t) :
    sup (s * t) = sup s * sup t :=
  cSup_image2_eq_cSup_cSup (fun _ => (OrderIso.mulRight _).to_galois_connection)
    (fun _ => (OrderIso.mulLeft _).to_galois_connection) hs₀ hs₁ ht₀ ht₁
#align cSup_mul cSup_mul

@[to_additive]
theorem cInf_mul (hs₀ : s.Nonempty) (hs₁ : BddBelow s) (ht₀ : t.Nonempty) (ht₁ : BddBelow t) :
    inf (s * t) = inf s * inf t :=
  cInf_image2_eq_cInf_cInf (fun _ => (OrderIso.mulRight _).symm.to_galois_connection)
    (fun _ => (OrderIso.mulLeft _).symm.to_galois_connection) hs₀ hs₁ ht₀ ht₁
#align cInf_mul cInf_mul

@[to_additive]
theorem cSup_div (hs₀ : s.Nonempty) (hs₁ : BddAbove s) (ht₀ : t.Nonempty) (ht₁ : BddBelow t) :
    sup (s / t) = sup s / inf t := by
  rw [div_eq_mul_inv, cSup_mul hs₀ hs₁ ht₀.inv ht₁.inv, cSup_inv ht₀ ht₁, div_eq_mul_inv]
#align cSup_div cSup_div

@[to_additive]
theorem cInf_div (hs₀ : s.Nonempty) (hs₁ : BddBelow s) (ht₀ : t.Nonempty) (ht₁ : BddAbove t) :
    inf (s / t) = inf s / sup t := by
  rw [div_eq_mul_inv, cInf_mul hs₀ hs₁ ht₀.inv ht₁.inv, cInf_inv ht₀ ht₁, div_eq_mul_inv]
#align cInf_div cInf_div

end Group

end ConditionallyCompleteLattice

section CompleteLattice

variable [CompleteLattice α]

section One

variable [One α]

@[simp, to_additive]
theorem Sup_one : sup (1 : Set α) = 1 :=
  Sup_singleton
#align Sup_one Sup_one

@[simp, to_additive]
theorem Inf_one : inf (1 : Set α) = 1 :=
  Inf_singleton
#align Inf_one Inf_one

end One

section Group

variable [Group α] [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
  (s t : Set α)

@[to_additive]
theorem Sup_inv (s : Set α) : sup s⁻¹ = (inf s)⁻¹ := by
  rw [← image_inv, Sup_image]
  exact ((OrderIso.inv α).map_Inf _).symm
#align Sup_inv Sup_inv

@[to_additive]
theorem Inf_inv (s : Set α) : inf s⁻¹ = (sup s)⁻¹ := by
  rw [← image_inv, Inf_image]
  exact ((OrderIso.inv α).map_Sup _).symm
#align Inf_inv Inf_inv

@[to_additive]
theorem Sup_mul : sup (s * t) = sup s * sup t :=
  (Sup_image2_eq_Sup_Sup fun _ => (OrderIso.mulRight _).to_galois_connection) fun _ =>
    (OrderIso.mulLeft _).to_galois_connection
#align Sup_mul Sup_mul

@[to_additive]
theorem Inf_mul : inf (s * t) = inf s * inf t :=
  (Inf_image2_eq_Inf_Inf fun _ => (OrderIso.mulRight _).symm.to_galois_connection) fun _ =>
    (OrderIso.mulLeft _).symm.to_galois_connection
#align Inf_mul Inf_mul

@[to_additive]
theorem Sup_div : sup (s / t) = sup s / inf t := by simp_rw [div_eq_mul_inv, Sup_mul, Sup_inv]
#align Sup_div Sup_div

@[to_additive]
theorem Inf_div : inf (s / t) = inf s / sup t := by simp_rw [div_eq_mul_inv, Inf_mul, Inf_inv]
#align Inf_div Inf_div

end Group

end CompleteLattice

namespace LinearOrderedField

variable {K : Type _} [LinearOrderedField K] {a b r : K} (hr : 0 < r)

open Set

include hr

theorem smul_Ioo : r • ioo a b = ioo (r • a) (r • b) := by
  ext x
  simp only [mem_smul_set, smul_eq_mul, mem_Ioo]
  constructor
  · rintro ⟨a, ⟨a_h_left_left, a_h_left_right⟩, rfl⟩
    constructor
    exact (mul_lt_mul_left hr).mpr a_h_left_left
    exact (mul_lt_mul_left hr).mpr a_h_left_right
  · rintro ⟨a_left, a_right⟩
    use x / r
    refine' ⟨⟨(lt_div_iff' hr).mpr a_left, (div_lt_iff' hr).mpr a_right⟩, _⟩
    rw [mul_div_cancel' _ (ne_of_gt hr)]
#align linear_ordered_field.smul_Ioo LinearOrderedField.smul_Ioo

theorem smul_Icc : r • icc a b = icc (r • a) (r • b) := by
  ext x
  simp only [mem_smul_set, smul_eq_mul, mem_Icc]
  constructor
  · rintro ⟨a, ⟨a_h_left_left, a_h_left_right⟩, rfl⟩
    constructor
    exact (mul_le_mul_left hr).mpr a_h_left_left
    exact (mul_le_mul_left hr).mpr a_h_left_right
  · rintro ⟨a_left, a_right⟩
    use x / r
    refine' ⟨⟨(le_div_iff' hr).mpr a_left, (div_le_iff' hr).mpr a_right⟩, _⟩
    rw [mul_div_cancel' _ (ne_of_gt hr)]
#align linear_ordered_field.smul_Icc LinearOrderedField.smul_Icc

theorem smul_Ico : r • ico a b = ico (r • a) (r • b) := by
  ext x
  simp only [mem_smul_set, smul_eq_mul, mem_Ico]
  constructor
  · rintro ⟨a, ⟨a_h_left_left, a_h_left_right⟩, rfl⟩
    constructor
    exact (mul_le_mul_left hr).mpr a_h_left_left
    exact (mul_lt_mul_left hr).mpr a_h_left_right
  · rintro ⟨a_left, a_right⟩
    use x / r
    refine' ⟨⟨(le_div_iff' hr).mpr a_left, (div_lt_iff' hr).mpr a_right⟩, _⟩
    rw [mul_div_cancel' _ (ne_of_gt hr)]
#align linear_ordered_field.smul_Ico LinearOrderedField.smul_Ico

theorem smul_Ioc : r • ioc a b = ioc (r • a) (r • b) := by
  ext x
  simp only [mem_smul_set, smul_eq_mul, mem_Ioc]
  constructor
  · rintro ⟨a, ⟨a_h_left_left, a_h_left_right⟩, rfl⟩
    constructor
    exact (mul_lt_mul_left hr).mpr a_h_left_left
    exact (mul_le_mul_left hr).mpr a_h_left_right
  · rintro ⟨a_left, a_right⟩
    use x / r
    refine' ⟨⟨(lt_div_iff' hr).mpr a_left, (div_le_iff' hr).mpr a_right⟩, _⟩
    rw [mul_div_cancel' _ (ne_of_gt hr)]
#align linear_ordered_field.smul_Ioc LinearOrderedField.smul_Ioc

theorem smul_Ioi : r • ioi a = ioi (r • a) := by 
  ext x
  simp only [mem_smul_set, smul_eq_mul, mem_Ioi]
  constructor
  · rintro ⟨a_w, a_h_left, rfl⟩
    exact (mul_lt_mul_left hr).mpr a_h_left
  · rintro h
    use x / r
    constructor
    exact (lt_div_iff' hr).mpr h
    exact mul_div_cancel' _ (ne_of_gt hr)
#align linear_ordered_field.smul_Ioi LinearOrderedField.smul_Ioi

theorem smul_Iio : r • iio a = iio (r • a) := by 
  ext x
  simp only [mem_smul_set, smul_eq_mul, mem_Iio]
  constructor
  · rintro ⟨a_w, a_h_left, rfl⟩
    exact (mul_lt_mul_left hr).mpr a_h_left
  · rintro h
    use x / r
    constructor
    exact (div_lt_iff' hr).mpr h
    exact mul_div_cancel' _ (ne_of_gt hr)
#align linear_ordered_field.smul_Iio LinearOrderedField.smul_Iio

theorem smul_Ici : r • ici a = ici (r • a) := by 
  ext x
  simp only [mem_smul_set, smul_eq_mul, mem_Ioi]
  constructor
  · rintro ⟨a_w, a_h_left, rfl⟩
    exact (mul_le_mul_left hr).mpr a_h_left
  · rintro h
    use x / r
    constructor
    exact (le_div_iff' hr).mpr h
    exact mul_div_cancel' _ (ne_of_gt hr)
#align linear_ordered_field.smul_Ici LinearOrderedField.smul_Ici

theorem smul_Iic : r • iic a = iic (r • a) := by 
  ext x
  simp only [mem_smul_set, smul_eq_mul, mem_Iio]
  constructor
  · rintro ⟨a_w, a_h_left, rfl⟩
    exact (mul_le_mul_left hr).mpr a_h_left
  · rintro h
    use x / r
    constructor
    exact (div_le_iff' hr).mpr h
    exact mul_div_cancel' _ (ne_of_gt hr)
#align linear_ordered_field.smul_Iic LinearOrderedField.smul_Iic

end LinearOrderedField

