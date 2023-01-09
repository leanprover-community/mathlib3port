/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Eric Wieser

! This file was ported from Lean 3 source module data.real.pointwise
! leanprover-community/mathlib commit 40acfb6aa7516ffe6f91136691df012a64683390
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Module
import Mathbin.Data.Real.Basic

/-!
# Pointwise operations on sets of reals

This file relates `Inf (a • s)`/`Sup (a • s)` with `a • Inf s`/`a • Sup s` for `s : set ℝ`.

From these, it relates `⨅ i, a • f i` / `⨆ i, a • f i` with `a • (⨅ i, f i)` / `a • (⨆ i, f i)`,
and provides lemmas about distributing `*` over `⨅` and `⨆`.

# TODO

This is true more generally for conditionally complete linear order whose default value is `0`. We
don't have those yet.
-/


open Set

open Pointwise

variable {ι : Sort _} {α : Type _} [LinearOrderedField α]

section MulActionWithZero

variable [MulActionWithZero α ℝ] [OrderedSmul α ℝ] {a : α}

theorem Real.Inf_smul_of_nonneg (ha : 0 ≤ a) (s : Set ℝ) : infₛ (a • s) = a • infₛ s :=
  by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.Inf_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact cinfₛ_singleton 0
  by_cases BddBelow s
  · exact ((OrderIso.smulLeft ℝ ha').map_cInf' hs h).symm
  ·
    rw [Real.Inf_of_not_bdd_below (mt (bdd_below_smul_iff_of_pos ha').1 h),
      Real.Inf_of_not_bdd_below h, smul_zero]
#align real.Inf_smul_of_nonneg Real.Inf_smul_of_nonneg

theorem Real.smul_infi_of_nonneg (ha : 0 ≤ a) (f : ι → ℝ) : (a • ⨅ i, f i) = ⨅ i, a • f i :=
  (Real.Inf_smul_of_nonneg ha _).symm.trans <| congr_arg infₛ <| (range_comp _ _).symm
#align real.smul_infi_of_nonneg Real.smul_infi_of_nonneg

theorem Real.Sup_smul_of_nonneg (ha : 0 ≤ a) (s : Set ℝ) : supₛ (a • s) = a • supₛ s :=
  by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.Sup_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csupₛ_singleton 0
  by_cases BddAbove s
  · exact ((OrderIso.smulLeft ℝ ha').map_cSup' hs h).symm
  ·
    rw [Real.Sup_of_not_bdd_above (mt (bdd_above_smul_iff_of_pos ha').1 h),
      Real.Sup_of_not_bdd_above h, smul_zero]
#align real.Sup_smul_of_nonneg Real.Sup_smul_of_nonneg

theorem Real.smul_supr_of_nonneg (ha : 0 ≤ a) (f : ι → ℝ) : (a • ⨆ i, f i) = ⨆ i, a • f i :=
  (Real.Sup_smul_of_nonneg ha _).symm.trans <| congr_arg supₛ <| (range_comp _ _).symm
#align real.smul_supr_of_nonneg Real.smul_supr_of_nonneg

end MulActionWithZero

section Module

variable [Module α ℝ] [OrderedSmul α ℝ] {a : α}

theorem Real.Inf_smul_of_nonpos (ha : a ≤ 0) (s : Set ℝ) : infₛ (a • s) = a • supₛ s :=
  by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.Inf_empty, Real.Sup_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact cinfₛ_singleton 0
  by_cases BddAbove s
  · exact ((OrderIso.smulLeftDual ℝ ha').map_cSup' hs h).symm
  ·
    rw [Real.Inf_of_not_bdd_below (mt (bdd_below_smul_iff_of_neg ha').1 h),
      Real.Sup_of_not_bdd_above h, smul_zero]
#align real.Inf_smul_of_nonpos Real.Inf_smul_of_nonpos

theorem Real.smul_supr_of_nonpos (ha : a ≤ 0) (f : ι → ℝ) : (a • ⨆ i, f i) = ⨅ i, a • f i :=
  (Real.Inf_smul_of_nonpos ha _).symm.trans <| congr_arg infₛ <| (range_comp _ _).symm
#align real.smul_supr_of_nonpos Real.smul_supr_of_nonpos

theorem Real.Sup_smul_of_nonpos (ha : a ≤ 0) (s : Set ℝ) : supₛ (a • s) = a • infₛ s :=
  by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.Sup_empty, Real.Inf_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csupₛ_singleton 0
  by_cases BddBelow s
  · exact ((OrderIso.smulLeftDual ℝ ha').map_cInf' hs h).symm
  ·
    rw [Real.Sup_of_not_bdd_above (mt (bdd_above_smul_iff_of_neg ha').1 h),
      Real.Inf_of_not_bdd_below h, smul_zero]
#align real.Sup_smul_of_nonpos Real.Sup_smul_of_nonpos

theorem Real.smul_infi_of_nonpos (ha : a ≤ 0) (f : ι → ℝ) : (a • ⨅ i, f i) = ⨆ i, a • f i :=
  (Real.Sup_smul_of_nonpos ha _).symm.trans <| congr_arg supₛ <| (range_comp _ _).symm
#align real.smul_infi_of_nonpos Real.smul_infi_of_nonpos

end Module

/-! ## Special cases for real multiplication -/


section Mul

variable {r : ℝ}

theorem Real.mul_infi_of_nonneg (ha : 0 ≤ r) (f : ι → ℝ) : (r * ⨅ i, f i) = ⨅ i, r * f i :=
  Real.smul_infi_of_nonneg ha f
#align real.mul_infi_of_nonneg Real.mul_infi_of_nonneg

theorem Real.mul_supr_of_nonneg (ha : 0 ≤ r) (f : ι → ℝ) : (r * ⨆ i, f i) = ⨆ i, r * f i :=
  Real.smul_supr_of_nonneg ha f
#align real.mul_supr_of_nonneg Real.mul_supr_of_nonneg

theorem Real.mul_infi_of_nonpos (ha : r ≤ 0) (f : ι → ℝ) : (r * ⨅ i, f i) = ⨆ i, r * f i :=
  Real.smul_infi_of_nonpos ha f
#align real.mul_infi_of_nonpos Real.mul_infi_of_nonpos

theorem Real.mul_supr_of_nonpos (ha : r ≤ 0) (f : ι → ℝ) : (r * ⨆ i, f i) = ⨅ i, r * f i :=
  Real.smul_supr_of_nonpos ha f
#align real.mul_supr_of_nonpos Real.mul_supr_of_nonpos

theorem Real.infi_mul_of_nonneg (ha : 0 ≤ r) (f : ι → ℝ) : (⨅ i, f i) * r = ⨅ i, f i * r := by
  simp only [Real.mul_infi_of_nonneg ha, mul_comm]
#align real.infi_mul_of_nonneg Real.infi_mul_of_nonneg

theorem Real.supr_mul_of_nonneg (ha : 0 ≤ r) (f : ι → ℝ) : (⨆ i, f i) * r = ⨆ i, f i * r := by
  simp only [Real.mul_supr_of_nonneg ha, mul_comm]
#align real.supr_mul_of_nonneg Real.supr_mul_of_nonneg

theorem Real.infi_mul_of_nonpos (ha : r ≤ 0) (f : ι → ℝ) : (⨅ i, f i) * r = ⨆ i, f i * r := by
  simp only [Real.mul_infi_of_nonpos ha, mul_comm]
#align real.infi_mul_of_nonpos Real.infi_mul_of_nonpos

theorem Real.supr_mul_of_nonpos (ha : r ≤ 0) (f : ι → ℝ) : (⨆ i, f i) * r = ⨅ i, f i * r := by
  simp only [Real.mul_supr_of_nonpos ha, mul_comm]
#align real.supr_mul_of_nonpos Real.supr_mul_of_nonpos

end Mul

