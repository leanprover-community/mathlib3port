/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Eric Wieser
-/
import Algebra.Order.Module
import Data.Real.Basic

#align_import data.real.pointwise from "leanprover-community/mathlib"@"34ee86e6a59d911a8e4f89b68793ee7577ae79c7"

/-!
# Pointwise operations on sets of reals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file relates `Inf (a • s)`/`Sup (a • s)` with `a • Inf s`/`a • Sup s` for `s : set ℝ`.

From these, it relates `⨅ i, a • f i` / `⨆ i, a • f i` with `a • (⨅ i, f i)` / `a • (⨆ i, f i)`,
and provides lemmas about distributing `*` over `⨅` and `⨆`.

# TODO

This is true more generally for conditionally complete linear order whose default value is `0`. We
don't have those yet.
-/


open Set

open scoped Pointwise

variable {ι : Sort _} {α : Type _} [LinearOrderedField α]

section MulActionWithZero

variable [MulActionWithZero α ℝ] [OrderedSMul α ℝ] {a : α}

#print Real.sInf_smul_of_nonneg /-
theorem Real.sInf_smul_of_nonneg (ha : 0 ≤ a) (s : Set ℝ) : sInf (a • s) = a • sInf s :=
  by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.sInf_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csInf_singleton 0
  by_cases BddBelow s
  · exact ((OrderIso.smulRight ℝ ha').map_csInf' hs h).symm
  ·
    rw [Real.sInf_of_not_bddBelow (mt (bddBelow_smul_iff_of_pos ha').1 h),
      Real.sInf_of_not_bddBelow h, smul_zero]
#align real.Inf_smul_of_nonneg Real.sInf_smul_of_nonneg
-/

#print Real.smul_iInf_of_nonneg /-
theorem Real.smul_iInf_of_nonneg (ha : 0 ≤ a) (f : ι → ℝ) : (a • ⨅ i, f i) = ⨅ i, a • f i :=
  (Real.sInf_smul_of_nonneg ha _).symm.trans <| congr_arg sInf <| (range_comp _ _).symm
#align real.smul_infi_of_nonneg Real.smul_iInf_of_nonneg
-/

#print Real.sSup_smul_of_nonneg /-
theorem Real.sSup_smul_of_nonneg (ha : 0 ≤ a) (s : Set ℝ) : sSup (a • s) = a • sSup s :=
  by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.sSup_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csSup_singleton 0
  by_cases BddAbove s
  · exact ((OrderIso.smulRight ℝ ha').map_csSup' hs h).symm
  ·
    rw [Real.sSup_of_not_bddAbove (mt (bddAbove_smul_iff_of_pos ha').1 h),
      Real.sSup_of_not_bddAbove h, smul_zero]
#align real.Sup_smul_of_nonneg Real.sSup_smul_of_nonneg
-/

#print Real.smul_iSup_of_nonneg /-
theorem Real.smul_iSup_of_nonneg (ha : 0 ≤ a) (f : ι → ℝ) : (a • ⨆ i, f i) = ⨆ i, a • f i :=
  (Real.sSup_smul_of_nonneg ha _).symm.trans <| congr_arg sSup <| (range_comp _ _).symm
#align real.smul_supr_of_nonneg Real.smul_iSup_of_nonneg
-/

end MulActionWithZero

section Module

variable [Module α ℝ] [OrderedSMul α ℝ] {a : α}

#print Real.sInf_smul_of_nonpos /-
theorem Real.sInf_smul_of_nonpos (ha : a ≤ 0) (s : Set ℝ) : sInf (a • s) = a • sSup s :=
  by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.sInf_empty, Real.sSup_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csInf_singleton 0
  by_cases BddAbove s
  · exact ((OrderIso.smulRightDual ℝ ha').map_csSup' hs h).symm
  ·
    rw [Real.sInf_of_not_bddBelow (mt (bddBelow_smul_iff_of_neg ha').1 h),
      Real.sSup_of_not_bddAbove h, smul_zero]
#align real.Inf_smul_of_nonpos Real.sInf_smul_of_nonpos
-/

#print Real.smul_iSup_of_nonpos /-
theorem Real.smul_iSup_of_nonpos (ha : a ≤ 0) (f : ι → ℝ) : (a • ⨆ i, f i) = ⨅ i, a • f i :=
  (Real.sInf_smul_of_nonpos ha _).symm.trans <| congr_arg sInf <| (range_comp _ _).symm
#align real.smul_supr_of_nonpos Real.smul_iSup_of_nonpos
-/

#print Real.sSup_smul_of_nonpos /-
theorem Real.sSup_smul_of_nonpos (ha : a ≤ 0) (s : Set ℝ) : sSup (a • s) = a • sInf s :=
  by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.sSup_empty, Real.sInf_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csSup_singleton 0
  by_cases BddBelow s
  · exact ((OrderIso.smulRightDual ℝ ha').map_csInf' hs h).symm
  ·
    rw [Real.sSup_of_not_bddAbove (mt (bddAbove_smul_iff_of_neg ha').1 h),
      Real.sInf_of_not_bddBelow h, smul_zero]
#align real.Sup_smul_of_nonpos Real.sSup_smul_of_nonpos
-/

#print Real.smul_iInf_of_nonpos /-
theorem Real.smul_iInf_of_nonpos (ha : a ≤ 0) (f : ι → ℝ) : (a • ⨅ i, f i) = ⨆ i, a • f i :=
  (Real.sSup_smul_of_nonpos ha _).symm.trans <| congr_arg sSup <| (range_comp _ _).symm
#align real.smul_infi_of_nonpos Real.smul_iInf_of_nonpos
-/

end Module

/-! ## Special cases for real multiplication -/


section Mul

variable {r : ℝ}

#print Real.mul_iInf_of_nonneg /-
theorem Real.mul_iInf_of_nonneg (ha : 0 ≤ r) (f : ι → ℝ) : (r * ⨅ i, f i) = ⨅ i, r * f i :=
  Real.smul_iInf_of_nonneg ha f
#align real.mul_infi_of_nonneg Real.mul_iInf_of_nonneg
-/

#print Real.mul_iSup_of_nonneg /-
theorem Real.mul_iSup_of_nonneg (ha : 0 ≤ r) (f : ι → ℝ) : (r * ⨆ i, f i) = ⨆ i, r * f i :=
  Real.smul_iSup_of_nonneg ha f
#align real.mul_supr_of_nonneg Real.mul_iSup_of_nonneg
-/

#print Real.mul_iInf_of_nonpos /-
theorem Real.mul_iInf_of_nonpos (ha : r ≤ 0) (f : ι → ℝ) : (r * ⨅ i, f i) = ⨆ i, r * f i :=
  Real.smul_iInf_of_nonpos ha f
#align real.mul_infi_of_nonpos Real.mul_iInf_of_nonpos
-/

#print Real.mul_iSup_of_nonpos /-
theorem Real.mul_iSup_of_nonpos (ha : r ≤ 0) (f : ι → ℝ) : (r * ⨆ i, f i) = ⨅ i, r * f i :=
  Real.smul_iSup_of_nonpos ha f
#align real.mul_supr_of_nonpos Real.mul_iSup_of_nonpos
-/

#print Real.iInf_mul_of_nonneg /-
theorem Real.iInf_mul_of_nonneg (ha : 0 ≤ r) (f : ι → ℝ) : (⨅ i, f i) * r = ⨅ i, f i * r := by
  simp only [Real.mul_iInf_of_nonneg ha, mul_comm]
#align real.infi_mul_of_nonneg Real.iInf_mul_of_nonneg
-/

#print Real.iSup_mul_of_nonneg /-
theorem Real.iSup_mul_of_nonneg (ha : 0 ≤ r) (f : ι → ℝ) : (⨆ i, f i) * r = ⨆ i, f i * r := by
  simp only [Real.mul_iSup_of_nonneg ha, mul_comm]
#align real.supr_mul_of_nonneg Real.iSup_mul_of_nonneg
-/

#print Real.iInf_mul_of_nonpos /-
theorem Real.iInf_mul_of_nonpos (ha : r ≤ 0) (f : ι → ℝ) : (⨅ i, f i) * r = ⨆ i, f i * r := by
  simp only [Real.mul_iInf_of_nonpos ha, mul_comm]
#align real.infi_mul_of_nonpos Real.iInf_mul_of_nonpos
-/

#print Real.iSup_mul_of_nonpos /-
theorem Real.iSup_mul_of_nonpos (ha : r ≤ 0) (f : ι → ℝ) : (⨆ i, f i) * r = ⨅ i, f i * r := by
  simp only [Real.mul_iSup_of_nonpos ha, mul_comm]
#align real.supr_mul_of_nonpos Real.iSup_mul_of_nonpos
-/

end Mul

