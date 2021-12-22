import Mathbin.Algebra.Order.Module
import Mathbin.Algebra.Pointwise
import Mathbin.Data.Real.Basic

/-!
# Pointwise operations on sets of reals

This file relates `Inf (a • s)`/`Sup (a • s)` with `a • Inf s`/`a • Sup s` for `s : set ℝ`.

# TODO

This is true more generally for conditionally complete linear order whose default value is `0`. We
don't have those yet.
-/


open Set

open_locale Pointwise

variable {α : Type _} [LinearOrderedField α]

section MulActionWithZero

variable [MulActionWithZero α ℝ] [OrderedSmul α ℝ] {a : α}

theorem Real.Inf_smul_of_nonneg (ha : 0 ≤ a) (s : Set ℝ) : Inf (a • s) = a • Inf s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  ·
    rw [smul_set_empty, Real.Inf_empty, smul_zero']
  obtain rfl | ha' := ha.eq_or_lt
  ·
    rw [zero_smul_set hs, zero_smul]
    exact cInf_singleton 0
  by_cases' BddBelow s
  ·
    exact ((OrderIso.smulLeft ℝ ha').map_cInf' hs h).symm
  ·
    rw [Real.Inf_of_not_bdd_below (mt (bdd_below_smul_iff_of_pos ha').1 h), Real.Inf_of_not_bdd_below h, smul_zero']

theorem Real.Sup_smul_of_nonneg (ha : 0 ≤ a) (s : Set ℝ) : Sup (a • s) = a • Sup s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  ·
    rw [smul_set_empty, Real.Sup_empty, smul_zero']
  obtain rfl | ha' := ha.eq_or_lt
  ·
    rw [zero_smul_set hs, zero_smul]
    exact cSup_singleton 0
  by_cases' BddAbove s
  ·
    exact ((OrderIso.smulLeft ℝ ha').map_cSup' hs h).symm
  ·
    rw [Real.Sup_of_not_bdd_above (mt (bdd_above_smul_iff_of_pos ha').1 h), Real.Sup_of_not_bdd_above h, smul_zero']

end MulActionWithZero

section Module

variable [Module α ℝ] [OrderedSmul α ℝ] {a : α}

theorem Real.Inf_smul_of_nonpos (ha : a ≤ 0) (s : Set ℝ) : Inf (a • s) = a • Sup s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  ·
    rw [smul_set_empty, Real.Inf_empty, Real.Sup_empty, smul_zero']
  obtain rfl | ha' := ha.eq_or_lt
  ·
    rw [zero_smul_set hs, zero_smul]
    exact cInf_singleton 0
  by_cases' BddAbove s
  ·
    exact ((OrderIso.smulLeftDual ℝ ha').map_cSup' hs h).symm
  ·
    rw [Real.Inf_of_not_bdd_below (mt (bdd_below_smul_iff_of_neg ha').1 h), Real.Sup_of_not_bdd_above h, smul_zero']

theorem Real.Sup_smul_of_nonpos (ha : a ≤ 0) (s : Set ℝ) : Sup (a • s) = a • Inf s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  ·
    rw [smul_set_empty, Real.Sup_empty, Real.Inf_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  ·
    rw [zero_smul_set hs, zero_smul]
    exact cSup_singleton 0
  by_cases' BddBelow s
  ·
    exact ((OrderIso.smulLeftDual ℝ ha').map_cInf' hs h).symm
  ·
    rw [Real.Sup_of_not_bdd_above (mt (bdd_above_smul_iff_of_neg ha').1 h), Real.Inf_of_not_bdd_below h, smul_zero]

end Module

