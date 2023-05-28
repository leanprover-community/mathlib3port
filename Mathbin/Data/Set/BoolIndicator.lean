/-
Copyright (c) 2022 Dagur Tómas Ásgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Tómas Ásgeirsson, Leonardo de Moura

! This file was ported from Lean 3 source module data.set.bool_indicator
! leanprover-community/mathlib commit 448144f7ae193a8990cb7473c9e9a01990f64ac7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Image

/-!
# Indicator function valued in bool

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

See also `set.indicator` and `set.piecewise`.
-/


open Bool

namespace Set

variable {α : Type _} (s : Set α)

#print Set.boolIndicator /-
/-- `bool_indicator` maps `x` to `tt` if `x ∈ s`, else to `ff` -/
noncomputable def boolIndicator (x : α) :=
  @ite _ (x ∈ s) (Classical.propDecidable _) true false
#align set.bool_indicator Set.boolIndicator
-/

#print Set.mem_iff_boolIndicator /-
theorem mem_iff_boolIndicator (x : α) : x ∈ s ↔ s.boolIndicator x = true := by
  unfold bool_indicator; split_ifs <;> tauto
#align set.mem_iff_bool_indicator Set.mem_iff_boolIndicator
-/

#print Set.not_mem_iff_boolIndicator /-
theorem not_mem_iff_boolIndicator (x : α) : x ∉ s ↔ s.boolIndicator x = false := by
  unfold bool_indicator; split_ifs <;> tauto
#align set.not_mem_iff_bool_indicator Set.not_mem_iff_boolIndicator
-/

/- warning: set.preimage_bool_indicator_tt clashes with set.preimage_bool_indicator_true -> Set.preimage_boolIndicator_true
Case conversion may be inaccurate. Consider using '#align set.preimage_bool_indicator_tt Set.preimage_boolIndicator_trueₓ'. -/
#print Set.preimage_boolIndicator_true /-
theorem preimage_boolIndicator_true : s.boolIndicator ⁻¹' {true} = s :=
  ext fun x => (s.mem_iff_boolIndicator x).symm
#align set.preimage_bool_indicator_tt Set.preimage_boolIndicator_true
-/

/- warning: set.preimage_bool_indicator_ff clashes with set.preimage_bool_indicator_false -> Set.preimage_boolIndicator_false
Case conversion may be inaccurate. Consider using '#align set.preimage_bool_indicator_ff Set.preimage_boolIndicator_falseₓ'. -/
theorem preimage_boolIndicator_false : s.boolIndicator ⁻¹' {false} = sᶜ :=
  ext fun x => (s.not_mem_iff_boolIndicator x).symm
#align set.preimage_bool_indicator_ff Set.preimage_boolIndicator_false

open scoped Classical

theorem preimage_boolIndicator_eq_union (t : Set Bool) :
    s.boolIndicator ⁻¹' t = (if true ∈ t then s else ∅) ∪ if false ∈ t then sᶜ else ∅ :=
  by
  ext x
  dsimp [bool_indicator]
  split_ifs <;> tauto
#align set.preimage_bool_indicator_eq_union Set.preimage_boolIndicator_eq_union

theorem preimage_boolIndicator (t : Set Bool) :
    s.boolIndicator ⁻¹' t = univ ∨
      s.boolIndicator ⁻¹' t = s ∨ s.boolIndicator ⁻¹' t = sᶜ ∨ s.boolIndicator ⁻¹' t = ∅ :=
  by
  simp only [preimage_bool_indicator_eq_union]
  split_ifs <;> simp [s.union_compl_self]
#align set.preimage_bool_indicator Set.preimage_boolIndicator

end Set

