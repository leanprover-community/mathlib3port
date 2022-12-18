/-
Copyright (c) 2022 Dagur Tómas Ásgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Tómas Ásgeirsson, Leonardo de Moura

! This file was ported from Lean 3 source module data.set.bool_indicator
! leanprover-community/mathlib commit c5c7e2760814660967bc27f0de95d190a22297f3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Image

/-!
# Indicator function valued in bool

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/988
> Any changes to this file require a corresponding PR to mathlib4.

See also `set.indicator` and `set.piecewise`.
-/


open Bool

namespace Set

variable {α : Type _} (s : Set α)

/- warning: set.bool_indicator clashes with set.boolIndicator -> Set.boolIndicator
Case conversion may be inaccurate. Consider using '#align set.bool_indicator Set.boolIndicatorₓ'. -/
#print Set.boolIndicator /-
/-- `bool_indicator` maps `x` to `tt` if `x ∈ s`, else to `ff` -/
noncomputable def boolIndicator (x : α) :=
  @ite _ (x ∈ s) (Classical.propDecidable _) true false
#align set.bool_indicator Set.boolIndicator
-/

theorem mem_iff_bool_indicator (x : α) : x ∈ s ↔ s.boolIndicator x = tt := by
  unfold bool_indicator
  split_ifs <;> tauto
#align set.mem_iff_bool_indicator Set.mem_iff_bool_indicator

theorem not_mem_iff_bool_indicator (x : α) : x ∉ s ↔ s.boolIndicator x = ff := by
  unfold bool_indicator
  split_ifs <;> tauto
#align set.not_mem_iff_bool_indicator Set.not_mem_iff_bool_indicator

theorem preimage_bool_indicator_tt : s.boolIndicator ⁻¹' {true} = s :=
  ext fun x => (s.mem_iff_bool_indicator x).symm
#align set.preimage_bool_indicator_tt Set.preimage_bool_indicator_tt

theorem preimage_bool_indicator_ff : s.boolIndicator ⁻¹' {false} = sᶜ :=
  ext fun x => (s.not_mem_iff_bool_indicator x).symm
#align set.preimage_bool_indicator_ff Set.preimage_bool_indicator_ff

open Classical

theorem preimage_bool_indicator_eq_union (t : Set Bool) :
    s.boolIndicator ⁻¹' t = (if tt ∈ t then s else ∅) ∪ if ff ∈ t then sᶜ else ∅ := by
  ext x
  dsimp [bool_indicator]
  split_ifs <;> tauto
#align set.preimage_bool_indicator_eq_union Set.preimage_bool_indicator_eq_union

theorem preimage_bool_indicator (t : Set Bool) :
    s.boolIndicator ⁻¹' t = univ ∨
      s.boolIndicator ⁻¹' t = s ∨ s.boolIndicator ⁻¹' t = sᶜ ∨ s.boolIndicator ⁻¹' t = ∅ :=
  by 
  simp only [preimage_bool_indicator_eq_union]
  split_ifs <;> simp [s.union_compl_self]
#align set.preimage_bool_indicator Set.preimage_bool_indicator

end Set

