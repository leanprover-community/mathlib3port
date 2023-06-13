/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module order.conditionally_complete_lattice.group
! leanprover-community/mathlib commit c3291da49cfa65f0d43b094750541c0731edc932
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.ConditionallyCompleteLattice.Basic
import Mathbin.Algebra.Order.Group.TypeTags

/-!
# Conditionally complete lattices and groups.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/


section Group

variable {α : Type _} {ι : Sort _} {ι' : Sort _} [Nonempty ι] [Nonempty ι']
  [ConditionallyCompleteLattice α] [Group α]

#print le_mul_ciInf /-
@[to_additive]
theorem le_mul_ciInf [CovariantClass α α (· * ·) (· ≤ ·)] {a : α} {g : α} {h : ι → α}
    (H : ∀ j, a ≤ g * h j) : a ≤ g * iInf h :=
  inv_mul_le_iff_le_mul.mp <| le_ciInf fun hi => inv_mul_le_iff_le_mul.mpr <| H _
#align le_mul_cinfi le_mul_ciInf
#align le_add_cinfi le_add_ciInf
-/

#print mul_ciSup_le /-
@[to_additive]
theorem mul_ciSup_le [CovariantClass α α (· * ·) (· ≤ ·)] {a : α} {g : α} {h : ι → α}
    (H : ∀ j, g * h j ≤ a) : g * iSup h ≤ a :=
  @le_mul_ciInf αᵒᵈ _ _ _ _ _ _ _ _ H
#align mul_csupr_le mul_ciSup_le
#align add_csupr_le add_ciSup_le
-/

#print le_ciInf_mul /-
@[to_additive]
theorem le_ciInf_mul [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a : α} {g : ι → α}
    {h : α} (H : ∀ i, a ≤ g i * h) : a ≤ iInf g * h :=
  mul_inv_le_iff_le_mul.mp <| le_ciInf fun gi => mul_inv_le_iff_le_mul.mpr <| H _
#align le_cinfi_mul le_ciInf_mul
#align le_cinfi_add le_ciInf_add
-/

#print ciSup_mul_le /-
@[to_additive]
theorem ciSup_mul_le [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a : α} {g : ι → α}
    {h : α} (H : ∀ i, g i * h ≤ a) : iSup g * h ≤ a :=
  @le_ciInf_mul αᵒᵈ _ _ _ _ _ _ _ _ H
#align csupr_mul_le ciSup_mul_le
#align csupr_add_le ciSup_add_le
-/

#print le_ciInf_mul_ciInf /-
@[to_additive]
theorem le_ciInf_mul_ciInf [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a : α} {g : ι → α} {h : ι' → α}
    (H : ∀ i j, a ≤ g i * h j) : a ≤ iInf g * iInf h :=
  le_ciInf_mul fun i => le_mul_ciInf <| H _
#align le_cinfi_mul_cinfi le_ciInf_mul_ciInf
#align le_cinfi_add_cinfi le_ciInf_add_ciInf
-/

#print ciSup_mul_ciSup_le /-
@[to_additive]
theorem ciSup_mul_ciSup_le [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a : α} {g : ι → α} {h : ι' → α}
    (H : ∀ i j, g i * h j ≤ a) : iSup g * iSup h ≤ a :=
  ciSup_mul_le fun i => mul_ciSup_le <| H _
#align csupr_mul_csupr_le ciSup_mul_ciSup_le
#align csupr_add_csupr_le ciSup_add_ciSup_le
-/

end Group

