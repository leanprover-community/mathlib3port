/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module data.set.opposite
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Opposite
import Mathbin.Data.Set.Image

/-!
# The opposite of a set

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The opposite of a set `s` is simply the set obtained by taking the opposite of each member of `s`.
-/


variable {α : Type _}

open Opposite

namespace Set

#print Set.op /-
/-- The opposite of a set `s` is the set obtained by taking the opposite of each member of `s`. -/
protected def op (s : Set α) : Set αᵒᵖ :=
  unop ⁻¹' s
#align set.op Set.op
-/

#print Set.unop /-
/-- The unop of a set `s` is the set obtained by taking the unop of each member of `s`. -/
protected def unop (s : Set αᵒᵖ) : Set α :=
  op ⁻¹' s
#align set.unop Set.unop
-/

#print Set.mem_op /-
@[simp]
theorem mem_op {s : Set α} {a : αᵒᵖ} : a ∈ s.op ↔ unop a ∈ s :=
  Iff.rfl
#align set.mem_op Set.mem_op
-/

#print Set.op_mem_op /-
@[simp]
theorem op_mem_op {s : Set α} {a : α} : op a ∈ s.op ↔ a ∈ s := by rw [mem_op, unop_op]
#align set.op_mem_op Set.op_mem_op
-/

#print Set.mem_unop /-
@[simp]
theorem mem_unop {s : Set αᵒᵖ} {a : α} : a ∈ s.unop ↔ op a ∈ s :=
  Iff.rfl
#align set.mem_unop Set.mem_unop
-/

#print Set.unop_mem_unop /-
@[simp]
theorem unop_mem_unop {s : Set αᵒᵖ} {a : αᵒᵖ} : unop a ∈ s.unop ↔ a ∈ s := by rw [mem_unop, op_unop]
#align set.unop_mem_unop Set.unop_mem_unop
-/

#print Set.op_unop /-
@[simp]
theorem op_unop (s : Set α) : s.op.unop = s :=
  ext (by simp only [mem_unop, op_mem_op, iff_self_iff, imp_true_iff])
#align set.op_unop Set.op_unop
-/

#print Set.unop_op /-
@[simp]
theorem unop_op (s : Set αᵒᵖ) : s.unop.op = s :=
  ext (by simp only [mem_op, unop_mem_unop, iff_self_iff, imp_true_iff])
#align set.unop_op Set.unop_op
-/

#print Set.opEquiv_self /-
/-- The members of the opposite of a set are in bijection with the members of the set itself. -/
@[simps]
def opEquiv_self (s : Set α) : s.op ≃ s :=
  ⟨fun x => ⟨unop x, x.2⟩, fun x => ⟨op x, x.2⟩, fun x => by simp, fun x => by simp⟩
#align set.op_equiv_self Set.opEquiv_self
-/

#print Set.opEquiv /-
/-- Taking opposites as an equivalence of powersets. -/
@[simps]
def opEquiv : Set α ≃ Set αᵒᵖ :=
  ⟨Set.op, Set.unop, op_unop, unop_op⟩
#align set.op_equiv Set.opEquiv
-/

#print Set.singleton_op /-
@[simp]
theorem singleton_op (x : α) : ({x} : Set α).op = {op x} :=
  ext fun y => by simpa only [mem_op, mem_singleton_iff] using unop_eq_iff_eq_op
#align set.singleton_op Set.singleton_op
-/

#print Set.singleton_unop /-
@[simp]
theorem singleton_unop (x : αᵒᵖ) : ({x} : Set αᵒᵖ).unop = {unop x} :=
  ext fun y => by simpa only [mem_unop, mem_singleton_iff] using op_eq_iff_eq_unop
#align set.singleton_unop Set.singleton_unop
-/

#print Set.singleton_op_unop /-
@[simp]
theorem singleton_op_unop (x : α) : ({op x} : Set αᵒᵖ).unop = {x} := by
  simp only [singleton_unop, Opposite.unop_op]
#align set.singleton_op_unop Set.singleton_op_unop
-/

#print Set.singleton_unop_op /-
@[simp]
theorem singleton_unop_op (x : αᵒᵖ) : ({unop x} : Set α).op = {x} := by
  simp only [singleton_op, Opposite.op_unop]
#align set.singleton_unop_op Set.singleton_unop_op
-/

end Set

