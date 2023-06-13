/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module group_theory.group_action.sigma
! leanprover-community/mathlib commit 448144f7ae193a8990cb7473c9e9a01990f64ac7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.GroupAction.Defs

/-!
# Sigma instances for additive and multiplicative actions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines instances for arbitrary sum of additive and multiplicative actions.

## See also

* `group_theory.group_action.pi`
* `group_theory.group_action.prod`
* `group_theory.group_action.sum`
-/


variable {ι : Type _} {M N : Type _} {α : ι → Type _}

namespace Sigma

section SMul

variable [∀ i, SMul M (α i)] [∀ i, SMul N (α i)] (a : M) (i : ι) (b : α i) (x : Σ i, α i)

@[to_additive Sigma.hasVadd]
instance : SMul M (Σ i, α i) :=
  ⟨fun a => Sigma.map id fun i => (· • ·) a⟩

#print Sigma.smul_def /-
@[to_additive]
theorem smul_def : a • x = x.map id fun i => (· • ·) a :=
  rfl
#align sigma.smul_def Sigma.smul_def
#align sigma.vadd_def Sigma.vadd_def
-/

#print Sigma.smul_mk /-
@[simp, to_additive]
theorem smul_mk : a • mk i b = ⟨i, a • b⟩ :=
  rfl
#align sigma.smul_mk Sigma.smul_mk
#align sigma.vadd_mk Sigma.vadd_mk
-/

@[to_additive]
instance [SMul M N] [∀ i, IsScalarTower M N (α i)] : IsScalarTower M N (Σ i, α i) :=
  ⟨fun a b x => by cases x; rw [smul_mk, smul_mk, smul_mk, smul_assoc]⟩

@[to_additive]
instance [∀ i, SMulCommClass M N (α i)] : SMulCommClass M N (Σ i, α i) :=
  ⟨fun a b x => by cases x; rw [smul_mk, smul_mk, smul_mk, smul_mk, smul_comm]⟩

@[to_additive]
instance [∀ i, SMul Mᵐᵒᵖ (α i)] [∀ i, IsCentralScalar M (α i)] : IsCentralScalar M (Σ i, α i) :=
  ⟨fun a x => by cases x; rw [smul_mk, smul_mk, op_smul_eq_smul]⟩

#print Sigma.FaithfulSMul' /-
/-- This is not an instance because `i` becomes a metavariable. -/
@[to_additive "This is not an instance because `i` becomes a metavariable."]
protected theorem FaithfulSMul' [FaithfulSMul M (α i)] : FaithfulSMul M (Σ i, α i) :=
  ⟨fun x y h => eq_of_smul_eq_smul fun a : α i => heq_iff_eq.1 (ext_iff.1 <| h <| mk i a).2⟩
#align sigma.has_faithful_smul' Sigma.FaithfulSMul'
#align sigma.has_faithful_vadd' Sigma.FaithfulVAdd'
-/

@[to_additive]
instance [Nonempty ι] [∀ i, FaithfulSMul M (α i)] : FaithfulSMul M (Σ i, α i) :=
  Nonempty.elim ‹_› fun i => Sigma.FaithfulSMul' i

end SMul

@[to_additive]
instance {m : Monoid M} [∀ i, MulAction M (α i)] : MulAction M (Σ i, α i)
    where
  mul_smul a b x := by cases x; rw [smul_mk, smul_mk, smul_mk, mul_smul]
  one_smul x := by cases x; rw [smul_mk, one_smul]

end Sigma

