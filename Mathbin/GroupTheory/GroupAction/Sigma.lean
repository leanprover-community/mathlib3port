/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module group_theory.group_action.sigma
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
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

variable [∀ i, SMul M (α i)] [∀ i, SMul N (α i)] (a : M) (i : ι) (b : α i) (x : Σi, α i)

@[to_additive Sigma.hasVadd]
instance : SMul M (Σi, α i) :=
  ⟨fun a => Sigma.map id fun i => (· • ·) a⟩

/- warning: sigma.smul_def -> Sigma.smul_def is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} {α : ι -> Type.{u3}} [_inst_1 : forall (i : ι), SMul.{u2, u3} M (α i)] (a : M) (x : Sigma.{u1, u3} ι (fun (i : ι) => α i)), Eq.{succ (max u1 u3)} (Sigma.{u1, u3} ι (fun (i : ι) => α i)) (SMul.smul.{u2, max u1 u3} M (Sigma.{u1, u3} ι (fun (i : ι) => α i)) (Sigma.hasSmul.{u1, u2, u3} ι M (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i)) a x) (Sigma.map.{u1, u1, u3, u3} ι ι (fun (i : ι) => α i) (fun (i : ι) => α i) (id.{succ u1} ι) (fun (i : ι) => SMul.smul.{u2, u3} M (α i) (_inst_1 i) a) x)
but is expected to have type
  forall {ι : Type.{u3}} {M : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : forall (i : ι), SMul.{u1, u2} M (α i)] (a : M) (x : Sigma.{u3, u2} ι (fun (i : ι) => α i)), Eq.{max (succ u3) (succ u2)} (Sigma.{u3, u2} ι (fun (i : ι) => α i)) (HSMul.hSMul.{u1, max u3 u2, max u3 u2} M (Sigma.{u3, u2} ι (fun (i : ι) => α i)) (Sigma.{u3, u2} ι (fun (i : ι) => α i)) (instHSMul.{u1, max u3 u2} M (Sigma.{u3, u2} ι (fun (i : ι) => α i)) (Sigma.instSMulSigma.{u3, u1, u2} ι M (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i))) a x) (Sigma.map.{u3, u3, u2, u2} ι ι (fun (i : ι) => α i) α (id.{succ u3} ι) (fun (i : ι) => (fun (x._@.Mathlib.GroupTheory.GroupAction.Sigma._hyg.231 : M) (x._@.Mathlib.GroupTheory.GroupAction.Sigma._hyg.233 : α i) => HSMul.hSMul.{u1, u2, u2} M (α i) (α (id.{succ u3} ι i)) (instHSMul.{u1, u2} M (α i) (_inst_1 i)) x._@.Mathlib.GroupTheory.GroupAction.Sigma._hyg.231 x._@.Mathlib.GroupTheory.GroupAction.Sigma._hyg.233) a) x)
Case conversion may be inaccurate. Consider using '#align sigma.smul_def Sigma.smul_defₓ'. -/
@[to_additive]
theorem smul_def : a • x = x.map id fun i => (· • ·) a :=
  rfl
#align sigma.smul_def Sigma.smul_def
#align sigma.vadd_def Sigma.vadd_def

/- warning: sigma.smul_mk -> Sigma.smul_mk is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} {α : ι -> Type.{u3}} [_inst_1 : forall (i : ι), SMul.{u2, u3} M (α i)] (a : M) (i : ι) (b : α i), Eq.{succ (max u1 u3)} (Sigma.{u1, u3} ι (fun (i : ι) => α i)) (SMul.smul.{u2, max u1 u3} M (Sigma.{u1, u3} ι (fun (i : ι) => α i)) (Sigma.hasSmul.{u1, u2, u3} ι M (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i)) a (Sigma.mk.{u1, u3} ι (fun (i : ι) => α i) i b)) (Sigma.mk.{u1, u3} ι (fun (i : ι) => α i) i (SMul.smul.{u2, u3} M (α i) (_inst_1 i) a b))
but is expected to have type
  forall {ι : Type.{u3}} {M : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : forall (i : ι), SMul.{u1, u2} M (α i)] (a : M) (i : ι) (b : α i), Eq.{max (succ u3) (succ u2)} (Sigma.{u3, u2} ι α) (HSMul.hSMul.{u1, max u2 u3, max u3 u2} M (Sigma.{u3, u2} ι α) (Sigma.{u3, u2} ι α) (instHSMul.{u1, max u3 u2} M (Sigma.{u3, u2} ι α) (Sigma.instSMulSigma.{u3, u1, u2} ι M (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i))) a (Sigma.mk.{u3, u2} ι α i b)) (Sigma.mk.{u3, u2} ι α i (HSMul.hSMul.{u1, u2, u2} M (α i) (α i) (instHSMul.{u1, u2} M (α i) (_inst_1 i)) a b))
Case conversion may be inaccurate. Consider using '#align sigma.smul_mk Sigma.smul_mkₓ'. -/
@[simp, to_additive]
theorem smul_mk : a • mk i b = ⟨i, a • b⟩ :=
  rfl
#align sigma.smul_mk Sigma.smul_mk
#align sigma.vadd_mk Sigma.vadd_mk

@[to_additive]
instance [SMul M N] [∀ i, IsScalarTower M N (α i)] : IsScalarTower M N (Σi, α i) :=
  ⟨fun a b x => by
    cases x
    rw [smul_mk, smul_mk, smul_mk, smul_assoc]⟩

@[to_additive]
instance [∀ i, SMulCommClass M N (α i)] : SMulCommClass M N (Σi, α i) :=
  ⟨fun a b x => by
    cases x
    rw [smul_mk, smul_mk, smul_mk, smul_mk, smul_comm]⟩

@[to_additive]
instance [∀ i, SMul Mᵐᵒᵖ (α i)] [∀ i, IsCentralScalar M (α i)] : IsCentralScalar M (Σi, α i) :=
  ⟨fun a x => by
    cases x
    rw [smul_mk, smul_mk, op_smul_eq_smul]⟩

/- warning: sigma.has_faithful_smul' -> Sigma.FaithfulSMul' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} {α : ι -> Type.{u3}} [_inst_1 : forall (i : ι), SMul.{u2, u3} M (α i)] (i : ι) [_inst_3 : FaithfulSMul.{u2, u3} M (α i) (_inst_1 i)], FaithfulSMul.{u2, max u1 u3} M (Sigma.{u1, u3} ι (fun (i : ι) => α i)) (Sigma.hasSmul.{u1, u2, u3} ι M (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i))
but is expected to have type
  forall {ι : Type.{u1}} {M : Type.{u3}} {α : ι -> Type.{u2}} [_inst_1 : forall (i : ι), SMul.{u3, u2} M (α i)] (i : ι) [_inst_3 : FaithfulSMul.{u3, u2} M (α i) (_inst_1 i)], FaithfulSMul.{u3, max u2 u1} M (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (Sigma.instSMulSigma.{u1, u3, u2} ι M (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i))
Case conversion may be inaccurate. Consider using '#align sigma.has_faithful_smul' Sigma.FaithfulSMul'ₓ'. -/
/-- This is not an instance because `i` becomes a metavariable. -/
@[to_additive "This is not an instance because `i` becomes a metavariable."]
protected theorem FaithfulSMul' [FaithfulSMul M (α i)] : FaithfulSMul M (Σi, α i) :=
  ⟨fun x y h => eq_of_smul_eq_smul fun a : α i => heq_iff_eq.1 (ext_iff.1 <| h <| mk i a).2⟩
#align sigma.has_faithful_smul' Sigma.FaithfulSMul'
#align sigma.has_faithful_vadd' Sigma.FaithfulVAdd'

@[to_additive]
instance [Nonempty ι] [∀ i, FaithfulSMul M (α i)] : FaithfulSMul M (Σi, α i) :=
  Nonempty.elim ‹_› fun i => Sigma.FaithfulSMul' i

end SMul

@[to_additive]
instance {m : Monoid M} [∀ i, MulAction M (α i)] : MulAction M (Σi, α i)
    where
  mul_smul a b x := by
    cases x
    rw [smul_mk, smul_mk, smul_mk, mul_smul]
  one_smul x := by
    cases x
    rw [smul_mk, one_smul]

end Sigma

