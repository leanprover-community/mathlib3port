/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser

! This file was ported from Lean 3 source module group_theory.group_action.prod
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Prod
import Mathbin.GroupTheory.GroupAction.Defs

/-!
# Prod instances for additive and multiplicative actions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines instances for binary product of additive and multiplicative actions and provides
scalar multiplication as a homomorphism from `α × β` to `β`.

## Main declarations

* `smul_mul_hom`/`smul_monoid_hom`: Scalar multiplication bundled as a multiplicative/monoid
  homomorphism.

## See also

* `group_theory.group_action.option`
* `group_theory.group_action.pi`
* `group_theory.group_action.sigma`
* `group_theory.group_action.sum`
-/


variable {M N P E α β : Type _}

namespace Prod

section

variable [SMul M α] [SMul M β] [SMul N α] [SMul N β] (a : M) (x : α × β)

@[to_additive Prod.hasVadd]
instance : SMul M (α × β) :=
  ⟨fun a p => (a • p.1, a • p.2)⟩

/- warning: prod.smul_fst -> Prod.smul_fst is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : SMul.{u1, u2} M α] [_inst_2 : SMul.{u1, u3} M β] (a : M) (x : Prod.{u2, u3} α β), Eq.{succ u2} α (Prod.fst.{u2, u3} α β (SMul.smul.{u1, max u2 u3} M (Prod.{u2, u3} α β) (Prod.smul.{u1, u2, u3} M α β _inst_1 _inst_2) a x)) (SMul.smul.{u1, u2} M α _inst_1 a (Prod.fst.{u2, u3} α β x))
but is expected to have type
  forall {M : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u3} M α] [_inst_2 : SMul.{u1, u2} M β] (a : M) (x : Prod.{u3, u2} α β), Eq.{succ u3} α (Prod.fst.{u3, u2} α β (HSMul.hSMul.{u1, max u3 u2, max u3 u2} M (Prod.{u3, u2} α β) (Prod.{u3, u2} α β) (instHSMul.{u1, max u3 u2} M (Prod.{u3, u2} α β) (Prod.smul.{u1, u3, u2} M α β _inst_1 _inst_2)) a x)) (HSMul.hSMul.{u1, u3, u3} M α α (instHSMul.{u1, u3} M α _inst_1) a (Prod.fst.{u3, u2} α β x))
Case conversion may be inaccurate. Consider using '#align prod.smul_fst Prod.smul_fstₓ'. -/
@[simp, to_additive]
theorem smul_fst : (a • x).1 = a • x.1 :=
  rfl
#align prod.smul_fst Prod.smul_fst
#align prod.vadd_fst Prod.vadd_fst

#print Prod.smul_snd /-
@[simp, to_additive]
theorem smul_snd : (a • x).2 = a • x.2 :=
  rfl
#align prod.smul_snd Prod.smul_snd
#align prod.vadd_snd Prod.vadd_snd
-/

/- warning: prod.smul_mk -> Prod.smul_mk is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : SMul.{u1, u2} M α] [_inst_2 : SMul.{u1, u3} M β] (a : M) (b : α) (c : β), Eq.{succ (max u2 u3)} (Prod.{u2, u3} α β) (SMul.smul.{u1, max u2 u3} M (Prod.{u2, u3} α β) (Prod.smul.{u1, u2, u3} M α β _inst_1 _inst_2) a (Prod.mk.{u2, u3} α β b c)) (Prod.mk.{u2, u3} α β (SMul.smul.{u1, u2} M α _inst_1 a b) (SMul.smul.{u1, u3} M β _inst_2 a c))
but is expected to have type
  forall {M : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u3} M α] [_inst_2 : SMul.{u1, u2} M β] (a : M) (b : α) (c : β), Eq.{max (succ u3) (succ u2)} (Prod.{u3, u2} α β) (HSMul.hSMul.{u1, max u2 u3, max u3 u2} M (Prod.{u3, u2} α β) (Prod.{u3, u2} α β) (instHSMul.{u1, max u3 u2} M (Prod.{u3, u2} α β) (Prod.smul.{u1, u3, u2} M α β _inst_1 _inst_2)) a (Prod.mk.{u3, u2} α β b c)) (Prod.mk.{u3, u2} α β (HSMul.hSMul.{u1, u3, u3} M α α (instHSMul.{u1, u3} M α _inst_1) a b) (HSMul.hSMul.{u1, u2, u2} M β β (instHSMul.{u1, u2} M β _inst_2) a c))
Case conversion may be inaccurate. Consider using '#align prod.smul_mk Prod.smul_mkₓ'. -/
@[simp, to_additive]
theorem smul_mk (a : M) (b : α) (c : β) : a • (b, c) = (a • b, a • c) :=
  rfl
#align prod.smul_mk Prod.smul_mk
#align prod.vadd_mk Prod.vadd_mk

/- warning: prod.smul_def -> Prod.smul_def is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : SMul.{u1, u2} M α] [_inst_2 : SMul.{u1, u3} M β] (a : M) (x : Prod.{u2, u3} α β), Eq.{succ (max u2 u3)} (Prod.{u2, u3} α β) (SMul.smul.{u1, max u2 u3} M (Prod.{u2, u3} α β) (Prod.smul.{u1, u2, u3} M α β _inst_1 _inst_2) a x) (Prod.mk.{u2, u3} α β (SMul.smul.{u1, u2} M α _inst_1 a (Prod.fst.{u2, u3} α β x)) (SMul.smul.{u1, u3} M β _inst_2 a (Prod.snd.{u2, u3} α β x)))
but is expected to have type
  forall {M : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u3} M α] [_inst_2 : SMul.{u1, u2} M β] (a : M) (x : Prod.{u3, u2} α β), Eq.{max (succ u3) (succ u2)} (Prod.{u3, u2} α β) (HSMul.hSMul.{u1, max u3 u2, max u3 u2} M (Prod.{u3, u2} α β) (Prod.{u3, u2} α β) (instHSMul.{u1, max u3 u2} M (Prod.{u3, u2} α β) (Prod.smul.{u1, u3, u2} M α β _inst_1 _inst_2)) a x) (Prod.mk.{u3, u2} α β (HSMul.hSMul.{u1, u3, u3} M α α (instHSMul.{u1, u3} M α _inst_1) a (Prod.fst.{u3, u2} α β x)) (HSMul.hSMul.{u1, u2, u2} M β β (instHSMul.{u1, u2} M β _inst_2) a (Prod.snd.{u3, u2} α β x)))
Case conversion may be inaccurate. Consider using '#align prod.smul_def Prod.smul_defₓ'. -/
@[to_additive]
theorem smul_def (a : M) (x : α × β) : a • x = (a • x.1, a • x.2) :=
  rfl
#align prod.smul_def Prod.smul_def
#align prod.vadd_def Prod.vadd_def

/- warning: prod.smul_swap -> Prod.smul_swap is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : SMul.{u1, u2} M α] [_inst_2 : SMul.{u1, u3} M β] (a : M) (x : Prod.{u2, u3} α β), Eq.{max (succ u3) (succ u2)} (Prod.{u3, u2} β α) (Prod.swap.{u2, u3} α β (SMul.smul.{u1, max u2 u3} M (Prod.{u2, u3} α β) (Prod.smul.{u1, u2, u3} M α β _inst_1 _inst_2) a x)) (SMul.smul.{u1, max u3 u2} M (Prod.{u3, u2} β α) (Prod.smul.{u1, u3, u2} M β α _inst_2 _inst_1) a (Prod.swap.{u2, u3} α β x))
but is expected to have type
  forall {M : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u3} M α] [_inst_2 : SMul.{u1, u2} M β] (a : M) (x : Prod.{u3, u2} α β), Eq.{max (succ u3) (succ u2)} (Prod.{u2, u3} β α) (Prod.swap.{u3, u2} α β (HSMul.hSMul.{u1, max u3 u2, max u3 u2} M (Prod.{u3, u2} α β) (Prod.{u3, u2} α β) (instHSMul.{u1, max u3 u2} M (Prod.{u3, u2} α β) (Prod.smul.{u1, u3, u2} M α β _inst_1 _inst_2)) a x)) (HSMul.hSMul.{u1, max u3 u2, max u3 u2} M (Prod.{u2, u3} β α) (Prod.{u2, u3} β α) (instHSMul.{u1, max u3 u2} M (Prod.{u2, u3} β α) (Prod.smul.{u1, u2, u3} M β α _inst_2 _inst_1)) a (Prod.swap.{u3, u2} α β x))
Case conversion may be inaccurate. Consider using '#align prod.smul_swap Prod.smul_swapₓ'. -/
@[simp, to_additive]
theorem smul_swap : (a • x).swap = a • x.swap :=
  rfl
#align prod.smul_swap Prod.smul_swap
#align prod.vadd_swap Prod.vadd_swap

/- warning: prod.smul_zero_mk -> Prod.smul_zero_mk is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {β : Type.{u2}} [_inst_2 : SMul.{u1, u2} M β] {α : Type.{u3}} [_inst_5 : Monoid.{u1} M] [_inst_6 : AddMonoid.{u3} α] [_inst_7 : DistribMulAction.{u1, u3} M α _inst_5 _inst_6] (a : M) (c : β), Eq.{succ (max u3 u2)} (Prod.{u3, u2} α β) (SMul.smul.{u1, max u3 u2} M (Prod.{u3, u2} α β) (Prod.smul.{u1, u3, u2} M α β (SMulZeroClass.toHasSmul.{u1, u3} M α (AddZeroClass.toHasZero.{u3} α (AddMonoid.toAddZeroClass.{u3} α _inst_6)) (DistribSMul.toSmulZeroClass.{u1, u3} M α (AddMonoid.toAddZeroClass.{u3} α _inst_6) (DistribMulAction.toDistribSMul.{u1, u3} M α _inst_5 _inst_6 _inst_7))) _inst_2) a (Prod.mk.{u3, u2} α β (OfNat.ofNat.{u3} α 0 (OfNat.mk.{u3} α 0 (Zero.zero.{u3} α (AddZeroClass.toHasZero.{u3} α (AddMonoid.toAddZeroClass.{u3} α _inst_6))))) c)) (Prod.mk.{u3, u2} α β (OfNat.ofNat.{u3} α 0 (OfNat.mk.{u3} α 0 (Zero.zero.{u3} α (AddZeroClass.toHasZero.{u3} α (AddMonoid.toAddZeroClass.{u3} α _inst_6))))) (SMul.smul.{u1, u2} M β _inst_2 a c))
but is expected to have type
  forall {M : Type.{u2}} {β : Type.{u1}} [_inst_2 : SMul.{u2, u1} M β] {α : Type.{u3}} [_inst_5 : Monoid.{u2} M] [_inst_6 : AddMonoid.{u3} α] [_inst_7 : DistribMulAction.{u2, u3} M α _inst_5 _inst_6] (a : M) (c : β), Eq.{max (succ u1) (succ u3)} (Prod.{u3, u1} α β) (HSMul.hSMul.{u2, max u1 u3, max u1 u3} M (Prod.{u3, u1} α β) (Prod.{u3, u1} α β) (instHSMul.{u2, max u1 u3} M (Prod.{u3, u1} α β) (Prod.smul.{u2, u3, u1} M α β (SMulZeroClass.toSMul.{u2, u3} M α (AddMonoid.toZero.{u3} α _inst_6) (DistribSMul.toSMulZeroClass.{u2, u3} M α (AddMonoid.toAddZeroClass.{u3} α _inst_6) (DistribMulAction.toDistribSMul.{u2, u3} M α _inst_5 _inst_6 _inst_7))) _inst_2)) a (Prod.mk.{u3, u1} α β (OfNat.ofNat.{u3} α 0 (Zero.toOfNat0.{u3} α (AddMonoid.toZero.{u3} α _inst_6))) c)) (Prod.mk.{u3, u1} α β (OfNat.ofNat.{u3} α 0 (Zero.toOfNat0.{u3} α (AddMonoid.toZero.{u3} α _inst_6))) (HSMul.hSMul.{u2, u1, u1} M β β (instHSMul.{u2, u1} M β _inst_2) a c))
Case conversion may be inaccurate. Consider using '#align prod.smul_zero_mk Prod.smul_zero_mkₓ'. -/
theorem smul_zero_mk {α : Type _} [Monoid M] [AddMonoid α] [DistribMulAction M α] (a : M) (c : β) :
    a • ((0 : α), c) = (0, a • c) := by rw [Prod.smul_mk, smul_zero]
#align prod.smul_zero_mk Prod.smul_zero_mk

/- warning: prod.smul_mk_zero -> Prod.smul_mk_zero is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : SMul.{u1, u2} M α] {β : Type.{u3}} [_inst_5 : Monoid.{u1} M] [_inst_6 : AddMonoid.{u3} β] [_inst_7 : DistribMulAction.{u1, u3} M β _inst_5 _inst_6] (a : M) (b : α), Eq.{succ (max u2 u3)} (Prod.{u2, u3} α β) (SMul.smul.{u1, max u2 u3} M (Prod.{u2, u3} α β) (Prod.smul.{u1, u2, u3} M α β _inst_1 (SMulZeroClass.toHasSmul.{u1, u3} M β (AddZeroClass.toHasZero.{u3} β (AddMonoid.toAddZeroClass.{u3} β _inst_6)) (DistribSMul.toSmulZeroClass.{u1, u3} M β (AddMonoid.toAddZeroClass.{u3} β _inst_6) (DistribMulAction.toDistribSMul.{u1, u3} M β _inst_5 _inst_6 _inst_7)))) a (Prod.mk.{u2, u3} α β b (OfNat.ofNat.{u3} β 0 (OfNat.mk.{u3} β 0 (Zero.zero.{u3} β (AddZeroClass.toHasZero.{u3} β (AddMonoid.toAddZeroClass.{u3} β _inst_6))))))) (Prod.mk.{u2, u3} α β (SMul.smul.{u1, u2} M α _inst_1 a b) (OfNat.ofNat.{u3} β 0 (OfNat.mk.{u3} β 0 (Zero.zero.{u3} β (AddZeroClass.toHasZero.{u3} β (AddMonoid.toAddZeroClass.{u3} β _inst_6))))))
but is expected to have type
  forall {M : Type.{u2}} {α : Type.{u1}} [_inst_1 : SMul.{u2, u1} M α] {β : Type.{u3}} [_inst_5 : Monoid.{u2} M] [_inst_6 : AddMonoid.{u3} β] [_inst_7 : DistribMulAction.{u2, u3} M β _inst_5 _inst_6] (a : M) (b : α), Eq.{max (succ u1) (succ u3)} (Prod.{u1, u3} α β) (HSMul.hSMul.{u2, max u3 u1, max u1 u3} M (Prod.{u1, u3} α β) (Prod.{u1, u3} α β) (instHSMul.{u2, max u1 u3} M (Prod.{u1, u3} α β) (Prod.smul.{u2, u1, u3} M α β _inst_1 (SMulZeroClass.toSMul.{u2, u3} M β (AddMonoid.toZero.{u3} β _inst_6) (DistribSMul.toSMulZeroClass.{u2, u3} M β (AddMonoid.toAddZeroClass.{u3} β _inst_6) (DistribMulAction.toDistribSMul.{u2, u3} M β _inst_5 _inst_6 _inst_7))))) a (Prod.mk.{u1, u3} α β b (OfNat.ofNat.{u3} β 0 (Zero.toOfNat0.{u3} β (AddMonoid.toZero.{u3} β _inst_6))))) (Prod.mk.{u1, u3} α β (HSMul.hSMul.{u2, u1, u1} M α α (instHSMul.{u2, u1} M α _inst_1) a b) (OfNat.ofNat.{u3} β 0 (Zero.toOfNat0.{u3} β (AddMonoid.toZero.{u3} β _inst_6))))
Case conversion may be inaccurate. Consider using '#align prod.smul_mk_zero Prod.smul_mk_zeroₓ'. -/
theorem smul_mk_zero {β : Type _} [Monoid M] [AddMonoid β] [DistribMulAction M β] (a : M) (b : α) :
    a • (b, (0 : β)) = (a • b, 0) := by rw [Prod.smul_mk, smul_zero]
#align prod.smul_mk_zero Prod.smul_mk_zero

variable [Pow α E] [Pow β E]

#print Prod.pow /-
@[to_additive SMul]
instance pow : Pow (α × β) E where pow p c := (p.1 ^ c, p.2 ^ c)
#align prod.has_pow Prod.pow
#align prod.has_smul Prod.smul
-/

/- warning: prod.pow_fst -> Prod.pow_fst is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_5 : Pow.{u2, u1} α E] [_inst_6 : Pow.{u3, u1} β E] (p : Prod.{u2, u3} α β) (c : E), Eq.{succ u2} α (Prod.fst.{u2, u3} α β (HPow.hPow.{max u2 u3, u1, max u2 u3} (Prod.{u2, u3} α β) E (Prod.{u2, u3} α β) (instHPow.{max u2 u3, u1} (Prod.{u2, u3} α β) E (Prod.pow.{u1, u2, u3} E α β _inst_5 _inst_6)) p c)) (HPow.hPow.{u2, u1, u2} α E α (instHPow.{u2, u1} α E _inst_5) (Prod.fst.{u2, u3} α β p) c)
but is expected to have type
  forall {E : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_5 : Pow.{u3, u1} α E] [_inst_6 : Pow.{u2, u1} β E] (p : Prod.{u3, u2} α β) (c : E), Eq.{succ u3} α (Prod.fst.{u3, u2} α β (HPow.hPow.{max u3 u2, u1, max u3 u2} (Prod.{u3, u2} α β) E (Prod.{u3, u2} α β) (instHPow.{max u3 u2, u1} (Prod.{u3, u2} α β) E (Prod.pow.{u1, u3, u2} E α β _inst_5 _inst_6)) p c)) (HPow.hPow.{u3, u1, u3} α E α (instHPow.{u3, u1} α E _inst_5) (Prod.fst.{u3, u2} α β p) c)
Case conversion may be inaccurate. Consider using '#align prod.pow_fst Prod.pow_fstₓ'. -/
@[simp, to_additive smul_fst, to_additive_reorder 6]
theorem pow_fst (p : α × β) (c : E) : (p ^ c).fst = p.fst ^ c :=
  rfl
#align prod.pow_fst Prod.pow_fst
#align prod.smul_fst Prod.smul_fst

/- warning: prod.pow_snd -> Prod.pow_snd is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_5 : Pow.{u2, u1} α E] [_inst_6 : Pow.{u3, u1} β E] (p : Prod.{u2, u3} α β) (c : E), Eq.{succ u3} β (Prod.snd.{u2, u3} α β (HPow.hPow.{max u2 u3, u1, max u2 u3} (Prod.{u2, u3} α β) E (Prod.{u2, u3} α β) (instHPow.{max u2 u3, u1} (Prod.{u2, u3} α β) E (Prod.pow.{u1, u2, u3} E α β _inst_5 _inst_6)) p c)) (HPow.hPow.{u3, u1, u3} β E β (instHPow.{u3, u1} β E _inst_6) (Prod.snd.{u2, u3} α β p) c)
but is expected to have type
  forall {E : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_5 : Pow.{u3, u1} α E] [_inst_6 : Pow.{u2, u1} β E] (p : Prod.{u3, u2} α β) (c : E), Eq.{succ u2} β (Prod.snd.{u3, u2} α β (HPow.hPow.{max u3 u2, u1, max u3 u2} (Prod.{u3, u2} α β) E (Prod.{u3, u2} α β) (instHPow.{max u3 u2, u1} (Prod.{u3, u2} α β) E (Prod.pow.{u1, u3, u2} E α β _inst_5 _inst_6)) p c)) (HPow.hPow.{u2, u1, u2} β E β (instHPow.{u2, u1} β E _inst_6) (Prod.snd.{u3, u2} α β p) c)
Case conversion may be inaccurate. Consider using '#align prod.pow_snd Prod.pow_sndₓ'. -/
@[simp, to_additive smul_snd, to_additive_reorder 6]
theorem pow_snd (p : α × β) (c : E) : (p ^ c).snd = p.snd ^ c :=
  rfl
#align prod.pow_snd Prod.pow_snd
#align prod.smul_snd Prod.smul_snd

/- warning: prod.pow_mk -> Prod.pow_mk is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_5 : Pow.{u2, u1} α E] [_inst_6 : Pow.{u3, u1} β E] (c : E) (a : α) (b : β), Eq.{succ (max u2 u3)} (Prod.{u2, u3} α β) (HPow.hPow.{max u2 u3, u1, max u2 u3} (Prod.{u2, u3} α β) E (Prod.{u2, u3} α β) (instHPow.{max u2 u3, u1} (Prod.{u2, u3} α β) E (Prod.pow.{u1, u2, u3} E α β _inst_5 _inst_6)) (Prod.mk.{u2, u3} α β a b) c) (Prod.mk.{u2, u3} α β (HPow.hPow.{u2, u1, u2} α E α (instHPow.{u2, u1} α E _inst_5) a c) (HPow.hPow.{u3, u1, u3} β E β (instHPow.{u3, u1} β E _inst_6) b c))
but is expected to have type
  forall {E : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_5 : Pow.{u3, u1} α E] [_inst_6 : Pow.{u2, u1} β E] (c : E) (a : α) (b : β), Eq.{max (succ u3) (succ u2)} (Prod.{u3, u2} α β) (HPow.hPow.{max u3 u2, u1, max u3 u2} (Prod.{u3, u2} α β) E (Prod.{u3, u2} α β) (instHPow.{max u3 u2, u1} (Prod.{u3, u2} α β) E (Prod.pow.{u1, u3, u2} E α β _inst_5 _inst_6)) (Prod.mk.{u3, u2} α β a b) c) (Prod.mk.{u3, u2} α β (HPow.hPow.{u3, u1, u3} α E α (instHPow.{u3, u1} α E _inst_5) a c) (HPow.hPow.{u2, u1, u2} β E β (instHPow.{u2, u1} β E _inst_6) b c))
Case conversion may be inaccurate. Consider using '#align prod.pow_mk Prod.pow_mkₓ'. -/
/- Note that the `c` arguments to this lemmas cannot be in the more natural right-most positions due
to limitations in `to_additive` and `to_additive_reorder`, which will silently fail to reorder more
than two adjacent arguments -/
@[simp, to_additive smul_mk, to_additive_reorder 6]
theorem pow_mk (c : E) (a : α) (b : β) : Prod.mk a b ^ c = Prod.mk (a ^ c) (b ^ c) :=
  rfl
#align prod.pow_mk Prod.pow_mk
#align prod.smul_mk Prod.smul_mk

/- warning: prod.pow_def -> Prod.pow_def is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_5 : Pow.{u2, u1} α E] [_inst_6 : Pow.{u3, u1} β E] (p : Prod.{u2, u3} α β) (c : E), Eq.{succ (max u2 u3)} (Prod.{u2, u3} α β) (HPow.hPow.{max u2 u3, u1, max u2 u3} (Prod.{u2, u3} α β) E (Prod.{u2, u3} α β) (instHPow.{max u2 u3, u1} (Prod.{u2, u3} α β) E (Prod.pow.{u1, u2, u3} E α β _inst_5 _inst_6)) p c) (Prod.mk.{u2, u3} α β (HPow.hPow.{u2, u1, u2} α E α (instHPow.{u2, u1} α E _inst_5) (Prod.fst.{u2, u3} α β p) c) (HPow.hPow.{u3, u1, u3} β E β (instHPow.{u3, u1} β E _inst_6) (Prod.snd.{u2, u3} α β p) c))
but is expected to have type
  forall {E : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_5 : Pow.{u3, u1} α E] [_inst_6 : Pow.{u2, u1} β E] (p : Prod.{u3, u2} α β) (c : E), Eq.{max (succ u3) (succ u2)} (Prod.{u3, u2} α β) (HPow.hPow.{max u3 u2, u1, max u3 u2} (Prod.{u3, u2} α β) E (Prod.{u3, u2} α β) (instHPow.{max u3 u2, u1} (Prod.{u3, u2} α β) E (Prod.pow.{u1, u3, u2} E α β _inst_5 _inst_6)) p c) (Prod.mk.{u3, u2} α β (HPow.hPow.{u3, u1, u3} α E α (instHPow.{u3, u1} α E _inst_5) (Prod.fst.{u3, u2} α β p) c) (HPow.hPow.{u2, u1, u2} β E β (instHPow.{u2, u1} β E _inst_6) (Prod.snd.{u3, u2} α β p) c))
Case conversion may be inaccurate. Consider using '#align prod.pow_def Prod.pow_defₓ'. -/
@[to_additive smul_def, to_additive_reorder 6]
theorem pow_def (p : α × β) (c : E) : p ^ c = (p.1 ^ c, p.2 ^ c) :=
  rfl
#align prod.pow_def Prod.pow_def
#align prod.smul_def Prod.smul_def

/- warning: prod.pow_swap -> Prod.pow_swap is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_5 : Pow.{u2, u1} α E] [_inst_6 : Pow.{u3, u1} β E] (p : Prod.{u2, u3} α β) (c : E), Eq.{max (succ u3) (succ u2)} (Prod.{u3, u2} β α) (Prod.swap.{u2, u3} α β (HPow.hPow.{max u2 u3, u1, max u2 u3} (Prod.{u2, u3} α β) E (Prod.{u2, u3} α β) (instHPow.{max u2 u3, u1} (Prod.{u2, u3} α β) E (Prod.pow.{u1, u2, u3} E α β _inst_5 _inst_6)) p c)) (HPow.hPow.{max u3 u2, u1, max u3 u2} (Prod.{u3, u2} β α) E (Prod.{u3, u2} β α) (instHPow.{max u3 u2, u1} (Prod.{u3, u2} β α) E (Prod.pow.{u1, u3, u2} E β α _inst_6 _inst_5)) (Prod.swap.{u2, u3} α β p) c)
but is expected to have type
  forall {E : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_5 : Pow.{u3, u1} α E] [_inst_6 : Pow.{u2, u1} β E] (p : Prod.{u3, u2} α β) (c : E), Eq.{max (succ u3) (succ u2)} (Prod.{u2, u3} β α) (Prod.swap.{u3, u2} α β (HPow.hPow.{max u3 u2, u1, max u3 u2} (Prod.{u3, u2} α β) E (Prod.{u3, u2} α β) (instHPow.{max u3 u2, u1} (Prod.{u3, u2} α β) E (Prod.pow.{u1, u3, u2} E α β _inst_5 _inst_6)) p c)) (HPow.hPow.{max u3 u2, u1, max u3 u2} (Prod.{u2, u3} β α) E (Prod.{u2, u3} β α) (instHPow.{max u3 u2, u1} (Prod.{u2, u3} β α) E (Prod.pow.{u1, u2, u3} E β α _inst_6 _inst_5)) (Prod.swap.{u3, u2} α β p) c)
Case conversion may be inaccurate. Consider using '#align prod.pow_swap Prod.pow_swapₓ'. -/
@[simp, to_additive smul_swap, to_additive_reorder 6]
theorem pow_swap (p : α × β) (c : E) : (p ^ c).swap = p.swap ^ c :=
  rfl
#align prod.pow_swap Prod.pow_swap
#align prod.smul_swap Prod.smul_swap

@[to_additive]
instance [SMul M N] [IsScalarTower M N α] [IsScalarTower M N β] : IsScalarTower M N (α × β) :=
  ⟨fun x y z => mk.inj_iff.mpr ⟨smul_assoc _ _ _, smul_assoc _ _ _⟩⟩

@[to_additive]
instance [SMulCommClass M N α] [SMulCommClass M N β] : SMulCommClass M N (α × β)
    where smul_comm r s x := mk.inj_iff.mpr ⟨smul_comm _ _ _, smul_comm _ _ _⟩

@[to_additive]
instance [SMul Mᵐᵒᵖ α] [SMul Mᵐᵒᵖ β] [IsCentralScalar M α] [IsCentralScalar M β] :
    IsCentralScalar M (α × β) :=
  ⟨fun r m => Prod.ext (op_smul_eq_smul _ _) (op_smul_eq_smul _ _)⟩

#print Prod.faithfulSMulLeft /-
@[to_additive]
instance faithfulSMulLeft [FaithfulSMul M α] [Nonempty β] : FaithfulSMul M (α × β) :=
  ⟨fun x y h =>
    let ⟨b⟩ := ‹Nonempty β›
    eq_of_smul_eq_smul fun a : α => by injection h (a, b)⟩
#align prod.has_faithful_smul_left Prod.faithfulSMulLeft
#align prod.has_faithful_vadd_left Prod.faithfulVAddLeft
-/

#print Prod.faithfulSMulRight /-
@[to_additive]
instance faithfulSMulRight [Nonempty α] [FaithfulSMul M β] : FaithfulSMul M (α × β) :=
  ⟨fun x y h =>
    let ⟨a⟩ := ‹Nonempty α›
    eq_of_smul_eq_smul fun b : β => by injection h (a, b)⟩
#align prod.has_faithful_smul_right Prod.faithfulSMulRight
#align prod.has_faithful_vadd_right Prod.faithfulVAddRight
-/

end

#print Prod.smulCommClassBoth /-
@[to_additive]
instance smulCommClassBoth [Mul N] [Mul P] [SMul M N] [SMul M P] [SMulCommClass M N N]
    [SMulCommClass M P P] : SMulCommClass M (N × P) (N × P) :=
  ⟨fun c x y => by simp [smul_def, mul_def, mul_smul_comm]⟩
#align prod.smul_comm_class_both Prod.smulCommClassBoth
#align prod.vadd_comm_class_both Prod.vaddCommClassBoth
-/

#print Prod.isScalarTowerBoth /-
instance isScalarTowerBoth [Mul N] [Mul P] [SMul M N] [SMul M P] [IsScalarTower M N N]
    [IsScalarTower M P P] : IsScalarTower M (N × P) (N × P) :=
  ⟨fun c x y => by simp [smul_def, mul_def, smul_mul_assoc]⟩
#align prod.is_scalar_tower_both Prod.isScalarTowerBoth
-/

@[to_additive]
instance {m : Monoid M} [MulAction M α] [MulAction M β] : MulAction M (α × β)
    where
  mul_smul a₁ a₂ p := mk.inj_iff.mpr ⟨mul_smul _ _ _, mul_smul _ _ _⟩
  one_smul := fun ⟨b, c⟩ => mk.inj_iff.mpr ⟨one_smul _ _, one_smul _ _⟩

instance {R M N : Type _} [Zero M] [Zero N] [SMulZeroClass R M] [SMulZeroClass R N] :
    SMulZeroClass R (M × N) where smul_zero a := mk.inj_iff.mpr ⟨smul_zero _, smul_zero _⟩

instance {R M N : Type _} [AddZeroClass M] [AddZeroClass N] [DistribSMul R M] [DistribSMul R N] :
    DistribSMul R (M × N) where smul_add a p₁ p₂ := mk.inj_iff.mpr ⟨smul_add _ _ _, smul_add _ _ _⟩

instance {R M N : Type _} {r : Monoid R} [AddMonoid M] [AddMonoid N] [DistribMulAction R M]
    [DistribMulAction R N] : DistribMulAction R (M × N) :=
  { Prod.distribSmul with }

instance {R M N : Type _} {r : Monoid R} [Monoid M] [Monoid N] [MulDistribMulAction R M]
    [MulDistribMulAction R N] : MulDistribMulAction R (M × N)
    where
  smul_mul a p₁ p₂ := mk.inj_iff.mpr ⟨smul_mul' _ _ _, smul_mul' _ _ _⟩
  smul_one a := mk.inj_iff.mpr ⟨smul_one _, smul_one _⟩

end Prod

/-! ### Scalar multiplication as a homomorphism -/


section BundledSmul

/- warning: smul_mul_hom -> smulMulHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : Mul.{u2} β] [_inst_3 : MulAction.{u1, u2} α β _inst_1] [_inst_4 : IsScalarTower.{u1, u2, u2} α β β (MulAction.toHasSmul.{u1, u2} α β _inst_1 _inst_3) (Mul.toSMul.{u2} β _inst_2) (MulAction.toHasSmul.{u1, u2} α β _inst_1 _inst_3)] [_inst_5 : SMulCommClass.{u1, u2, u2} α β β (MulAction.toHasSmul.{u1, u2} α β _inst_1 _inst_3) (Mul.toSMul.{u2} β _inst_2)], MulHom.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Prod.hasMul.{u1, u2} α β (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2) _inst_2
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : Mul.{u2} β] [_inst_3 : MulAction.{u1, u2} α β _inst_1] [_inst_4 : IsScalarTower.{u1, u2, u2} α β β (MulAction.toSMul.{u1, u2} α β _inst_1 _inst_3) (Mul.toSMul.{u2} β _inst_2) (MulAction.toSMul.{u1, u2} α β _inst_1 _inst_3)] [_inst_5 : SMulCommClass.{u1, u2, u2} α β β (MulAction.toSMul.{u1, u2} α β _inst_1 _inst_3) (Mul.toSMul.{u2} β _inst_2)], MulHom.{max u2 u1, u2} (Prod.{u1, u2} α β) β (Prod.instMulProd.{u1, u2} α β (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2) _inst_2
Case conversion may be inaccurate. Consider using '#align smul_mul_hom smulMulHomₓ'. -/
/-- Scalar multiplication as a multiplicative homomorphism. -/
@[simps]
def smulMulHom [Monoid α] [Mul β] [MulAction α β] [IsScalarTower α β β] [SMulCommClass α β β] :
    α × β →ₙ* β where
  toFun a := a.1 • a.2
  map_mul' a b := (smul_mul_smul _ _ _ _).symm
#align smul_mul_hom smulMulHom

/- warning: smul_monoid_hom -> smulMonoidHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : MulOneClass.{u2} β] [_inst_3 : MulAction.{u1, u2} α β _inst_1] [_inst_4 : IsScalarTower.{u1, u2, u2} α β β (MulAction.toHasSmul.{u1, u2} α β _inst_1 _inst_3) (Mul.toSMul.{u2} β (MulOneClass.toHasMul.{u2} β _inst_2)) (MulAction.toHasSmul.{u1, u2} α β _inst_1 _inst_3)] [_inst_5 : SMulCommClass.{u1, u2, u2} α β β (MulAction.toHasSmul.{u1, u2} α β _inst_1 _inst_3) (Mul.toSMul.{u2} β (MulOneClass.toHasMul.{u2} β _inst_2))], MonoidHom.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Prod.mulOneClass.{u1, u2} α β (Monoid.toMulOneClass.{u1} α _inst_1) _inst_2) _inst_2
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : MulOneClass.{u2} β] [_inst_3 : MulAction.{u1, u2} α β _inst_1] [_inst_4 : IsScalarTower.{u1, u2, u2} α β β (MulAction.toSMul.{u1, u2} α β _inst_1 _inst_3) (Mul.toSMul.{u2} β (MulOneClass.toMul.{u2} β _inst_2)) (MulAction.toSMul.{u1, u2} α β _inst_1 _inst_3)] [_inst_5 : SMulCommClass.{u1, u2, u2} α β β (MulAction.toSMul.{u1, u2} α β _inst_1 _inst_3) (Mul.toSMul.{u2} β (MulOneClass.toMul.{u2} β _inst_2))], MonoidHom.{max u2 u1, u2} (Prod.{u1, u2} α β) β (Prod.instMulOneClassProd.{u1, u2} α β (Monoid.toMulOneClass.{u1} α _inst_1) _inst_2) _inst_2
Case conversion may be inaccurate. Consider using '#align smul_monoid_hom smulMonoidHomₓ'. -/
/-- Scalar multiplication as a monoid homomorphism. -/
@[simps]
def smulMonoidHom [Monoid α] [MulOneClass β] [MulAction α β] [IsScalarTower α β β]
    [SMulCommClass α β β] : α × β →* β :=
  { smulMulHom with map_one' := one_smul _ _ }
#align smul_monoid_hom smulMonoidHom

end BundledSmul

