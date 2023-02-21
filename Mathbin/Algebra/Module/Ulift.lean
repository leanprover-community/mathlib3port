/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.module.ulift
! leanprover-community/mathlib commit 68d1483e8a718ec63219f0e227ca3f0140361086
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Ring.Ulift
import Mathbin.Algebra.Module.Equiv

/-!
# `ulift` instances for module and multiplicative actions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines instances for module, mul_action and related structures on `ulift` types.

(Recall `ulift α` is just a "copy" of a type `α` in a higher universe.)

We also provide `ulift.module_equiv : ulift M ≃ₗ[R] M`.

-/


namespace ULift

universe u v w

variable {R : Type u}

variable {M : Type v}

variable {N : Type w}

#print ULift.smulLeft /-
@[to_additive]
instance smulLeft [SMul R M] : SMul (ULift R) M :=
  ⟨fun s x => s.down • x⟩
#align ulift.has_smul_left ULift.smulLeft
#align ulift.has_vadd_left ULift.vaddLeft
-/

/- warning: ulift.smul_def -> ULift.smul_def is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : SMul.{u1, u2} R M] (s : ULift.{u3, u1} R) (x : M), Eq.{succ u2} M (SMul.smul.{max u1 u3, u2} (ULift.{u3, u1} R) M (ULift.smulLeft.{u1, u2, u3} R M _inst_1) s x) (SMul.smul.{u1, u2} R M _inst_1 (ULift.down.{u3, u1} R s) x)
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : SMul.{u2, u3} R M] (s : ULift.{u1, u2} R) (x : M), Eq.{succ u3} M (HSMul.hSMul.{max u2 u1, u3, u3} (ULift.{u1, u2} R) M M (instHSMul.{max u2 u1, u3} (ULift.{u1, u2} R) M (ULift.smulLeft.{u2, u3, u1} R M _inst_1)) s x) (HSMul.hSMul.{u2, u3, u3} R M M (instHSMul.{u2, u3} R M _inst_1) (ULift.down.{u1, u2} R s) x)
Case conversion may be inaccurate. Consider using '#align ulift.smul_def ULift.smul_defₓ'. -/
@[simp, to_additive]
theorem smul_def [SMul R M] (s : ULift R) (x : M) : s • x = s.down • x :=
  rfl
#align ulift.smul_def ULift.smul_def
#align ulift.vadd_def ULift.vadd_def

#print ULift.isScalarTower /-
instance isScalarTower [SMul R M] [SMul M N] [SMul R N] [IsScalarTower R M N] :
    IsScalarTower (ULift R) M N :=
  ⟨fun x y z => show (x.down • y) • z = x.down • y • z from smul_assoc _ _ _⟩
#align ulift.is_scalar_tower ULift.isScalarTower
-/

#print ULift.isScalarTower' /-
instance isScalarTower' [SMul R M] [SMul M N] [SMul R N] [IsScalarTower R M N] :
    IsScalarTower R (ULift M) N :=
  ⟨fun x y z => show (x • y.down) • z = x • y.down • z from smul_assoc _ _ _⟩
#align ulift.is_scalar_tower' ULift.isScalarTower'
-/

#print ULift.isScalarTower'' /-
instance isScalarTower'' [SMul R M] [SMul M N] [SMul R N] [IsScalarTower R M N] :
    IsScalarTower R M (ULift N) :=
  ⟨fun x y z => show up ((x • y) • z.down) = ⟨x • y • z.down⟩ by rw [smul_assoc]⟩
#align ulift.is_scalar_tower'' ULift.isScalarTower''
-/

instance [SMul R M] [SMul Rᵐᵒᵖ M] [IsCentralScalar R M] : IsCentralScalar R (ULift M) :=
  ⟨fun r m => congr_arg up <| op_smul_eq_smul r m.down⟩

#print ULift.mulAction /-
@[to_additive]
instance mulAction [Monoid R] [MulAction R M] : MulAction (ULift R) M
    where
  smul := (· • ·)
  mul_smul _ _ := mul_smul _ _
  one_smul := one_smul _
#align ulift.mul_action ULift.mulAction
#align ulift.add_action ULift.addAction
-/

#print ULift.mulAction' /-
@[to_additive]
instance mulAction' [Monoid R] [MulAction R M] : MulAction R (ULift M)
    where
  smul := (· • ·)
  mul_smul := fun r s ⟨f⟩ => ext _ _ <| mul_smul _ _ _
  one_smul := fun ⟨f⟩ => ext _ _ <| one_smul _ _
#align ulift.mul_action' ULift.mulAction'
#align ulift.add_action' ULift.addAction'
-/

#print ULift.smulZeroClass /-
instance smulZeroClass [Zero M] [SMulZeroClass R M] : SMulZeroClass (ULift R) M :=
  { ULift.smulLeft with smul_zero := fun _ => smul_zero _ }
#align ulift.smul_zero_class ULift.smulZeroClass
-/

#print ULift.smulZeroClass' /-
instance smulZeroClass' [Zero M] [SMulZeroClass R M] : SMulZeroClass R (ULift M)
    where smul_zero c := by
    ext
    simp [smul_zero]
#align ulift.smul_zero_class' ULift.smulZeroClass'
-/

#print ULift.distribSmul /-
instance distribSmul [AddZeroClass M] [DistribSMul R M] : DistribSMul (ULift R) M
    where smul_add _ := smul_add _
#align ulift.distrib_smul ULift.distribSmul
-/

#print ULift.distribSmul' /-
instance distribSmul' [AddZeroClass M] [DistribSMul R M] : DistribSMul R (ULift M)
    where smul_add c f g := by
    ext
    simp [smul_add]
#align ulift.distrib_smul' ULift.distribSmul'
-/

#print ULift.distribMulAction /-
instance distribMulAction [Monoid R] [AddMonoid M] [DistribMulAction R M] :
    DistribMulAction (ULift R) M :=
  { ULift.mulAction, ULift.distribSmul with }
#align ulift.distrib_mul_action ULift.distribMulAction
-/

#print ULift.distribMulAction' /-
instance distribMulAction' [Monoid R] [AddMonoid M] [DistribMulAction R M] :
    DistribMulAction R (ULift M) :=
  { ULift.mulAction', ULift.distribSmul' with }
#align ulift.distrib_mul_action' ULift.distribMulAction'
-/

#print ULift.mulDistribMulAction /-
instance mulDistribMulAction [Monoid R] [Monoid M] [MulDistribMulAction R M] :
    MulDistribMulAction (ULift R) M
    where
  smul_one _ := smul_one _
  smul_mul _ := smul_mul' _
#align ulift.mul_distrib_mul_action ULift.mulDistribMulAction
-/

#print ULift.mulDistribMulAction' /-
instance mulDistribMulAction' [Monoid R] [Monoid M] [MulDistribMulAction R M] :
    MulDistribMulAction R (ULift M) :=
  {
    ULift.mulAction' with
    smul_one := fun _ => by
      ext
      simp [smul_one]
    smul_mul := fun c f g => by
      ext
      simp [smul_mul'] }
#align ulift.mul_distrib_mul_action' ULift.mulDistribMulAction'
-/

#print ULift.smulWithZero /-
instance smulWithZero [Zero R] [Zero M] [SMulWithZero R M] : SMulWithZero (ULift R) M :=
  { ULift.smulLeft with
    smul_zero := fun _ => smul_zero _
    zero_smul := zero_smul _ }
#align ulift.smul_with_zero ULift.smulWithZero
-/

#print ULift.smulWithZero' /-
instance smulWithZero' [Zero R] [Zero M] [SMulWithZero R M] : SMulWithZero R (ULift M)
    where
  smul_zero _ := ULift.ext _ _ <| smul_zero _
  zero_smul _ := ULift.ext _ _ <| zero_smul _ _
#align ulift.smul_with_zero' ULift.smulWithZero'
-/

#print ULift.mulActionWithZero /-
instance mulActionWithZero [MonoidWithZero R] [Zero M] [MulActionWithZero R M] :
    MulActionWithZero (ULift R) M :=
  { ULift.smulWithZero with }
#align ulift.mul_action_with_zero ULift.mulActionWithZero
-/

#print ULift.mulActionWithZero' /-
instance mulActionWithZero' [MonoidWithZero R] [Zero M] [MulActionWithZero R M] :
    MulActionWithZero R (ULift M) :=
  { ULift.smulWithZero' with }
#align ulift.mul_action_with_zero' ULift.mulActionWithZero'
-/

#print ULift.module /-
instance module [Semiring R] [AddCommMonoid M] [Module R M] : Module (ULift R) M :=
  { ULift.smulWithZero with add_smul := fun _ _ => add_smul _ _ }
#align ulift.module ULift.module
-/

#print ULift.module' /-
instance module' [Semiring R] [AddCommMonoid M] [Module R M] : Module R (ULift M) :=
  { ULift.smulWithZero' with add_smul := fun _ _ _ => ULift.ext _ _ <| add_smul _ _ _ }
#align ulift.module' ULift.module'
-/

#print ULift.moduleEquiv /-
/-- The `R`-linear equivalence between `ulift M` and `M`.
-/
@[simps apply symm_apply]
def moduleEquiv [Semiring R] [AddCommMonoid M] [Module R M] : ULift M ≃ₗ[R] M
    where
  toFun := ULift.down
  invFun := ULift.up
  map_smul' r x := rfl
  map_add' x y := rfl
  left_inv := by tidy
  right_inv := by tidy
#align ulift.module_equiv ULift.moduleEquiv
-/

end ULift

