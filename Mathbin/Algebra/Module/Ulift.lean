/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.module.ulift
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Ring.Ulift
import Mathbin.Algebra.Module.Equiv

/-!
# `ulift` instances for module and multiplicative actions

This file defines instances for module, mul_action and related structures on `ulift` types.

(Recall `ulift α` is just a "copy" of a type `α` in a higher universe.)

We also provide `ulift.module_equiv : ulift M ≃ₗ[R] M`.

-/


namespace ULift

universe u v w

variable {R : Type u}

variable {M : Type v}

variable {N : Type w}

@[to_additive]
instance hasSmulLeft [SMul R M] : SMul (ULift R) M :=
  ⟨fun s x => s.down • x⟩
#align ulift.has_smul_left ULift.hasSmulLeft

@[simp, to_additive]
theorem smul_def [SMul R M] (s : ULift R) (x : M) : s • x = s.down • x :=
  rfl
#align ulift.smul_def ULift.smul_def

instance is_scalar_tower [SMul R M] [SMul M N] [SMul R N] [IsScalarTower R M N] :
    IsScalarTower (ULift R) M N :=
  ⟨fun x y z => show (x.down • y) • z = x.down • y • z from smul_assoc _ _ _⟩
#align ulift.is_scalar_tower ULift.is_scalar_tower

instance is_scalar_tower' [SMul R M] [SMul M N] [SMul R N] [IsScalarTower R M N] :
    IsScalarTower R (ULift M) N :=
  ⟨fun x y z => show (x • y.down) • z = x • y.down • z from smul_assoc _ _ _⟩
#align ulift.is_scalar_tower' ULift.is_scalar_tower'

instance is_scalar_tower'' [SMul R M] [SMul M N] [SMul R N] [IsScalarTower R M N] :
    IsScalarTower R M (ULift N) :=
  ⟨fun x y z => show up ((x • y) • z.down) = ⟨x • y • z.down⟩ by rw [smul_assoc]⟩
#align ulift.is_scalar_tower'' ULift.is_scalar_tower''

instance [SMul R M] [SMul Rᵐᵒᵖ M] [IsCentralScalar R M] : IsCentralScalar R (ULift M) :=
  ⟨fun r m => congr_arg up <| op_smul_eq_smul r m.down⟩

@[to_additive]
instance mulAction [Monoid R] [MulAction R M] : MulAction (ULift R) M
    where
  smul := (· • ·)
  mul_smul _ _ := mul_smul _ _
  one_smul := one_smul _
#align ulift.mul_action ULift.mulAction

@[to_additive]
instance mulAction' [Monoid R] [MulAction R M] : MulAction R (ULift M)
    where
  smul := (· • ·)
  mul_smul := fun r s ⟨f⟩ => ext _ _ <| mul_smul _ _ _
  one_smul := fun ⟨f⟩ => ext _ _ <| one_smul _ _
#align ulift.mul_action' ULift.mulAction'

instance smulZeroClass [Zero M] [SMulZeroClass R M] : SMulZeroClass (ULift R) M :=
  { ULift.hasSmulLeft with smul_zero := fun _ => smul_zero _ }
#align ulift.smul_zero_class ULift.smulZeroClass

instance smulZeroClass' [Zero M] [SMulZeroClass R M] : SMulZeroClass R (ULift M)
    where smul_zero c := by
    ext
    simp [smul_zero]
#align ulift.smul_zero_class' ULift.smulZeroClass'

instance distribSmul [AddZeroClass M] [DistribSMul R M] : DistribSMul (ULift R) M
    where smul_add _ := smul_add _
#align ulift.distrib_smul ULift.distribSmul

instance distribSmul' [AddZeroClass M] [DistribSMul R M] : DistribSMul R (ULift M)
    where smul_add c f g := by
    ext
    simp [smul_add]
#align ulift.distrib_smul' ULift.distribSmul'

instance distribMulAction [Monoid R] [AddMonoid M] [DistribMulAction R M] :
    DistribMulAction (ULift R) M :=
  { ULift.mulAction, ULift.distribSmul with }
#align ulift.distrib_mul_action ULift.distribMulAction

instance distribMulAction' [Monoid R] [AddMonoid M] [DistribMulAction R M] :
    DistribMulAction R (ULift M) :=
  { ULift.mulAction', ULift.distribSmul' with }
#align ulift.distrib_mul_action' ULift.distribMulAction'

instance mulDistribMulAction [Monoid R] [Monoid M] [MulDistribMulAction R M] :
    MulDistribMulAction (ULift R) M
    where
  smul_one _ := smul_one _
  smul_mul _ := smul_mul' _
#align ulift.mul_distrib_mul_action ULift.mulDistribMulAction

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

instance smulWithZero [Zero R] [Zero M] [SMulWithZero R M] : SMulWithZero (ULift R) M :=
  { ULift.hasSmulLeft with
    smul_zero := fun _ => smul_zero _
    zero_smul := zero_smul _ }
#align ulift.smul_with_zero ULift.smulWithZero

instance smulWithZero' [Zero R] [Zero M] [SMulWithZero R M] : SMulWithZero R (ULift M)
    where
  smul_zero _ := ULift.ext _ _ <| smul_zero _
  zero_smul _ := ULift.ext _ _ <| zero_smul _ _
#align ulift.smul_with_zero' ULift.smulWithZero'

instance mulActionWithZero [MonoidWithZero R] [Zero M] [MulActionWithZero R M] :
    MulActionWithZero (ULift R) M :=
  { ULift.smulWithZero with }
#align ulift.mul_action_with_zero ULift.mulActionWithZero

instance mulActionWithZero' [MonoidWithZero R] [Zero M] [MulActionWithZero R M] :
    MulActionWithZero R (ULift M) :=
  { ULift.smulWithZero' with }
#align ulift.mul_action_with_zero' ULift.mulActionWithZero'

instance module [Semiring R] [AddCommMonoid M] [Module R M] : Module (ULift R) M :=
  { ULift.smulWithZero with add_smul := fun _ _ => add_smul _ _ }
#align ulift.module ULift.module

instance module' [Semiring R] [AddCommMonoid M] [Module R M] : Module R (ULift M) :=
  { ULift.smulWithZero' with add_smul := fun _ _ _ => ULift.ext _ _ <| add_smul _ _ _ }
#align ulift.module' ULift.module'

/-- The `R`-linear equivalence between `ulift M` and `M`.
-/
def moduleEquiv [Semiring R] [AddCommMonoid M] [Module R M] : ULift M ≃ₗ[R] M
    where
  toFun := ULift.down
  invFun := ULift.up
  map_smul' r x := rfl
  map_add' x y := rfl
  left_inv := by tidy
  right_inv := by tidy
#align ulift.module_equiv ULift.moduleEquiv

end ULift

