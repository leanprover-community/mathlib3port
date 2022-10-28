/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
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
instance hasSmulLeft [HasSmul R M] : HasSmul (ULift R) M :=
  ⟨fun s x => s.down • x⟩

@[simp, to_additive]
theorem smul_def [HasSmul R M] (s : ULift R) (x : M) : s • x = s.down • x :=
  rfl

instance is_scalar_tower [HasSmul R M] [HasSmul M N] [HasSmul R N] [IsScalarTower R M N] :
    IsScalarTower (ULift R) M N :=
  ⟨fun x y z => show (x.down • y) • z = x.down • y • z from smul_assoc _ _ _⟩

instance is_scalar_tower' [HasSmul R M] [HasSmul M N] [HasSmul R N] [IsScalarTower R M N] :
    IsScalarTower R (ULift M) N :=
  ⟨fun x y z => show (x • y.down) • z = x • y.down • z from smul_assoc _ _ _⟩

instance is_scalar_tower'' [HasSmul R M] [HasSmul M N] [HasSmul R N] [IsScalarTower R M N] :
    IsScalarTower R M (ULift N) :=
  ⟨fun x y z => show up ((x • y) • z.down) = ⟨x • y • z.down⟩ by rw [smul_assoc]⟩

instance [HasSmul R M] [HasSmul Rᵐᵒᵖ M] [IsCentralScalar R M] : IsCentralScalar R (ULift M) :=
  ⟨fun r m => congr_arg up <| op_smul_eq_smul r m.down⟩

@[to_additive]
instance mulAction [Monoid R] [MulAction R M] : MulAction (ULift R) M where
  smul := (· • ·)
  mul_smul _ _ := mul_smul _ _
  one_smul := one_smul _

@[to_additive]
instance mulAction' [Monoid R] [MulAction R M] : MulAction R (ULift M) where
  smul := (· • ·)
  mul_smul := fun r s ⟨f⟩ => ext _ _ <| mul_smul _ _ _
  one_smul := fun ⟨f⟩ => ext _ _ <| one_smul _ _

instance smulZeroClass [Zero M] [SmulZeroClass R M] : SmulZeroClass (ULift R) M :=
  { ULift.hasSmulLeft with smul_zero := fun _ => smul_zero _ }

instance smulZeroClass' [Zero M] [SmulZeroClass R M] :
    SmulZeroClass R (ULift M) where smul_zero c := by
    ext
    simp [smul_zero]

instance distribSmul [AddZeroClass M] [DistribSmul R M] : DistribSmul (ULift R) M where smul_add _ := smul_add _

instance distribSmul' [AddZeroClass M] [DistribSmul R M] :
    DistribSmul R (ULift M) where smul_add c f g := by
    ext
    simp [smul_add]

instance distribMulAction [Monoid R] [AddMonoid M] [DistribMulAction R M] : DistribMulAction (ULift R) M :=
  { ULift.mulAction, ULift.distribSmul with }

instance distribMulAction' [Monoid R] [AddMonoid M] [DistribMulAction R M] : DistribMulAction R (ULift M) :=
  { ULift.mulAction', ULift.distribSmul' with }

instance mulDistribMulAction [Monoid R] [Monoid M] [MulDistribMulAction R M] : MulDistribMulAction (ULift R) M where
  smul_one _ := smul_one _
  smul_mul _ := smul_mul' _

instance mulDistribMulAction' [Monoid R] [Monoid M] [MulDistribMulAction R M] : MulDistribMulAction R (ULift M) :=
  { ULift.mulAction' with
    smul_one := fun _ => by
      ext
      simp [smul_one],
    smul_mul := fun c f g => by
      ext
      simp [smul_mul'] }

instance smulWithZero [Zero R] [Zero M] [SmulWithZero R M] : SmulWithZero (ULift R) M :=
  { ULift.hasSmulLeft with smul_zero := fun _ => smul_zero _, zero_smul := zero_smul _ }

instance smulWithZero' [Zero R] [Zero M] [SmulWithZero R M] : SmulWithZero R (ULift M) where
  smul_zero _ := ULift.ext _ _ <| smul_zero _
  zero_smul _ := ULift.ext _ _ <| zero_smul _ _

instance mulActionWithZero [MonoidWithZero R] [Zero M] [MulActionWithZero R M] : MulActionWithZero (ULift R) M :=
  { ULift.smulWithZero with }

instance mulActionWithZero' [MonoidWithZero R] [Zero M] [MulActionWithZero R M] : MulActionWithZero R (ULift M) :=
  { ULift.smulWithZero' with }

instance module [Semiring R] [AddCommMonoid M] [Module R M] : Module (ULift R) M :=
  { ULift.smulWithZero with add_smul := fun _ _ => add_smul _ _ }

instance module' [Semiring R] [AddCommMonoid M] [Module R M] : Module R (ULift M) :=
  { ULift.smulWithZero' with add_smul := fun _ _ _ => ULift.ext _ _ <| add_smul _ _ _ }

/-- The `R`-linear equivalence between `ulift M` and `M`.
-/
def moduleEquiv [Semiring R] [AddCommMonoid M] [Module R M] : ULift M ≃ₗ[R] M where
  toFun := ULift.down
  invFun := ULift.up
  map_smul' r x := rfl
  map_add' x y := rfl
  left_inv := by tidy
  right_inv := by tidy

end ULift

