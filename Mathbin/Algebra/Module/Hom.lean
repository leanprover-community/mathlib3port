/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Algebra.Module.Pi

#align_import algebra.module.hom from "leanprover-community/mathlib"@"be24ec5de6701447e5df5ca75400ffee19d65659"

/-!
# Bundled hom instances for module and multiplicative actions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines instances for module, mul_action and related structures on bundled `_hom` types.

These are analogous to the instances in `algebra.module.pi`, but for bundled instead of unbundled
functions.
-/


variable {R S A B : Type _}

namespace AddMonoidHom

section

variable [Monoid R] [Monoid S] [AddMonoid A] [AddCommMonoid B]

variable [DistribMulAction R B] [DistribMulAction S B]

instance : DistribMulAction R (A →+ B)
    where
  smul r f :=
    { toFun := r • f
      map_zero' := by simp
      map_add' := fun x y => by simp [smul_add] }
  one_smul f := by simp
  hMul_smul r s f := by simp [mul_smul]
  smul_add r f g := ext fun x => by simp [smul_add]
  smul_zero r := ext fun x => by simp [smul_zero]

#print AddMonoidHom.coe_smul /-
@[simp]
theorem coe_smul (r : R) (f : A →+ B) : ⇑(r • f) = r • f :=
  rfl
#align add_monoid_hom.coe_smul AddMonoidHom.coe_smul
-/

#print AddMonoidHom.smul_apply /-
theorem smul_apply (r : R) (f : A →+ B) (x : A) : (r • f) x = r • f x :=
  rfl
#align add_monoid_hom.smul_apply AddMonoidHom.smul_apply
-/

instance [SMulCommClass R S B] : SMulCommClass R S (A →+ B) :=
  ⟨fun a b f => ext fun x => smul_comm _ _ _⟩

instance [SMul R S] [IsScalarTower R S B] : IsScalarTower R S (A →+ B) :=
  ⟨fun a b f => ext fun x => smul_assoc _ _ _⟩

instance [DistribMulAction Rᵐᵒᵖ B] [IsCentralScalar R B] : IsCentralScalar R (A →+ B) :=
  ⟨fun a b => ext fun x => op_smul_eq_smul _ _⟩

end

instance [Semiring R] [AddMonoid A] [AddCommMonoid B] [Module R B] : Module R (A →+ B) :=
  {
    AddMonoidHom.instDistribMulAction with
    add_smul := fun r s x => ext fun y => by simp [add_smul]
    zero_smul := fun x => ext fun y => by simp [zero_smul] }

end AddMonoidHom

