/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module algebra.module.hom
! leanprover-community/mathlib commit 7b78d1776212a91ecc94cf601f83bdcc46b04213
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Module.Pi

/-!
# Bundled hom instances for module and multiplicative actions

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
  mul_smul r s f := by simp [mul_smul]
  smul_add r f g := ext fun x => by simp [smul_add]
  smul_zero r := ext fun x => by simp [smul_zero]

@[simp]
theorem coe_smul (r : R) (f : A →+ B) : ⇑(r • f) = r • f :=
  rfl
#align add_monoid_hom.coe_smul AddMonoidHom.coe_smul

/- warning: add_monoid_hom.smul_apply -> AddMonoidHom.smul_apply is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : Monoid.{u1} R] [_inst_3 : AddMonoid.{u2} A] [_inst_4 : AddCommMonoid.{u3} B] [_inst_5 : DistribMulAction.{u1, u3} R B _inst_1 (AddCommMonoid.toAddMonoid.{u3} B _inst_4)] (r : R) (f : AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_3) (AddMonoid.toAddZeroClass.{u3} B (AddCommMonoid.toAddMonoid.{u3} B _inst_4))) (x : A), Eq.{succ u3} B (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_3) (AddMonoid.toAddZeroClass.{u3} B (AddCommMonoid.toAddMonoid.{u3} B _inst_4))) (fun (_x : AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_3) (AddMonoid.toAddZeroClass.{u3} B (AddCommMonoid.toAddMonoid.{u3} B _inst_4))) => A -> B) (AddMonoidHom.hasCoeToFun.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_3) (AddMonoid.toAddZeroClass.{u3} B (AddCommMonoid.toAddMonoid.{u3} B _inst_4))) (HasSmul.smul.{u1, max u3 u2} R (AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_3) (AddMonoid.toAddZeroClass.{u3} B (AddCommMonoid.toAddMonoid.{u3} B _inst_4))) (SMulZeroClass.toHasSmul.{u1, max u3 u2} R (AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_3) (AddMonoid.toAddZeroClass.{u3} B (AddCommMonoid.toAddMonoid.{u3} B _inst_4))) (AddZeroClass.toHasZero.{max u3 u2} (AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_3) (AddMonoid.toAddZeroClass.{u3} B (AddCommMonoid.toAddMonoid.{u3} B _inst_4))) (AddMonoid.toAddZeroClass.{max u3 u2} (AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_3) (AddMonoid.toAddZeroClass.{u3} B (AddCommMonoid.toAddMonoid.{u3} B _inst_4))) (AddCommMonoid.toAddMonoid.{max u3 u2} (AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_3) (AddMonoid.toAddZeroClass.{u3} B (AddCommMonoid.toAddMonoid.{u3} B _inst_4))) (AddMonoidHom.addCommMonoid.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_3) _inst_4)))) (DistribSMul.toSmulZeroClass.{u1, max u3 u2} R (AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_3) (AddMonoid.toAddZeroClass.{u3} B (AddCommMonoid.toAddMonoid.{u3} B _inst_4))) (AddMonoid.toAddZeroClass.{max u3 u2} (AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_3) (AddMonoid.toAddZeroClass.{u3} B (AddCommMonoid.toAddMonoid.{u3} B _inst_4))) (AddCommMonoid.toAddMonoid.{max u3 u2} (AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_3) (AddMonoid.toAddZeroClass.{u3} B (AddCommMonoid.toAddMonoid.{u3} B _inst_4))) (AddMonoidHom.addCommMonoid.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_3) _inst_4))) (DistribMulAction.toDistribSMul.{u1, max u3 u2} R (AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_3) (AddMonoid.toAddZeroClass.{u3} B (AddCommMonoid.toAddMonoid.{u3} B _inst_4))) _inst_1 (AddCommMonoid.toAddMonoid.{max u3 u2} (AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_3) (AddMonoid.toAddZeroClass.{u3} B (AddCommMonoid.toAddMonoid.{u3} B _inst_4))) (AddMonoidHom.addCommMonoid.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_3) _inst_4)) (AddMonoidHom.distribMulAction.{u1, u2, u3} R A B _inst_1 _inst_3 _inst_4 _inst_5)))) r f) x) (HasSmul.smul.{u1, u3} R B (SMulZeroClass.toHasSmul.{u1, u3} R B (AddZeroClass.toHasZero.{u3} B (AddMonoid.toAddZeroClass.{u3} B (AddCommMonoid.toAddMonoid.{u3} B _inst_4))) (DistribSMul.toSmulZeroClass.{u1, u3} R B (AddMonoid.toAddZeroClass.{u3} B (AddCommMonoid.toAddMonoid.{u3} B _inst_4)) (DistribMulAction.toDistribSMul.{u1, u3} R B _inst_1 (AddCommMonoid.toAddMonoid.{u3} B _inst_4) _inst_5))) r (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_3) (AddMonoid.toAddZeroClass.{u3} B (AddCommMonoid.toAddMonoid.{u3} B _inst_4))) (fun (_x : AddMonoidHom.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_3) (AddMonoid.toAddZeroClass.{u3} B (AddCommMonoid.toAddMonoid.{u3} B _inst_4))) => A -> B) (AddMonoidHom.hasCoeToFun.{u2, u3} A B (AddMonoid.toAddZeroClass.{u2} A _inst_3) (AddMonoid.toAddZeroClass.{u3} B (AddCommMonoid.toAddMonoid.{u3} B _inst_4))) f x))
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u3}} {B : Type.{u2}} [_inst_1 : Monoid.{u1} R] [_inst_3 : AddMonoid.{u3} A] [_inst_4 : AddCommMonoid.{u2} B] [_inst_5 : DistribMulAction.{u1, u2} R B _inst_1 (AddCommMonoid.toAddMonoid.{u2} B _inst_4)] (r : R) (f : AddMonoidHom.{u3, u2} A B (AddMonoid.toAddZeroClass.{u3} A _inst_3) (AddMonoid.toAddZeroClass.{u2} B (AddCommMonoid.toAddMonoid.{u2} B _inst_4))) (x : A), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => B) x) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (AddMonoidHom.{u3, u2} A B (AddMonoid.toAddZeroClass.{u3} A _inst_3) (AddMonoid.toAddZeroClass.{u2} B (AddCommMonoid.toAddMonoid.{u2} B _inst_4))) A (fun (_x : A) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => B) _x) (AddHomClass.toFunLike.{max u3 u2, u3, u2} (AddMonoidHom.{u3, u2} A B (AddMonoid.toAddZeroClass.{u3} A _inst_3) (AddMonoid.toAddZeroClass.{u2} B (AddCommMonoid.toAddMonoid.{u2} B _inst_4))) A B (AddZeroClass.toAdd.{u3} A (AddMonoid.toAddZeroClass.{u3} A _inst_3)) (AddZeroClass.toAdd.{u2} B (AddMonoid.toAddZeroClass.{u2} B (AddCommMonoid.toAddMonoid.{u2} B _inst_4))) (AddMonoidHomClass.toAddHomClass.{max u3 u2, u3, u2} (AddMonoidHom.{u3, u2} A B (AddMonoid.toAddZeroClass.{u3} A _inst_3) (AddMonoid.toAddZeroClass.{u2} B (AddCommMonoid.toAddMonoid.{u2} B _inst_4))) A B (AddMonoid.toAddZeroClass.{u3} A _inst_3) (AddMonoid.toAddZeroClass.{u2} B (AddCommMonoid.toAddMonoid.{u2} B _inst_4)) (AddMonoidHom.addMonoidHomClass.{u3, u2} A B (AddMonoid.toAddZeroClass.{u3} A _inst_3) (AddMonoid.toAddZeroClass.{u2} B (AddCommMonoid.toAddMonoid.{u2} B _inst_4))))) (HSMul.hSMul.{u1, max u3 u2, max u3 u2} R (AddMonoidHom.{u3, u2} A B (AddMonoid.toAddZeroClass.{u3} A _inst_3) (AddMonoid.toAddZeroClass.{u2} B (AddCommMonoid.toAddMonoid.{u2} B _inst_4))) (AddMonoidHom.{u3, u2} A B (AddMonoid.toAddZeroClass.{u3} A _inst_3) (AddMonoid.toAddZeroClass.{u2} B (AddCommMonoid.toAddMonoid.{u2} B _inst_4))) (instHSMul.{u1, max u3 u2} R (AddMonoidHom.{u3, u2} A B (AddMonoid.toAddZeroClass.{u3} A _inst_3) (AddMonoid.toAddZeroClass.{u2} B (AddCommMonoid.toAddMonoid.{u2} B _inst_4))) (SMulZeroClass.toSMul.{u1, max u3 u2} R (AddMonoidHom.{u3, u2} A B (AddMonoid.toAddZeroClass.{u3} A _inst_3) (AddMonoid.toAddZeroClass.{u2} B (AddCommMonoid.toAddMonoid.{u2} B _inst_4))) (instZeroAddMonoidHom.{u3, u2} A B (AddMonoid.toAddZeroClass.{u3} A _inst_3) (AddMonoid.toAddZeroClass.{u2} B (AddCommMonoid.toAddMonoid.{u2} B _inst_4))) (DistribSMul.toSMulZeroClass.{u1, max u3 u2} R (AddMonoidHom.{u3, u2} A B (AddMonoid.toAddZeroClass.{u3} A _inst_3) (AddMonoid.toAddZeroClass.{u2} B (AddCommMonoid.toAddMonoid.{u2} B _inst_4))) (AddMonoid.toAddZeroClass.{max u3 u2} (AddMonoidHom.{u3, u2} A B (AddMonoid.toAddZeroClass.{u3} A _inst_3) (AddMonoid.toAddZeroClass.{u2} B (AddCommMonoid.toAddMonoid.{u2} B _inst_4))) (AddCommMonoid.toAddMonoid.{max u3 u2} (AddMonoidHom.{u3, u2} A B (AddMonoid.toAddZeroClass.{u3} A _inst_3) (AddMonoid.toAddZeroClass.{u2} B (AddCommMonoid.toAddMonoid.{u2} B _inst_4))) (AddMonoidHom.addCommMonoid.{u3, u2} A B (AddMonoid.toAddZeroClass.{u3} A _inst_3) _inst_4))) (DistribMulAction.toDistribSMul.{u1, max u3 u2} R (AddMonoidHom.{u3, u2} A B (AddMonoid.toAddZeroClass.{u3} A _inst_3) (AddMonoid.toAddZeroClass.{u2} B (AddCommMonoid.toAddMonoid.{u2} B _inst_4))) _inst_1 (AddCommMonoid.toAddMonoid.{max u3 u2} (AddMonoidHom.{u3, u2} A B (AddMonoid.toAddZeroClass.{u3} A _inst_3) (AddMonoid.toAddZeroClass.{u2} B (AddCommMonoid.toAddMonoid.{u2} B _inst_4))) (AddMonoidHom.addCommMonoid.{u3, u2} A B (AddMonoid.toAddZeroClass.{u3} A _inst_3) _inst_4)) (AddMonoidHom.distribMulAction.{u1, u3, u2} R A B _inst_1 _inst_3 _inst_4 _inst_5))))) r f) x) (HSMul.hSMul.{u1, u2, u2} R ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => B) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => B) x) (instHSMul.{u1, u2} R ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => B) x) (SMulZeroClass.toSMul.{u1, u2} R ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => B) x) (AddMonoid.toZero.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => B) x) (AddCommMonoid.toAddMonoid.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => B) x) _inst_4)) (DistribSMul.toSMulZeroClass.{u1, u2} R ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => B) x) (AddMonoid.toAddZeroClass.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => B) x) (AddCommMonoid.toAddMonoid.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => B) x) _inst_4)) (DistribMulAction.toDistribSMul.{u1, u2} R ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => B) x) _inst_1 (AddCommMonoid.toAddMonoid.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => B) x) _inst_4) _inst_5)))) r (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (AddMonoidHom.{u3, u2} A B (AddMonoid.toAddZeroClass.{u3} A _inst_3) (AddMonoid.toAddZeroClass.{u2} B (AddCommMonoid.toAddMonoid.{u2} B _inst_4))) A (fun (_x : A) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => B) _x) (AddHomClass.toFunLike.{max u3 u2, u3, u2} (AddMonoidHom.{u3, u2} A B (AddMonoid.toAddZeroClass.{u3} A _inst_3) (AddMonoid.toAddZeroClass.{u2} B (AddCommMonoid.toAddMonoid.{u2} B _inst_4))) A B (AddZeroClass.toAdd.{u3} A (AddMonoid.toAddZeroClass.{u3} A _inst_3)) (AddZeroClass.toAdd.{u2} B (AddMonoid.toAddZeroClass.{u2} B (AddCommMonoid.toAddMonoid.{u2} B _inst_4))) (AddMonoidHomClass.toAddHomClass.{max u3 u2, u3, u2} (AddMonoidHom.{u3, u2} A B (AddMonoid.toAddZeroClass.{u3} A _inst_3) (AddMonoid.toAddZeroClass.{u2} B (AddCommMonoid.toAddMonoid.{u2} B _inst_4))) A B (AddMonoid.toAddZeroClass.{u3} A _inst_3) (AddMonoid.toAddZeroClass.{u2} B (AddCommMonoid.toAddMonoid.{u2} B _inst_4)) (AddMonoidHom.addMonoidHomClass.{u3, u2} A B (AddMonoid.toAddZeroClass.{u3} A _inst_3) (AddMonoid.toAddZeroClass.{u2} B (AddCommMonoid.toAddMonoid.{u2} B _inst_4))))) f x))
Case conversion may be inaccurate. Consider using '#align add_monoid_hom.smul_apply AddMonoidHom.smul_applyₓ'. -/
theorem smul_apply (r : R) (f : A →+ B) (x : A) : (r • f) x = r • f x :=
  rfl
#align add_monoid_hom.smul_apply AddMonoidHom.smul_apply

instance [SMulCommClass R S B] : SMulCommClass R S (A →+ B) :=
  ⟨fun a b f => ext fun x => smul_comm _ _ _⟩

instance [HasSmul R S] [IsScalarTower R S B] : IsScalarTower R S (A →+ B) :=
  ⟨fun a b f => ext fun x => smul_assoc _ _ _⟩

instance [DistribMulAction Rᵐᵒᵖ B] [IsCentralScalar R B] : IsCentralScalar R (A →+ B) :=
  ⟨fun a b => ext fun x => op_smul_eq_smul _ _⟩

end

instance [Semiring R] [AddMonoid A] [AddCommMonoid B] [Module R B] : Module R (A →+ B) :=
  {
    AddMonoidHom.distribMulAction with
    add_smul := fun r s x => ext fun y => by simp [add_smul]
    zero_smul := fun x => ext fun y => by simp [zero_smul] }

end AddMonoidHom

