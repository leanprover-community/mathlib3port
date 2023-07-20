/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Category.Module.Basic
import Mathbin.LinearAlgebra.Span

#align_import algebra.category.Module.tannaka from "leanprover-community/mathlib"@"9d2f0748e6c50d7a2657c564b1ff2c695b39148d"

/-!
# Tannaka duality for rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A ring `R` is equivalent to
the endomorphisms of the additive forgetful functor `Module R ⥤ AddCommGroup`.

-/


universe u

open CategoryTheory

#print ringEquivEndForget₂ /-
/-- An ingredient of Tannaka duality for rings:
A ring `R` is equivalent to
the endomorphisms of the additive forgetful functor `Module R ⥤ AddCommGroup`.
-/
def ringEquivEndForget₂ (R : Type u) [Ring R] :
    R ≃+* End (AdditiveFunctor.of (forget₂ (ModuleCat.{u} R) AddCommGroupCat.{u}))
    where
  toFun r :=
    { app := fun M => by apply DistribMulAction.toAddMonoidHom M r
      naturality' := fun M N f => by ext; exact (f.map_smul _ _).symm }
  invFun φ := φ.app (ModuleCat.of R R) (1 : R)
  left_inv := by intro r; simp
  right_inv := by
    intro φ; ext M x
    simp only [DistribMulAction.toAddMonoidHom_apply]
    have w :=
      AddMonoidHom.congr_fun (φ.naturality (ModuleCat.asHomRight (LinearMap.toSpanSingleton R M x)))
        (1 : R)
    convert w.symm
    exact (one_smul _ _).symm
  map_add' := by intros; ext; simp [add_smul]
  map_mul' := by intros; ext; simpa using mul_smul _ _ _
#align ring_equiv_End_forget₂ ringEquivEndForget₂
-/

