/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.category.Module.tannaka
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.ModuleCat.Basic

/-!
# Tannaka duality for rings

A ring `R` is equivalent to
the endomorphisms of the additive forgetful functor `Module R ⥤ AddCommGroup`.

-/


universe u

open CategoryTheory

/-- An ingredient of Tannaka duality for rings:
A ring `R` is equivalent to
the endomorphisms of the additive forgetful functor `Module R ⥤ AddCommGroup`.
-/
def ringEquivEndForget₂ (R : Type u) [Ring R] :
    R ≃+* EndCat (AdditiveFunctorCat.of (forget₂ (ModuleCat.{u} R) AddCommGroupCat.{u}))
    where
  toFun r :=
    { app := fun M => by apply DistribMulAction.toAddMonoidHom M r
      naturality' := fun M N f => by
        ext
        exact (f.map_smul _ _).symm }
  invFun φ := φ.app (ModuleCat.of R R) (1 : R)
  left_inv := by
    intro r
    simp
  right_inv := by
    intro φ; ext (M x)
    simp only [DistribMulAction.toAddMonoidHom_apply]
    have w :=
      AddMonoidHom.congr_fun (φ.naturality (ModuleCat.asHomRight (LinearMap.toSpanSingleton R M x)))
        (1 : R)
    convert w.symm
    exact (one_smul _ _).symm
  map_add' := by
    intros
    ext
    simp [add_smul]
  map_mul' := by
    intros
    ext
    simpa using mul_smul _ _ _
#align ring_equiv_End_forget₂ ringEquivEndForget₂

