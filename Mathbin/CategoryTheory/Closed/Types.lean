/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import CategoryTheory.Limits.Presheaf
import CategoryTheory.Limits.Preserves.FunctorCategory
import CategoryTheory.Limits.Shapes.Types
import CategoryTheory.Closed.Cartesian

#align_import category_theory.closed.types from "leanprover-community/mathlib"@"fd4551cfe4b7484b81c2c9ba3405edae27659676"

/-!
# Cartesian closure of Type

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Show that `Type u₁` is cartesian closed, and `C ⥤ Type u₁` is cartesian closed for `C` a small
category in `Type u₁`.
Note this implies that the category of presheaves on a small category `C` is cartesian closed.
-/


namespace CategoryTheory

noncomputable section

open Category Limits

universe v₁ v₂ u₁ u₂

variable {C : Type v₂} [Category.{v₁} C]

section CartesianClosed

instance (X : Type v₁) : CategoryTheory.Functor.IsLeftAdjoint (Types.binaryProductFunctor.obj X)
    where
  right :=
    { obj := fun Y => X ⟶ Y
      map := fun Y₁ Y₂ f g => g ≫ f }
  adj :=
    Adjunction.mkOfUnitCounit
      { Unit := { app := fun Z (z : Z) x => ⟨x, z⟩ }
        counit := { app := fun Z xf => xf.2 xf.1 } }

instance : HasFiniteProducts (Type v₁) :=
  hasFiniteProducts_of_hasProducts.{v₁} _

instance : CartesianClosed (Type v₁)
    where closed' X := { is_adj := Functor.isLeftAdjoint_of_iso (Types.binaryProductIsoProd.app X) }

instance {C : Type u₁} [Category.{v₁} C] : HasFiniteProducts (C ⥤ Type u₁) :=
  hasFiniteProducts_of_hasProducts.{u₁} _

instance {C : Type v₁} [SmallCategory C] : CartesianClosed (C ⥤ Type v₁)
    where closed' F :=
    {
      is_adj := by
        letI := functor_category.prod_preserves_colimits F
        apply is_left_adjoint_of_preserves_colimits (prod.functor.obj F) }

end CartesianClosed

end CategoryTheory

