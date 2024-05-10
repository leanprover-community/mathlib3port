/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Algebra.Group.Hom.Defs
import CategoryTheory.DiscreteCategory
import CategoryTheory.Monoidal.NaturalTransformation

#align_import category_theory.monoidal.discrete from "leanprover-community/mathlib"@"31ca6f9cf5f90a6206092cd7f84b359dcb6d52e0"

/-!
# Monoids as discrete monoidal categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The discrete category on a monoid is a monoidal category.
Multiplicative morphisms induced monoidal functors.
-/


universe u

open CategoryTheory

open CategoryTheory.Discrete

variable (M : Type u) [Monoid M]

namespace CategoryTheory

#print CategoryTheory.Discrete.monoidal /-
@[to_additive Discrete.addMonoidal, simps tensor_obj_as tensor_unit_as]
instance Discrete.monoidal : MonoidalCategory (Discrete M)
    where
  tensorUnit := Discrete.mk 1
  tensorObj X Y := Discrete.mk (X.as * Y.as)
  tensorHom W X Y Z f g := eqToHom (by rw [eq_of_hom f, eq_of_hom g])
  leftUnitor X := Discrete.eqToIso (one_mul X.as)
  rightUnitor X := Discrete.eqToIso (mul_one X.as)
  associator X Y Z := Discrete.eqToIso (mul_assoc _ _ _)
#align category_theory.discrete.monoidal CategoryTheory.Discrete.monoidal
#align category_theory.discrete.add_monoidal CategoryTheory.Discrete.addMonoidal
-/

variable {M} {N : Type u} [Monoid N]

#print CategoryTheory.Discrete.monoidalFunctor /-
/-- A multiplicative morphism between monoids gives a monoidal functor between the corresponding
discrete monoidal categories.
-/
@[to_additive Discrete.addMonoidalFunctor
      "An additive morphism between add_monoids gives a\n  monoidal functor between the corresponding discrete monoidal categories.",
  simps]
def Discrete.monoidalFunctor (F : M →* N) : MonoidalFunctor (Discrete M) (Discrete N)
    where
  obj X := Discrete.mk (F X.as)
  map X Y f := Discrete.eqToHom (F.congr_arg (eq_of_hom f))
  ε := Discrete.eqToHom F.map_one.symm
  μ X Y := Discrete.eqToHom (F.map_hMul X.as Y.as).symm
#align category_theory.discrete.monoidal_functor CategoryTheory.Discrete.monoidalFunctor
#align category_theory.discrete.add_monoidal_functor CategoryTheory.Discrete.addMonoidalFunctor
-/

variable {K : Type u} [Monoid K]

/- ././././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.Discrete.monoidalFunctorComp /-
/-- The monoidal natural isomorphism corresponding to composing two multiplicative morphisms.
-/
@[to_additive Discrete.addMonoidalFunctorComp
      "The monoidal natural isomorphism corresponding to\ncomposing two additive morphisms."]
def Discrete.monoidalFunctorComp (F : M →* N) (G : N →* K) :
    Discrete.monoidalFunctor F ⊗⋙ Discrete.monoidalFunctor G ≅ Discrete.monoidalFunctor (G.comp F)
    where
  Hom := { app := fun X => 𝟙 _ }
  inv := { app := fun X => 𝟙 _ }
#align category_theory.discrete.monoidal_functor_comp CategoryTheory.Discrete.monoidalFunctorComp
#align category_theory.discrete.add_monoidal_functor_comp CategoryTheory.Discrete.addMonoidalFunctorComp
-/

end CategoryTheory

