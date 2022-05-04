/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Hom.Group
import Mathbin.CategoryTheory.DiscreteCategory
import Mathbin.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Monoids as discrete monoidal categories

The discrete category on a monoid is a monoidal category.
Multiplicative morphisms induced monoidal functors.
-/


universe u

open CategoryTheory

open CategoryTheory.Discrete

variable (M : Type u) [Monoidₓ M]

namespace CategoryTheory

@[to_additive]
instance monoidDiscrete : Monoidₓ (Discrete M) := by
  dsimp' [discrete]
  infer_instance

@[to_additive Discrete.addMonoidal]
instance Discrete.monoidal : MonoidalCategory (Discrete M) where
  tensorUnit := 1
  tensorObj := fun X Y => X * Y
  tensorHom := fun W X Y Z f g =>
    eqToHom
      (by
        rw [eq_of_hom f, eq_of_hom g])
  leftUnitor := fun X => eqToIso (one_mulₓ X)
  rightUnitor := fun X => eqToIso (mul_oneₓ X)
  associator := fun X Y Z => eqToIso (mul_assoc _ _ _)

variable {M} {N : Type u} [Monoidₓ N]

/-- A multiplicative morphism between monoids gives a monoidal functor between the corresponding
discrete monoidal categories.
-/
@[to_additive Discrete.addMonoidalFunctor
      "An additive morphism between add_monoids gives a\n  monoidal functor between the corresponding discrete monoidal categories.",
  simps]
def Discrete.monoidalFunctor (F : M →* N) : MonoidalFunctor (Discrete M) (Discrete N) where
  obj := F
  map := fun X Y f => eqToHom (F.congr_arg (eq_of_hom f))
  ε := eqToHom F.map_one.symm
  μ := fun X Y => eqToHom (F.map_mul X Y).symm

variable {K : Type u} [Monoidₓ K]

/-- The monoidal natural isomorphism corresponding to composing two multiplicative morphisms.
-/
@[to_additive Discrete.addMonoidalFunctorComp
      "The monoidal natural isomorphism corresponding to\ncomposing two additive morphisms."]
def Discrete.monoidalFunctorComp (F : M →* N) (G : N →* K) :
    Discrete.monoidalFunctor F ⊗⋙ Discrete.monoidalFunctor G ≅ Discrete.monoidalFunctor (G.comp F) where
  Hom := { app := fun X => 𝟙 _ }
  inv := { app := fun X => 𝟙 _ }

end CategoryTheory

