import Mathbin.CategoryTheory.Monoidal.NaturalTransformation
import Mathbin.CategoryTheory.DiscreteCategory
import Mathbin.Algebra.Group.Hom

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
instance monoid_discrete : Monoidₓ (discrete M) := by
  dsimp [discrete]
  infer_instance

@[to_additive Discrete.addMonoidal]
instance discrete.monoidal : monoidal_category (discrete M) where
  tensorUnit := 1
  tensorObj := fun X Y => X * Y
  tensorHom := fun W X Y Z f g =>
    eq_to_hom
      (by
        rw [eq_of_hom f, eq_of_hom g])
  leftUnitor := fun X => eq_to_iso (one_mulₓ X)
  rightUnitor := fun X => eq_to_iso (mul_oneₓ X)
  associator := fun X Y Z => eq_to_iso (mul_assoc _ _ _)

variable {M} {N : Type u} [Monoidₓ N]

/-- A multiplicative morphism between monoids gives a monoidal functor between the corresponding
discrete monoidal categories.
-/
@[to_additive Dicrete.addMonoidalFunctor
      "An additive morphism between add_monoids gives a\n  monoidal functor between the corresponding discrete monoidal categories.",
  simps]
def discrete.monoidal_functor (F : M →* N) : monoidal_functor (discrete M) (discrete N) where
  obj := F
  map := fun X Y f => eq_to_hom (F.congr_arg (eq_of_hom f))
  ε := eq_to_hom F.map_one.symm
  μ := fun X Y => eq_to_hom (F.map_mul X Y).symm

variable {K : Type u} [Monoidₓ K]

/-- The monoidal natural isomorphism corresponding to composing two multiplicative morphisms.
-/
@[to_additive Dicrete.addMonoidalFunctorComp
      "The monoidal natural isomorphism corresponding to\ncomposing two additive morphisms."]
def discrete.monoidal_functor_comp (F : M →* N) (G : N →* K) :
    discrete.monoidal_functor F ⊗⋙ discrete.monoidal_functor G ≅ discrete.monoidal_functor (G.comp F) where
  Hom := { app := fun X => 𝟙 _ }
  inv := { app := fun X => 𝟙 _ }

end CategoryTheory

