import Mathbin.Algebra.Free 
import Mathbin.Algebra.MonoidAlgebra.Basic

/-!
# Free algebras

Given a semiring `R` and a type `X`, we construct the free non-unital, non-associative algebra on
`X` with coefficients in `R`, together with its universal property. The construction is valuable
because it can be used to build free algebras with more structure, e.g., free Lie algebras.

Note that elsewhere we have a construction of the free unital, associative algebra. This is called
`free_algebra`.

## Main definitions

  * `free_non_unital_non_assoc_algebra`
  * `free_non_unital_non_assoc_algebra.lift`
  * `free_non_unital_non_assoc_algebra.of`

## Implementation details

We construct the free algebra as the magma algebra, with coefficients in `R`, of the free magma on
`X`. However we regard this as an implementation detail and thus deliberately omit the lemmas
`of_apply` and `lift_apply`, and we mark `free_non_unital_non_assoc_algebra` and `lift` as
irreducible once we have established the universal property.

## Tags

free algebra, non-unital, non-associative, free magma, magma algebra, universal property,
forgetful functor, adjoint functor
-/


universe u v w

noncomputable section 

variable (R : Type u) (X : Type v) [Semiringₓ R]

-- ././Mathport/Syntax/Translate/Basic.lean:748:9: unsupported derive handler inhabited
-- ././Mathport/Syntax/Translate/Basic.lean:748:9: unsupported derive handler non_unital_non_assoc_semiring
-- ././Mathport/Syntax/Translate/Basic.lean:748:9: unsupported derive handler module R
/-- The free non-unital, non-associative algebra on the type `X` with coefficients in `R`. -/
def FreeNonUnitalNonAssocAlgebra :=
  MonoidAlgebra R (FreeMagma X)deriving [anonymous], [anonymous], [anonymous]

namespace FreeNonUnitalNonAssocAlgebra

variable {X}

/-- The embedding of `X` into the free algebra with coefficients in `R`. -/
def of : X → FreeNonUnitalNonAssocAlgebra R X :=
  MonoidAlgebra.ofMagma R _ ∘ FreeMagma.of

instance : IsScalarTower R (FreeNonUnitalNonAssocAlgebra R X) (FreeNonUnitalNonAssocAlgebra R X) :=
  MonoidAlgebra.is_scalar_tower_self R

/-- If the coefficients are commutative amongst themselves, they also commute with the algebra
multiplication. -/
instance (R : Type u) [CommSemiringₓ R] :
  SmulCommClass R (FreeNonUnitalNonAssocAlgebra R X) (FreeNonUnitalNonAssocAlgebra R X) :=
  MonoidAlgebra.smul_comm_class_self R

instance (R : Type u) [Ringₓ R] : AddCommGroupₓ (FreeNonUnitalNonAssocAlgebra R X) :=
  Module.addCommMonoidToAddCommGroup R

variable {A : Type w} [NonUnitalNonAssocSemiring A]

variable [Module R A] [IsScalarTower R A A] [SmulCommClass R A A]

/-- The functor `X ↦ free_non_unital_non_assoc_algebra R X` from the category of types to the
category of non-unital, non-associative algebras over `R` is adjoint to the forgetful functor in the
other direction. -/
def lift : (X → A) ≃ NonUnitalAlgHom R (FreeNonUnitalNonAssocAlgebra R X) A :=
  FreeMagma.lift.trans (MonoidAlgebra.liftMagma R)

@[simp]
theorem lift_symm_apply (F : NonUnitalAlgHom R (FreeNonUnitalNonAssocAlgebra R X) A) : (lift R).symm F = F ∘ of R :=
  rfl

@[simp]
theorem of_comp_lift (f : X → A) : lift R f ∘ of R = f :=
  (lift R).left_inv f

@[simp]
theorem lift_unique (f : X → A) (F : NonUnitalAlgHom R (FreeNonUnitalNonAssocAlgebra R X) A) :
  F ∘ of R = f ↔ F = lift R f :=
  (lift R).symm_apply_eq

@[simp]
theorem lift_of_apply (f : X → A) x : lift R f (of R x) = f x :=
  by 
    rw [←Function.comp_app (lift R f) (of R) x, of_comp_lift]

@[simp]
theorem lift_comp_of (F : NonUnitalAlgHom R (FreeNonUnitalNonAssocAlgebra R X) A) : lift R (F ∘ of R) = F :=
  by 
    rw [←lift_symm_apply, Equivₓ.apply_symm_apply]

@[ext]
theorem hom_ext {F₁ F₂ : NonUnitalAlgHom R (FreeNonUnitalNonAssocAlgebra R X) A} (h : ∀ x, F₁ (of R x) = F₂ (of R x)) :
  F₁ = F₂ :=
  have h' : (lift R).symm F₁ = (lift R).symm F₂ :=
    by 
      ext 
      simp [h]
  (lift R).symm.Injective h'

end FreeNonUnitalNonAssocAlgebra

