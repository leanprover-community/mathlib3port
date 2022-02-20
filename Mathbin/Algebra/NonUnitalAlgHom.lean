/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathbin.Algebra.Algebra.Basic

/-!
# Morphisms of non-unital algebras

This file defines morphisms between two types, each of which carries:
 * an addition,
 * an additive zero,
 * a multiplication,
 * a scalar action.

The multiplications are not assumed to be associative or unital, or even to be compatible with the
scalar actions. In a typical application, the operations will satisfy compatibility conditions
making them into algebras (albeit possibly non-associative and/or non-unital) but such conditions
are not required to make this definition.

This notion of morphism should be useful for any category of non-unital algebras. The motivating
application at the time it was introduced was to be able to state the adjunction property for
magma algebras. These are non-unital, non-associative algebras obtained by applying the
group-algebra construction except where we take a type carrying just `has_mul` instead of `group`.

For a plausible future application, one could take the non-unital algebra of compactly-supported
functions on a non-compact topological space. A proper map between a pair of such spaces
(contravariantly) induces a morphism between their algebras of compactly-supported functions which
will be a `non_unital_alg_hom`.

TODO: add `non_unital_alg_equiv` when needed.

## Main definitions

  * `non_unital_alg_hom`
  * `alg_hom.to_non_unital_alg_hom`

## Tags

non-unital, algebra, morphism
-/


universe u v w w₁ w₂ w₃

variable (R : Type u) (A : Type v) (B : Type w) (C : Type w₁)

/-- A morphism respecting addition, multiplication, and scalar multiplication. When these arise from
algebra structures, this is the same as a not-necessarily-unital morphism of algebras. -/
structure NonUnitalAlgHom [Monoidₓ R] [NonUnitalNonAssocSemiringₓ A] [DistribMulAction R A]
  [NonUnitalNonAssocSemiringₓ B] [DistribMulAction R B] extends A →+[R] B, MulHom A B

attribute [nolint doc_blame] NonUnitalAlgHom.toDistribMulActionHom

attribute [nolint doc_blame] NonUnitalAlgHom.toMulHom

namespace NonUnitalAlgHom

variable {R A B C} [Monoidₓ R]

variable [NonUnitalNonAssocSemiringₓ A] [DistribMulAction R A]

variable [NonUnitalNonAssocSemiringₓ B] [DistribMulAction R B]

variable [NonUnitalNonAssocSemiringₓ C] [DistribMulAction R C]

/-- see Note [function coercion] -/
instance : CoeFun (NonUnitalAlgHom R A B) fun _ => A → B :=
  ⟨toFun⟩

@[simp]
theorem to_fun_eq_coe (f : NonUnitalAlgHom R A B) : f.toFun = ⇑f :=
  rfl

initialize_simps_projections NonUnitalAlgHom (toFun → apply)

theorem coe_injective : @Function.Injective (NonUnitalAlgHom R A B) (A → B) coeFn := by
  rintro ⟨f, _⟩ ⟨g, _⟩ ⟨h⟩ <;> congr

@[ext]
theorem ext {f g : NonUnitalAlgHom R A B} (h : ∀ x, f x = g x) : f = g :=
  coe_injective <| funext h

theorem ext_iff {f g : NonUnitalAlgHom R A B} : f = g ↔ ∀ x, f x = g x :=
  ⟨by
    rintro rfl x
    rfl, ext⟩

theorem congr_fun {f g : NonUnitalAlgHom R A B} (h : f = g) (x : A) : f x = g x :=
  h ▸ rfl

@[simp]
theorem coe_mk (f : A → B) h₁ h₂ h₃ h₄ : ((⟨f, h₁, h₂, h₃, h₄⟩ : NonUnitalAlgHom R A B) : A → B) = f :=
  rfl

@[simp]
theorem mk_coe (f : NonUnitalAlgHom R A B) h₁ h₂ h₃ h₄ : (⟨f, h₁, h₂, h₃, h₄⟩ : NonUnitalAlgHom R A B) = f := by
  ext
  rfl

instance : Coe (NonUnitalAlgHom R A B) (A →+[R] B) :=
  ⟨toDistribMulActionHom⟩

instance : Coe (NonUnitalAlgHom R A B) (MulHom A B) :=
  ⟨toMulHom⟩

@[simp]
theorem to_distrib_mul_action_hom_eq_coe (f : NonUnitalAlgHom R A B) : f.toDistribMulActionHom = ↑f :=
  rfl

@[simp]
theorem to_mul_hom_eq_coe (f : NonUnitalAlgHom R A B) : f.toMulHom = ↑f :=
  rfl

@[simp, norm_cast]
theorem coe_to_distrib_mul_action_hom (f : NonUnitalAlgHom R A B) : ((f : A →+[R] B) : A → B) = f :=
  rfl

@[simp, norm_cast]
theorem coe_to_mul_hom (f : NonUnitalAlgHom R A B) : ((f : MulHom A B) : A → B) = f :=
  rfl

theorem to_distrib_mul_action_hom_injective {f g : NonUnitalAlgHom R A B} (h : (f : A →+[R] B) = (g : A →+[R] B)) :
    f = g := by
  ext a
  exact DistribMulActionHom.congr_fun h a

theorem to_mul_hom_injective {f g : NonUnitalAlgHom R A B} (h : (f : MulHom A B) = (g : MulHom A B)) : f = g := by
  ext a
  exact MulHom.congr_fun h a

@[norm_cast]
theorem coe_distrib_mul_action_hom_mk (f : NonUnitalAlgHom R A B) h₁ h₂ h₃ h₄ :
    ((⟨f, h₁, h₂, h₃, h₄⟩ : NonUnitalAlgHom R A B) : A →+[R] B) = ⟨f, h₁, h₂, h₃⟩ := by
  ext
  rfl

@[norm_cast]
theorem coe_mul_hom_mk (f : NonUnitalAlgHom R A B) h₁ h₂ h₃ h₄ :
    ((⟨f, h₁, h₂, h₃, h₄⟩ : NonUnitalAlgHom R A B) : MulHom A B) = ⟨f, h₄⟩ := by
  ext
  rfl

@[simp]
theorem map_smul (f : NonUnitalAlgHom R A B) (c : R) (x : A) : f (c • x) = c • f x :=
  f.toDistribMulActionHom.map_smul c x

@[simp]
theorem map_add (f : NonUnitalAlgHom R A B) (x y : A) : f (x + y) = f x + f y :=
  f.toDistribMulActionHom.map_add x y

@[simp]
theorem map_mul (f : NonUnitalAlgHom R A B) (x y : A) : f (x * y) = f x * f y :=
  f.toMulHom.map_mul x y

@[simp]
theorem map_zero (f : NonUnitalAlgHom R A B) : f 0 = 0 :=
  f.toDistribMulActionHom.map_zero

instance : Zero (NonUnitalAlgHom R A B) :=
  ⟨{ (0 : A →+[R] B) with
      map_mul' := by
        simp }⟩

instance : One (NonUnitalAlgHom R A A) :=
  ⟨{ (1 : A →+[R] A) with
      map_mul' := by
        simp }⟩

@[simp]
theorem coe_zero : ((0 : NonUnitalAlgHom R A B) : A → B) = 0 :=
  rfl

@[simp]
theorem coe_one : ((1 : NonUnitalAlgHom R A A) : A → A) = id :=
  rfl

theorem zero_apply (a : A) : (0 : NonUnitalAlgHom R A B) a = 0 :=
  rfl

theorem one_apply (a : A) : (1 : NonUnitalAlgHom R A A) a = a :=
  rfl

instance : Inhabited (NonUnitalAlgHom R A B) :=
  ⟨0⟩

/-- The composition of morphisms is a morphism. -/
def comp (f : NonUnitalAlgHom R B C) (g : NonUnitalAlgHom R A B) : NonUnitalAlgHom R A C :=
  { (f : MulHom B C).comp (g : MulHom A B), (f : B →+[R] C).comp (g : A →+[R] B) with }

@[simp, norm_cast]
theorem coe_comp (f : NonUnitalAlgHom R B C) (g : NonUnitalAlgHom R A B) :
    (f.comp g : A → C) = (f : B → C) ∘ (g : A → B) :=
  rfl

theorem comp_apply (f : NonUnitalAlgHom R B C) (g : NonUnitalAlgHom R A B) (x : A) : f.comp g x = f (g x) :=
  rfl

/-- The inverse of a bijective morphism is a morphism. -/
def inverse (f : NonUnitalAlgHom R A B) (g : B → A) (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    NonUnitalAlgHom R B A :=
  { (f : MulHom A B).inverse g h₁ h₂, (f : A →+[R] B).inverse g h₁ h₂ with }

@[simp]
theorem coe_inverse (f : NonUnitalAlgHom R A B) (g : B → A) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : (inverse f g h₁ h₂ : B → A) = g :=
  rfl

end NonUnitalAlgHom

namespace AlgHom

variable {R A B} [CommSemiringₓ R] [Semiringₓ A] [Semiringₓ B] [Algebra R A] [Algebra R B]

/-- A unital morphism of algebras is a `non_unital_alg_hom`. -/
def toNonUnitalAlgHom (f : A →ₐ[R] B) : NonUnitalAlgHom R A B :=
  { f with map_smul' := f.map_smul }

instance NonUnitalAlgHom.hasCoe : Coe (A →ₐ[R] B) (NonUnitalAlgHom R A B) :=
  ⟨toNonUnitalAlgHom⟩

@[simp]
theorem to_non_unital_alg_hom_eq_coe (f : A →ₐ[R] B) : f.toNonUnitalAlgHom = f :=
  rfl

@[simp, norm_cast]
theorem coe_to_non_unital_alg_hom (f : A →ₐ[R] B) : ((f : NonUnitalAlgHom R A B) : A → B) = f :=
  rfl

end AlgHom

