/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathbin.Algebra.Hom.NonUnitalAlg
import Mathbin.Algebra.Star.Prod

/-!
# Morphisms of star algebras

This file defines morphisms between `R`-algebras (unital or non-unital) `A` and `B` where both
`A` and `B` are equipped with a `star` operation. These morphisms, namely `star_alg_hom` and
`non_unital_star_alg_hom` are direct extensions of their non-`star`red counterparts with a field
`map_star` which guarantees they preserve the star operation. We keep the type classes as generic
as possible, in keeping with the definition of `non_unital_alg_hom` in the non-unital case. In this
file, we only assume `has_star` unless we want to talk about the zero map as a
`non_unital_star_alg_hom`, in which case we need `star_add_monoid`. Note that the scalar ring `R`
is not required to have a star operation, nor do we need `star_ring` or `star_module` structures on
`A` and `B`.

As with `non_unital_alg_hom`, in the non-unital case the multiplications are not assumed to be
associative or unital, or even to be compatible with the scalar actions. In a typical application,
the operations will satisfy compatibility conditions making them into algebras (albeit possibly
non-associative and/or non-unital) but such conditions are not required here for the definitions.

The primary impetus for defining these types is that they constitute the morphisms in the categories
of unital C⋆-algebras (with `star_alg_hom`s) and of C⋆-algebras (with `non_unital_star_alg_hom`s).

TODO: add `star_alg_equiv`.

## Main definitions

  * `non_unital_alg_hom`
  * `star_alg_hom`

## Tags

non-unital, algebra, morphism, star
-/


/-! ### Non-unital star algebra homomorphisms -/


/-- A *non-unital ⋆-algebra homomorphism* is a non-unital algebra homomorphism between
non-unital `R`-algebras `A` and `B` equipped with a `star` operation, and this homomorphism is
also `star`-preserving. -/
structure NonUnitalStarAlgHom (R A B : Type _) [Monoidₓ R] [NonUnitalNonAssocSemiringₓ A] [DistribMulAction R A]
  [HasStar A] [NonUnitalNonAssocSemiringₓ B] [DistribMulAction R B] [HasStar B] extends A →ₙₐ[R] B where
  map_star' : ∀ a : A, to_fun (star a) = star (to_fun a)

-- mathport name: «expr →⋆ₙₐ »
infixr:25 " →⋆ₙₐ " => NonUnitalStarAlgHom _

-- mathport name: «expr →⋆ₙₐ[ ] »
notation:25 A " →⋆ₙₐ[" R "] " B => NonUnitalStarAlgHom R A B

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Command.lean:665:43: in add_decl_doc #[[ident non_unital_star_alg_hom.to_non_unital_alg_hom]]: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- `non_unital_star_alg_hom_class F R A B` asserts `F` is a type of bundled non-unital ⋆-algebra
homomorphisms from `A` to `B`. -/
class NonUnitalStarAlgHomClass (F : Type _) (R : outParam (Type _)) (A : outParam (Type _)) (B : outParam (Type _))
  [Monoidₓ R] [HasStar A] [HasStar B] [NonUnitalNonAssocSemiringₓ A] [NonUnitalNonAssocSemiringₓ B]
  [DistribMulAction R A] [DistribMulAction R B] extends NonUnitalAlgHomClass F R A B, StarHomClass F A B

-- `R` becomes a metavariable but that's fine because it's an `out_param`
attribute [nolint dangerous_instance] NonUnitalStarAlgHomClass.toStarHomClass

namespace NonUnitalStarAlgHom

section Basic

variable {R A B C D : Type _} [Monoidₓ R]

variable [NonUnitalNonAssocSemiringₓ A] [DistribMulAction R A] [HasStar A]

variable [NonUnitalNonAssocSemiringₓ B] [DistribMulAction R B] [HasStar B]

variable [NonUnitalNonAssocSemiringₓ C] [DistribMulAction R C] [HasStar C]

variable [NonUnitalNonAssocSemiringₓ D] [DistribMulAction R D] [HasStar D]

instance : NonUnitalStarAlgHomClass (A →⋆ₙₐ[R] B) R A B where
  coe := toFun
  coe_injective' := by
    rintro ⟨f, _⟩ ⟨g, _⟩ ⟨h⟩ <;> congr
  map_smul := fun f => f.map_smul'
  map_add := fun f => f.map_add'
  map_zero := fun f => f.map_zero'
  map_mul := fun f => f.map_mul'
  map_star := fun f => f.map_star'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (A →⋆ₙₐ[R] B) fun _ => A → B :=
  FunLike.hasCoeToFun

initialize_simps_projections NonUnitalStarAlgHom (toFun → apply)

@[simp]
theorem coe_to_non_unital_alg_hom {f : A →⋆ₙₐ[R] B} : (f.toNonUnitalAlgHom : A → B) = f :=
  rfl

@[ext]
theorem ext {f g : A →⋆ₙₐ[R] B} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext _ _ h

/-- Copy of a `non_unital_star_alg_hom` with a new `to_fun` equal to the old one. Useful
to fix definitional equalities. -/
protected def copy (f : A →⋆ₙₐ[R] B) (f' : A → B) (h : f' = f) : A →⋆ₙₐ[R] B where
  toFun := f'
  map_smul' := h.symm ▸ map_smul f
  map_zero' := h.symm ▸ map_zero f
  map_add' := h.symm ▸ map_add f
  map_mul' := h.symm ▸ map_mul f
  map_star' := h.symm ▸ map_star f

@[simp]
theorem coe_mk (f : A → B) (h₁ h₂ h₃ h₄ h₅) : ((⟨f, h₁, h₂, h₃, h₄, h₅⟩ : A →⋆ₙₐ[R] B) : A → B) = f :=
  rfl

@[simp]
theorem mk_coe (f : A →⋆ₙₐ[R] B) (h₁ h₂ h₃ h₄ h₅) : (⟨f, h₁, h₂, h₃, h₄, h₅⟩ : A →⋆ₙₐ[R] B) = f := by
  ext
  rfl

section

variable (R A)

/-- The identity as a non-unital ⋆-algebra homomorphism. -/
protected def id : A →⋆ₙₐ[R] A :=
  { (1 : A →ₙₐ[R] A) with map_star' := fun x => rfl }

@[simp]
theorem coe_id : ⇑(NonUnitalStarAlgHom.id R A) = id :=
  rfl

end

/-- The composition of non-unital ⋆-algebra homomorphisms, as a non-unital ⋆-algebra
homomorphism. -/
def comp (f : B →⋆ₙₐ[R] C) (g : A →⋆ₙₐ[R] B) : A →⋆ₙₐ[R] C :=
  { f.toNonUnitalAlgHom.comp g.toNonUnitalAlgHom with
    map_star' := by
      simp only [map_star, NonUnitalAlgHom.to_fun_eq_coe, eq_self_iff_true, NonUnitalAlgHom.coe_comp,
        coe_to_non_unital_alg_hom, Function.comp_app, forall_const] }

@[simp]
theorem coe_comp (f : B →⋆ₙₐ[R] C) (g : A →⋆ₙₐ[R] B) : ⇑(comp f g) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : B →⋆ₙₐ[R] C) (g : A →⋆ₙₐ[R] B) (a : A) : comp f g a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : C →⋆ₙₐ[R] D) (g : B →⋆ₙₐ[R] C) (h : A →⋆ₙₐ[R] B) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem id_comp (f : A →⋆ₙₐ[R] B) : (NonUnitalStarAlgHom.id _ _).comp f = f :=
  ext fun _ => rfl

@[simp]
theorem comp_id (f : A →⋆ₙₐ[R] B) : f.comp (NonUnitalStarAlgHom.id _ _) = f :=
  ext fun _ => rfl

instance : Monoidₓ (A →⋆ₙₐ[R] A) where
  mul := comp
  mul_assoc := comp_assoc
  one := NonUnitalStarAlgHom.id R A
  one_mul := id_comp
  mul_one := comp_id

@[simp]
theorem coe_one : ((1 : A →⋆ₙₐ[R] A) : A → A) = id :=
  rfl

theorem one_apply (a : A) : (1 : A →⋆ₙₐ[R] A) a = a :=
  rfl

end Basic

section Zero

-- the `zero` requires extra type class assumptions because we need `star_zero`
variable {R A B C D : Type _} [Monoidₓ R]

variable [NonUnitalNonAssocSemiringₓ A] [DistribMulAction R A] [StarAddMonoid A]

variable [NonUnitalNonAssocSemiringₓ B] [DistribMulAction R B] [StarAddMonoid B]

instance : Zero (A →⋆ₙₐ[R] B) :=
  ⟨{ (0 : NonUnitalAlgHom R A B) with
      map_star' := by
        simp }⟩

instance : Inhabited (A →⋆ₙₐ[R] B) :=
  ⟨0⟩

instance : MonoidWithZeroₓ (A →⋆ₙₐ[R] A) :=
  { NonUnitalStarAlgHom.monoid, NonUnitalStarAlgHom.hasZero with zero_mul := fun f => ext fun x => rfl,
    mul_zero := fun f => ext fun x => map_zero f }

@[simp]
theorem coe_zero : ((0 : A →⋆ₙₐ[R] B) : A → B) = 0 :=
  rfl

theorem zero_apply (a : A) : (0 : A →⋆ₙₐ[R] B) a = 0 :=
  rfl

end Zero

end NonUnitalStarAlgHom

/-! ### Unital star algebra homomorphisms -/


section Unital

/-- A *⋆-algebra homomorphism* is an algebra homomorphism between `R`-algebras `A` and `B`
equipped with a `star` operation, and this homomorphism is also `star`-preserving. -/
structure StarAlgHom (R A B : Type _) [CommSemiringₓ R] [Semiringₓ A] [Algebra R A] [HasStar A] [Semiringₓ B]
  [Algebra R B] [HasStar B] extends AlgHom R A B where
  map_star' : ∀ x : A, to_fun (star x) = star (to_fun x)

-- mathport name: «expr →⋆ₐ »
infixr:25 " →⋆ₐ " => StarAlgHom _

-- mathport name: «expr →⋆ₐ[ ] »
notation:25 A " →⋆ₐ[" R "] " B => StarAlgHom R A B

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Command.lean:665:43: in add_decl_doc #[[ident star_alg_hom.to_alg_hom]]: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- `star_alg_hom_class F R A B` states that `F` is a type of ⋆-algebra homomorphisms.

You should also extend this typeclass when you extend `star_alg_hom`. -/
class StarAlgHomClass (F : Type _) (R : outParam (Type _)) (A : outParam (Type _)) (B : outParam (Type _))
  [CommSemiringₓ R] [Semiringₓ A] [Algebra R A] [HasStar A] [Semiringₓ B] [Algebra R B] [HasStar B] extends
  AlgHomClass F R A B, StarHomClass F A B

-- `R` becomes a metavariable but that's fine because it's an `out_param`
attribute [nolint dangerous_instance] StarAlgHomClass.toStarHomClass

-- See note [lower instance priority]
instance (priority := 100) StarAlgHomClass.toNonUnitalStarAlgHomClass (F R A B : Type _) [CommSemiringₓ R] [Semiringₓ A]
    [Algebra R A] [HasStar A] [Semiringₓ B] [Algebra R B] [HasStar B] [StarAlgHomClass F R A B] :
    NonUnitalStarAlgHomClass F R A B :=
  { StarAlgHomClass.toAlgHomClass F R A B, StarAlgHomClass.toStarHomClass F R A B with map_smul := map_smul }

namespace StarAlgHom

variable {F R A B C D : Type _} [CommSemiringₓ R] [Semiringₓ A] [Algebra R A] [HasStar A] [Semiringₓ B] [Algebra R B]
  [HasStar B] [Semiringₓ C] [Algebra R C] [HasStar C] [Semiringₓ D] [Algebra R D] [HasStar D]

instance : StarAlgHomClass (A →⋆ₐ[R] B) R A B where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by
    obtain ⟨_, _, _, _, _, _, _⟩ := f <;> obtain ⟨_, _, _, _, _, _, _⟩ := g <;> congr
  map_mul := map_mul'
  map_one := map_one'
  map_add := map_add'
  map_zero := map_zero'
  commutes := commutes'
  map_star := map_star'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (A →⋆ₐ[R] B) fun _ => A → B :=
  FunLike.hasCoeToFun

@[simp]
theorem coe_to_alg_hom {f : A →⋆ₐ[R] B} : (f.toAlgHom : A → B) = f :=
  rfl

@[ext]
theorem ext {f g : A →⋆ₐ[R] B} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext _ _ h

/-- Copy of a `star_alg_hom` with a new `to_fun` equal to the old one. Useful
to fix definitional equalities. -/
protected def copy (f : A →⋆ₐ[R] B) (f' : A → B) (h : f' = f) : A →⋆ₐ[R] B where
  toFun := f'
  map_one' := h.symm ▸ map_one f
  map_mul' := h.symm ▸ map_mul f
  map_zero' := h.symm ▸ map_zero f
  map_add' := h.symm ▸ map_add f
  commutes' := h.symm ▸ AlgHomClass.commutes f
  map_star' := h.symm ▸ map_star f

@[simp]
theorem coe_mk (f : A → B) (h₁ h₂ h₃ h₄ h₅ h₆) : ((⟨f, h₁, h₂, h₃, h₄, h₅, h₆⟩ : A →⋆ₐ[R] B) : A → B) = f :=
  rfl

@[simp]
theorem mk_coe (f : A →⋆ₐ[R] B) (h₁ h₂ h₃ h₄ h₅ h₆) : (⟨f, h₁, h₂, h₃, h₄, h₅, h₆⟩ : A →⋆ₐ[R] B) = f := by
  ext
  rfl

section

variable (R A)

/-- The identity as a `star_alg_hom`. -/
protected def id : A →⋆ₐ[R] A :=
  { AlgHom.id _ _ with map_star' := fun x => rfl }

@[simp]
theorem coe_id : ⇑(StarAlgHom.id R A) = id :=
  rfl

end

instance : Inhabited (A →⋆ₐ[R] A) :=
  ⟨StarAlgHom.id R A⟩

/-- The composition of ⋆-algebra homomorphisms, as a ⋆-algebra homomorphism. -/
def comp (f : B →⋆ₐ[R] C) (g : A →⋆ₐ[R] B) : A →⋆ₐ[R] C :=
  { f.toAlgHom.comp g.toAlgHom with
    map_star' := by
      simp only [map_star, AlgHom.to_fun_eq_coe, AlgHom.coe_comp, coe_to_alg_hom, Function.comp_app, eq_self_iff_true,
        forall_const] }

@[simp]
theorem coe_comp (f : B →⋆ₐ[R] C) (g : A →⋆ₐ[R] B) : ⇑(comp f g) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : B →⋆ₐ[R] C) (g : A →⋆ₐ[R] B) (a : A) : comp f g a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : C →⋆ₐ[R] D) (g : B →⋆ₐ[R] C) (h : A →⋆ₐ[R] B) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem id_comp (f : A →⋆ₐ[R] B) : (StarAlgHom.id _ _).comp f = f :=
  ext fun _ => rfl

@[simp]
theorem comp_id (f : A →⋆ₐ[R] B) : f.comp (StarAlgHom.id _ _) = f :=
  ext fun _ => rfl

instance : Monoidₓ (A →⋆ₐ[R] A) where
  mul := comp
  mul_assoc := comp_assoc
  one := StarAlgHom.id R A
  one_mul := id_comp
  mul_one := comp_id

/-- A unital morphism of ⋆-algebras is a `non_unital_star_alg_hom`. -/
def toNonUnitalStarAlgHom (f : A →⋆ₐ[R] B) : A →⋆ₙₐ[R] B :=
  { f with map_smul' := map_smul f }

@[simp]
theorem coe_to_non_unital_star_alg_hom (f : A →⋆ₐ[R] B) : (f.toNonUnitalStarAlgHom : A → B) = f :=
  rfl

end StarAlgHom

end Unital

/-! ### Operations on the product type

Note that this is copied from [`algebra/hom/non_unital_alg`](non_unital_alg). -/


namespace NonUnitalStarAlgHom

section Prod

variable (R A B C : Type _) [Monoidₓ R] [NonUnitalNonAssocSemiringₓ A] [DistribMulAction R A] [HasStar A]
  [NonUnitalNonAssocSemiringₓ B] [DistribMulAction R B] [HasStar B] [NonUnitalNonAssocSemiringₓ C]
  [DistribMulAction R C] [HasStar C]

/-- The first projection of a product is a non-unital ⋆-algebra homomoprhism. -/
@[simps]
def fst : A × B →⋆ₙₐ[R] A :=
  { NonUnitalAlgHom.fst R A B with map_star' := fun x => rfl }

/-- The second projection of a product is a non-unital ⋆-algebra homomorphism. -/
@[simps]
def snd : A × B →⋆ₙₐ[R] B :=
  { NonUnitalAlgHom.snd R A B with map_star' := fun x => rfl }

variable {R A B C}

/-- The `pi.prod` of two morphisms is a morphism. -/
@[simps]
def prod (f : A →⋆ₙₐ[R] B) (g : A →⋆ₙₐ[R] C) : A →⋆ₙₐ[R] B × C :=
  { f.toNonUnitalAlgHom.Prod g.toNonUnitalAlgHom with
    map_star' := fun x => by
      simp [map_star, Prod.star_def] }

theorem coe_prod (f : A →⋆ₙₐ[R] B) (g : A →⋆ₙₐ[R] C) : ⇑(f.Prod g) = Pi.prod f g :=
  rfl

@[simp]
theorem fst_prod (f : A →⋆ₙₐ[R] B) (g : A →⋆ₙₐ[R] C) : (fst R B C).comp (prod f g) = f := by
  ext <;> rfl

@[simp]
theorem snd_prod (f : A →⋆ₙₐ[R] B) (g : A →⋆ₙₐ[R] C) : (snd R B C).comp (prod f g) = g := by
  ext <;> rfl

@[simp]
theorem prod_fst_snd : prod (fst R A B) (snd R A B) = 1 :=
  FunLike.coe_injective Pi.prod_fst_snd

/-- Taking the product of two maps with the same domain is equivalent to taking the product of
their codomains. -/
@[simps]
def prodEquiv : (A →⋆ₙₐ[R] B) × (A →⋆ₙₐ[R] C) ≃ (A →⋆ₙₐ[R] B × C) where
  toFun := fun f => f.1.Prod f.2
  invFun := fun f => ((fst _ _ _).comp f, (snd _ _ _).comp f)
  left_inv := fun f => by
    ext <;> rfl
  right_inv := fun f => by
    ext <;> rfl

end Prod

section InlInr

variable (R A B C : Type _) [Monoidₓ R] [NonUnitalNonAssocSemiringₓ A] [DistribMulAction R A] [StarAddMonoid A]
  [NonUnitalNonAssocSemiringₓ B] [DistribMulAction R B] [StarAddMonoid B] [NonUnitalNonAssocSemiringₓ C]
  [DistribMulAction R C] [StarAddMonoid C]

/-- The left injection into a product is a non-unital algebra homomorphism. -/
def inl : A →⋆ₙₐ[R] A × B :=
  prod 1 0

/-- The right injection into a product is a non-unital algebra homomorphism. -/
def inr : B →⋆ₙₐ[R] A × B :=
  prod 0 1

variable {R A B}

@[simp]
theorem coe_inl : (inl R A B : A → A × B) = fun x => (x, 0) :=
  rfl

theorem inl_apply (x : A) : inl R A B x = (x, 0) :=
  rfl

@[simp]
theorem coe_inr : (inr R A B : B → A × B) = Prod.mk 0 :=
  rfl

theorem inr_apply (x : B) : inr R A B x = (0, x) :=
  rfl

end InlInr

end NonUnitalStarAlgHom

namespace StarAlgHom

variable (R A B C : Type _) [CommSemiringₓ R] [Semiringₓ A] [Algebra R A] [HasStar A] [Semiringₓ B] [Algebra R B]
  [HasStar B] [Semiringₓ C] [Algebra R C] [HasStar C]

/-- The first projection of a product is a ⋆-algebra homomoprhism. -/
@[simps]
def fst : A × B →⋆ₐ[R] A :=
  { AlgHom.fst R A B with map_star' := fun x => rfl }

/-- The second projection of a product is a ⋆-algebra homomorphism. -/
@[simps]
def snd : A × B →⋆ₐ[R] B :=
  { AlgHom.snd R A B with map_star' := fun x => rfl }

variable {R A B C}

/-- The `pi.prod` of two morphisms is a morphism. -/
@[simps]
def prod (f : A →⋆ₐ[R] B) (g : A →⋆ₐ[R] C) : A →⋆ₐ[R] B × C :=
  { f.toAlgHom.Prod g.toAlgHom with
    map_star' := fun x => by
      simp [Prod.star_def, map_star] }

theorem coe_prod (f : A →⋆ₐ[R] B) (g : A →⋆ₐ[R] C) : ⇑(f.Prod g) = Pi.prod f g :=
  rfl

@[simp]
theorem fst_prod (f : A →⋆ₐ[R] B) (g : A →⋆ₐ[R] C) : (fst R B C).comp (prod f g) = f := by
  ext <;> rfl

@[simp]
theorem snd_prod (f : A →⋆ₐ[R] B) (g : A →⋆ₐ[R] C) : (snd R B C).comp (prod f g) = g := by
  ext <;> rfl

@[simp]
theorem prod_fst_snd : prod (fst R A B) (snd R A B) = 1 :=
  FunLike.coe_injective Pi.prod_fst_snd

/-- Taking the product of two maps with the same domain is equivalent to taking the product of
their codomains. -/
@[simps]
def prodEquiv : (A →⋆ₐ[R] B) × (A →⋆ₐ[R] C) ≃ (A →⋆ₐ[R] B × C) where
  toFun := fun f => f.1.Prod f.2
  invFun := fun f => ((fst _ _ _).comp f, (snd _ _ _).comp f)
  left_inv := fun f => by
    ext <;> rfl
  right_inv := fun f => by
    ext <;> rfl

end StarAlgHom

