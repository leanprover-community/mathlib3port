/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Algebra.Subalgebra.Basic
import Mathbin.Algebra.FreeAlgebra
import Mathbin.Algebra.Category.RingCat.Basic
import Mathbin.Algebra.Category.ModuleCat.Basic

/-!
# Category instance for algebras over a commutative ring

We introduce the bundled category `Algebra` of algebras over a fixed commutative ring `R ` along
with the forgetful functors to `Ring` and `Module`. We furthermore show that the functor associating
to a type the free `R`-algebra on that type is left adjoint to the forgetful functor.
-/


open CategoryTheory

open CategoryTheory.Limits

universe v u

variable (R : Type u) [CommRing R]

/-- The category of R-algebras and their morphisms. -/
structure AlgebraCat where
  Carrier : Type v
  [isRing : Ring carrier]
  [isAlgebra : Algebra R carrier]

attribute [instance] AlgebraCat.isRing AlgebraCat.isAlgebra

namespace AlgebraCat

instance : CoeSort (AlgebraCat R) (Type v) :=
  ⟨AlgebraCat.Carrier⟩

instance : Category (AlgebraCat.{v} R) where
  hom A B := A →ₐ[R] B
  id A := AlgHom.id R A
  comp A B C f g := g.comp f

instance : ConcreteCategory.{v} (AlgebraCat.{v} R) where
  forget := { obj := fun R => R, map := fun R S f => (f : R → S) }
  forget_faithful := {  }

instance hasForgetToRing :
    HasForget₂ (AlgebraCat.{v} R)
      RingCat.{v} where forget₂ := { obj := fun A => RingCat.of A, map := fun A₁ A₂ f => AlgHom.toRingHom f }

instance hasForgetToModule :
    HasForget₂ (AlgebraCat.{v} R)
      (ModuleCat.{v}
        R) where forget₂ := { obj := fun M => ModuleCat.of R M, map := fun M₁ M₂ f => AlgHom.toLinearMap f }

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. -/
def of (X : Type v) [Ring X] [Algebra R X] : AlgebraCat.{v} R :=
  ⟨X⟩

/-- Typecheck a `alg_hom` as a morphism in `Algebra R`. -/
def ofHom {R : Type u} [CommRing R] {X Y : Type v} [Ring X] [Algebra R X] [Ring Y] [Algebra R Y] (f : X →ₐ[R] Y) :
    of R X ⟶ of R Y :=
  f

@[simp]
theorem of_hom_apply {R : Type u} [CommRing R] {X Y : Type v} [Ring X] [Algebra R X] [Ring Y] [Algebra R Y]
    (f : X →ₐ[R] Y) (x : X) : ofHom f x = f x :=
  rfl

instance : Inhabited (AlgebraCat R) :=
  ⟨of R R⟩

@[simp]
theorem coe_of (X : Type u) [Ring X] [Algebra R X] : (of R X : Type u) = X :=
  rfl

variable {R}

/-- Forgetting to the underlying type and then building the bundled object returns the original
algebra. -/
@[simps]
def ofSelfIso (M : AlgebraCat.{v} R) : AlgebraCat.of R M ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M

variable {R} {M N U : ModuleCat.{v} R}

@[simp]
theorem id_apply (m : M) : (𝟙 M : M → M) m = m :=
  rfl

@[simp]
theorem coe_comp (f : M ⟶ N) (g : N ⟶ U) : (f ≫ g : M → U) = g ∘ f :=
  rfl

variable (R)

/-- The "free algebra" functor, sending a type `S` to the free algebra on `S`. -/
@[simps]
def free : Type u ⥤ AlgebraCat.{u} R where
  obj S := { Carrier := FreeAlgebra R S, isRing := Algebra.semiringToRing R }
  map S T f := FreeAlgebra.lift _ <| FreeAlgebra.ι _ ∘ f
  -- obviously can fill the next two goals, but it is slow
  map_id' := by
    intro X
    ext1
    simp only [FreeAlgebra.ι_comp_lift]
    rfl
  map_comp' := by
    intros
    ext1
    simp only [FreeAlgebra.ι_comp_lift]
    ext1
    simp only [FreeAlgebra.lift_ι_apply, CategoryTheory.coe_comp, Function.comp_app, types_comp_apply]

/-- The free/forget adjunction for `R`-algebras. -/
def adj : free.{u} R ⊣ forget (AlgebraCat.{u} R) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X A =>
        (FreeAlgebra.lift _).symm,-- Relying on `obviously` to fill out these proofs is very slow :(
      hom_equiv_naturality_left_symm' := by
        intros
        ext
        simp only [free_map, Equiv.symm_symm, FreeAlgebra.lift_ι_apply, CategoryTheory.coe_comp, Function.comp_app,
          types_comp_apply],
      hom_equiv_naturality_right' := by
        intros
        ext
        simp only [forget_map_eq_coe, CategoryTheory.coe_comp, Function.comp_app, FreeAlgebra.lift_symm_apply,
          types_comp_apply] }

instance : IsRightAdjoint (forget (AlgebraCat.{u} R)) :=
  ⟨_, adj R⟩

end AlgebraCat

variable {R}

variable {X₁ X₂ : Type u}

/-- Build an isomorphism in the category `Algebra R` from a `alg_equiv` between `algebra`s. -/
@[simps]
def AlgEquiv.toAlgebraIso {g₁ : Ring X₁} {g₂ : Ring X₂} {m₁ : Algebra R X₁} {m₂ : Algebra R X₂} (e : X₁ ≃ₐ[R] X₂) :
    AlgebraCat.of R X₁ ≅ AlgebraCat.of R X₂ where
  hom := (e : X₁ →ₐ[R] X₂)
  inv := (e.symm : X₂ →ₐ[R] X₁)
  hom_inv_id' := by
    ext
    exact e.left_inv x
  inv_hom_id' := by
    ext
    exact e.right_inv x

namespace CategoryTheory.Iso

/-- Build a `alg_equiv` from an isomorphism in the category `Algebra R`. -/
@[simps]
def toAlgEquiv {X Y : AlgebraCat R} (i : X ≅ Y) : X ≃ₐ[R] Y where
  toFun := i.hom
  invFun := i.inv
  left_inv := by tidy
  right_inv := by tidy
  map_add' := by tidy
  map_mul' := by tidy
  commutes' := by tidy

end CategoryTheory.Iso

/-- Algebra equivalences between `algebras`s are the same as (isomorphic to) isomorphisms in
`Algebra`. -/
@[simps]
def algEquivIsoAlgebraIso {X Y : Type u} [Ring X] [Ring Y] [Algebra R X] [Algebra R Y] :
    (X ≃ₐ[R] Y) ≅ AlgebraCat.of R X ≅ AlgebraCat.of R Y where
  hom e := e.toAlgebraIso
  inv i := i.toAlgEquiv

instance (X : Type u) [Ring X] [Algebra R X] : Coe (Subalgebra R X) (AlgebraCat R) :=
  ⟨fun N => AlgebraCat.of R N⟩

instance AlgebraCat.forget_reflects_isos :
    ReflectsIsomorphisms (forget (AlgebraCat.{u} R)) where reflects X Y f _ := by
    skip
    let i := as_iso ((forget (AlgebraCat.{u} R)).map f)
    let e : X ≃ₐ[R] Y := { f, i.to_equiv with }
    exact ⟨(is_iso.of_iso e.to_Algebra_iso).1⟩

