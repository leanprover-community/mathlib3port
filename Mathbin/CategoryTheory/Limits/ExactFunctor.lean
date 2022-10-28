/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathbin.CategoryTheory.Limits.Preserves.Finite

/-!
# Bundled exact functors

We say that a functor `F` is left exact if it preserves finite limits, it is right exact if it
preserves finite colimits, and it is exact if it is both left exact and right exact.

In this file, we define the categories of bundled left exact, right exact and exact functors.

-/


universe v₁ v₂ u₁ u₂

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

section

variable (C) (D)

/-- Bundled left-exact functors. -/
@[nolint has_nonempty_instance]
def LeftExactFunctorCat :=
  FullSubcategory fun F : C ⥤ D => Nonempty (PreservesFiniteLimits F)deriving Category

-- mathport name: «expr ⥤ₗ »
infixr:26 " ⥤ₗ " => LeftExactFunctorCat

/-- A left exact functor is in particular a functor. -/
def LeftExactFunctorCat.forget : (C ⥤ₗ D) ⥤ C ⥤ D :=
  fullSubcategoryInclusion _ deriving Full, Faithful

/-- Bundled right-exact functors. -/
@[nolint has_nonempty_instance]
def RightExactFunctorCat :=
  FullSubcategory fun F : C ⥤ D => Nonempty (PreservesFiniteColimits F)deriving Category

-- mathport name: «expr ⥤ᵣ »
infixr:26 " ⥤ᵣ " => RightExactFunctorCat

/-- A right exact functor is in particular a functor. -/
def RightExactFunctorCat.forget : (C ⥤ᵣ D) ⥤ C ⥤ D :=
  fullSubcategoryInclusion _ deriving Full, Faithful

/-- Bundled exact functors. -/
@[nolint has_nonempty_instance]
def ExactFunctorCat :=
  FullSubcategory fun F : C ⥤ D => Nonempty (PreservesFiniteLimits F) ∧ Nonempty (PreservesFiniteColimits F)deriving
  Category

-- mathport name: «expr ⥤ₑ »
infixr:26 " ⥤ₑ " => ExactFunctorCat

/-- An exact functor is in particular a functor. -/
def ExactFunctorCat.forget : (C ⥤ₑ D) ⥤ C ⥤ D :=
  fullSubcategoryInclusion _ deriving Full, Faithful

/-- Turn an exact functor into a left exact functor. -/
def LeftExactFunctorCat.ofExact : (C ⥤ₑ D) ⥤ C ⥤ₗ D :=
  FullSubcategory.map fun X => And.left deriving Full, Faithful

/-- Turn an exact functor into a left exact functor. -/
def RightExactFunctorCat.ofExact : (C ⥤ₑ D) ⥤ C ⥤ᵣ D :=
  FullSubcategory.map fun X => And.right deriving Full, Faithful

variable {C D}

@[simp]
theorem LeftExactFunctorCat.of_exact_obj (F : C ⥤ₑ D) : (LeftExactFunctorCat.ofExact C D).obj F = ⟨F.1, F.2.1⟩ :=
  rfl

@[simp]
theorem RightExactFunctorCat.of_exact_obj (F : C ⥤ₑ D) : (RightExactFunctorCat.ofExact C D).obj F = ⟨F.1, F.2.2⟩ :=
  rfl

@[simp]
theorem LeftExactFunctorCat.of_exact_map {F G : C ⥤ₑ D} (α : F ⟶ G) : (LeftExactFunctorCat.ofExact C D).map α = α :=
  rfl

@[simp]
theorem RightExactFunctorCat.of_exact_map {F G : C ⥤ₑ D} (α : F ⟶ G) : (RightExactFunctorCat.ofExact C D).map α = α :=
  rfl

@[simp]
theorem LeftExactFunctorCat.forget_obj (F : C ⥤ₗ D) : (LeftExactFunctorCat.forget C D).obj F = F.1 :=
  rfl

@[simp]
theorem RightExactFunctorCat.forget_obj (F : C ⥤ᵣ D) : (RightExactFunctorCat.forget C D).obj F = F.1 :=
  rfl

@[simp]
theorem ExactFunctorCat.forget_obj (F : C ⥤ₑ D) : (ExactFunctorCat.forget C D).obj F = F.1 :=
  rfl

@[simp]
theorem LeftExactFunctorCat.forget_map {F G : C ⥤ₗ D} (α : F ⟶ G) : (LeftExactFunctorCat.forget C D).map α = α :=
  rfl

@[simp]
theorem RightExactFunctorCat.forget_map {F G : C ⥤ᵣ D} (α : F ⟶ G) : (RightExactFunctorCat.forget C D).map α = α :=
  rfl

@[simp]
theorem ExactFunctorCat.forget_map {F G : C ⥤ₑ D} (α : F ⟶ G) : (ExactFunctorCat.forget C D).map α = α :=
  rfl

/-- Turn a left exact functor into an object of the category `LeftExactFunctor C D`. -/
def LeftExactFunctorCat.of (F : C ⥤ D) [PreservesFiniteLimits F] : C ⥤ₗ D :=
  ⟨F, ⟨inferInstance⟩⟩

/-- Turn a right exact functor into an object of the category `RightExactFunctor C D`. -/
def RightExactFunctorCat.of (F : C ⥤ D) [PreservesFiniteColimits F] : C ⥤ᵣ D :=
  ⟨F, ⟨inferInstance⟩⟩

/-- Turn an exact functor into an object of the category `ExactFunctor C D`. -/
def ExactFunctorCat.of (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteColimits F] : C ⥤ₑ D :=
  ⟨F, ⟨⟨inferInstance⟩, ⟨inferInstance⟩⟩⟩

@[simp]
theorem LeftExactFunctorCat.of_fst (F : C ⥤ D) [PreservesFiniteLimits F] : (LeftExactFunctorCat.of F).obj = F :=
  rfl

@[simp]
theorem RightExactFunctorCat.of_fst (F : C ⥤ D) [PreservesFiniteColimits F] : (RightExactFunctorCat.of F).obj = F :=
  rfl

@[simp]
theorem ExactFunctorCat.of_fst (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (ExactFunctorCat.of F).obj = F :=
  rfl

theorem LeftExactFunctorCat.forget_obj_of (F : C ⥤ D) [PreservesFiniteLimits F] :
    (LeftExactFunctorCat.forget C D).obj (LeftExactFunctorCat.of F) = F :=
  rfl

theorem RightExactFunctorCat.forget_obj_of (F : C ⥤ D) [PreservesFiniteColimits F] :
    (RightExactFunctorCat.forget C D).obj (RightExactFunctorCat.of F) = F :=
  rfl

theorem ExactFunctorCat.forget_obj_of (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (ExactFunctorCat.forget C D).obj (ExactFunctorCat.of F) = F :=
  rfl

noncomputable instance (F : C ⥤ₗ D) : PreservesFiniteLimits F.obj :=
  F.property.some

noncomputable instance (F : C ⥤ᵣ D) : PreservesFiniteColimits F.obj :=
  F.property.some

noncomputable instance (F : C ⥤ₑ D) : PreservesFiniteLimits F.obj :=
  F.property.1.some

noncomputable instance (F : C ⥤ₑ D) : PreservesFiniteColimits F.obj :=
  F.property.2.some

end

end CategoryTheory

