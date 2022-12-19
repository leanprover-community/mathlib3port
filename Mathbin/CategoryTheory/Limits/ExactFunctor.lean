/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module category_theory.limits.exact_functor
! leanprover-community/mathlib commit bbeb185db4ccee8ed07dc48449414ebfa39cb821
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
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
#align category_theory.LeftExactFunctor CategoryTheory.LeftExactFunctorCat

-- mathport name: «expr ⥤ₗ »
infixr:26 " ⥤ₗ " => LeftExactFunctorCat

/-- A left exact functor is in particular a functor. -/
def LeftExactFunctorCat.forget : (C ⥤ₗ D) ⥤ C ⥤ D :=
  fullSubcategoryInclusion _ deriving Full, Faithful
#align category_theory.LeftExactFunctor.forget CategoryTheory.LeftExactFunctorCat.forget

/-- Bundled right-exact functors. -/
@[nolint has_nonempty_instance]
def RightExactFunctorCat :=
  FullSubcategory fun F : C ⥤ D => Nonempty (PreservesFiniteColimits F)deriving Category
#align category_theory.RightExactFunctor CategoryTheory.RightExactFunctorCat

-- mathport name: «expr ⥤ᵣ »
infixr:26 " ⥤ᵣ " => RightExactFunctorCat

/-- A right exact functor is in particular a functor. -/
def RightExactFunctorCat.forget : (C ⥤ᵣ D) ⥤ C ⥤ D :=
  fullSubcategoryInclusion _ deriving Full, Faithful
#align category_theory.RightExactFunctor.forget CategoryTheory.RightExactFunctorCat.forget

/-- Bundled exact functors. -/
@[nolint has_nonempty_instance]
def ExactFunctorCat :=
  FullSubcategory fun F : C ⥤ D =>
    Nonempty (PreservesFiniteLimits F) ∧ Nonempty (PreservesFiniteColimits F)deriving
  Category
#align category_theory.ExactFunctor CategoryTheory.ExactFunctorCat

-- mathport name: «expr ⥤ₑ »
infixr:26 " ⥤ₑ " => ExactFunctorCat

/-- An exact functor is in particular a functor. -/
def ExactFunctorCat.forget : (C ⥤ₑ D) ⥤ C ⥤ D :=
  fullSubcategoryInclusion _ deriving Full, Faithful
#align category_theory.ExactFunctor.forget CategoryTheory.ExactFunctorCat.forget

/-- Turn an exact functor into a left exact functor. -/
def LeftExactFunctorCat.ofExact : (C ⥤ₑ D) ⥤ C ⥤ₗ D :=
  FullSubcategory.map fun X => And.left deriving Full, Faithful
#align category_theory.LeftExactFunctor.of_exact CategoryTheory.LeftExactFunctorCat.ofExact

/-- Turn an exact functor into a left exact functor. -/
def RightExactFunctorCat.ofExact : (C ⥤ₑ D) ⥤ C ⥤ᵣ D :=
  FullSubcategory.map fun X => And.right deriving Full, Faithful
#align category_theory.RightExactFunctor.of_exact CategoryTheory.RightExactFunctorCat.ofExact

variable {C D}

@[simp]
theorem LeftExactFunctorCat.of_exact_obj (F : C ⥤ₑ D) :
    (LeftExactFunctorCat.ofExact C D).obj F = ⟨F.1, F.2.1⟩ :=
  rfl
#align category_theory.LeftExactFunctor.of_exact_obj CategoryTheory.LeftExactFunctorCat.of_exact_obj

@[simp]
theorem RightExactFunctorCat.of_exact_obj (F : C ⥤ₑ D) :
    (RightExactFunctorCat.ofExact C D).obj F = ⟨F.1, F.2.2⟩ :=
  rfl
#align
  category_theory.RightExactFunctor.of_exact_obj CategoryTheory.RightExactFunctorCat.of_exact_obj

@[simp]
theorem LeftExactFunctorCat.of_exact_map {F G : C ⥤ₑ D} (α : F ⟶ G) :
    (LeftExactFunctorCat.ofExact C D).map α = α :=
  rfl
#align category_theory.LeftExactFunctor.of_exact_map CategoryTheory.LeftExactFunctorCat.of_exact_map

@[simp]
theorem RightExactFunctorCat.of_exact_map {F G : C ⥤ₑ D} (α : F ⟶ G) :
    (RightExactFunctorCat.ofExact C D).map α = α :=
  rfl
#align
  category_theory.RightExactFunctor.of_exact_map CategoryTheory.RightExactFunctorCat.of_exact_map

@[simp]
theorem LeftExactFunctorCat.forget_obj (F : C ⥤ₗ D) :
    (LeftExactFunctorCat.forget C D).obj F = F.1 :=
  rfl
#align category_theory.LeftExactFunctor.forget_obj CategoryTheory.LeftExactFunctorCat.forget_obj

@[simp]
theorem RightExactFunctorCat.forget_obj (F : C ⥤ᵣ D) :
    (RightExactFunctorCat.forget C D).obj F = F.1 :=
  rfl
#align category_theory.RightExactFunctor.forget_obj CategoryTheory.RightExactFunctorCat.forget_obj

@[simp]
theorem ExactFunctorCat.forget_obj (F : C ⥤ₑ D) : (ExactFunctorCat.forget C D).obj F = F.1 :=
  rfl
#align category_theory.ExactFunctor.forget_obj CategoryTheory.ExactFunctorCat.forget_obj

@[simp]
theorem LeftExactFunctorCat.forget_map {F G : C ⥤ₗ D} (α : F ⟶ G) :
    (LeftExactFunctorCat.forget C D).map α = α :=
  rfl
#align category_theory.LeftExactFunctor.forget_map CategoryTheory.LeftExactFunctorCat.forget_map

@[simp]
theorem RightExactFunctorCat.forget_map {F G : C ⥤ᵣ D} (α : F ⟶ G) :
    (RightExactFunctorCat.forget C D).map α = α :=
  rfl
#align category_theory.RightExactFunctor.forget_map CategoryTheory.RightExactFunctorCat.forget_map

@[simp]
theorem ExactFunctorCat.forget_map {F G : C ⥤ₑ D} (α : F ⟶ G) :
    (ExactFunctorCat.forget C D).map α = α :=
  rfl
#align category_theory.ExactFunctor.forget_map CategoryTheory.ExactFunctorCat.forget_map

/-- Turn a left exact functor into an object of the category `LeftExactFunctor C D`. -/
def LeftExactFunctorCat.of (F : C ⥤ D) [PreservesFiniteLimits F] : C ⥤ₗ D :=
  ⟨F, ⟨inferInstance⟩⟩
#align category_theory.LeftExactFunctor.of CategoryTheory.LeftExactFunctorCat.of

/-- Turn a right exact functor into an object of the category `RightExactFunctor C D`. -/
def RightExactFunctorCat.of (F : C ⥤ D) [PreservesFiniteColimits F] : C ⥤ᵣ D :=
  ⟨F, ⟨inferInstance⟩⟩
#align category_theory.RightExactFunctor.of CategoryTheory.RightExactFunctorCat.of

/-- Turn an exact functor into an object of the category `ExactFunctor C D`. -/
def ExactFunctorCat.of (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteColimits F] : C ⥤ₑ D :=
  ⟨F, ⟨⟨inferInstance⟩, ⟨inferInstance⟩⟩⟩
#align category_theory.ExactFunctor.of CategoryTheory.ExactFunctorCat.of

@[simp]
theorem LeftExactFunctorCat.of_fst (F : C ⥤ D) [PreservesFiniteLimits F] :
    (LeftExactFunctorCat.of F).obj = F :=
  rfl
#align category_theory.LeftExactFunctor.of_fst CategoryTheory.LeftExactFunctorCat.of_fst

@[simp]
theorem RightExactFunctorCat.of_fst (F : C ⥤ D) [PreservesFiniteColimits F] :
    (RightExactFunctorCat.of F).obj = F :=
  rfl
#align category_theory.RightExactFunctor.of_fst CategoryTheory.RightExactFunctorCat.of_fst

@[simp]
theorem ExactFunctorCat.of_fst (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (ExactFunctorCat.of F).obj = F :=
  rfl
#align category_theory.ExactFunctor.of_fst CategoryTheory.ExactFunctorCat.of_fst

theorem LeftExactFunctorCat.forget_obj_of (F : C ⥤ D) [PreservesFiniteLimits F] :
    (LeftExactFunctorCat.forget C D).obj (LeftExactFunctorCat.of F) = F :=
  rfl
#align
  category_theory.LeftExactFunctor.forget_obj_of CategoryTheory.LeftExactFunctorCat.forget_obj_of

theorem RightExactFunctorCat.forget_obj_of (F : C ⥤ D) [PreservesFiniteColimits F] :
    (RightExactFunctorCat.forget C D).obj (RightExactFunctorCat.of F) = F :=
  rfl
#align
  category_theory.RightExactFunctor.forget_obj_of CategoryTheory.RightExactFunctorCat.forget_obj_of

theorem ExactFunctorCat.forget_obj_of (F : C ⥤ D) [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] : (ExactFunctorCat.forget C D).obj (ExactFunctorCat.of F) = F :=
  rfl
#align category_theory.ExactFunctor.forget_obj_of CategoryTheory.ExactFunctorCat.forget_obj_of

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

