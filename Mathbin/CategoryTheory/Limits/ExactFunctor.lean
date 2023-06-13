/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module category_theory.limits.exact_functor
! leanprover-community/mathlib commit f47581155c818e6361af4e4fda60d27d020c226b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Preserves.Finite

/-!
# Bundled exact functors

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

#print CategoryTheory.LeftExactFunctor /-
/-- Bundled left-exact functors. -/
@[nolint has_nonempty_instance]
def LeftExactFunctor :=
  FullSubcategory fun F : C ⥤ D => Nonempty (PreservesFiniteLimits F)
deriving Category
#align category_theory.LeftExactFunctor CategoryTheory.LeftExactFunctor
-/

infixr:26 " ⥤ₗ " => LeftExactFunctor

#print CategoryTheory.LeftExactFunctor.forget /-
/-- A left exact functor is in particular a functor. -/
def LeftExactFunctor.forget : (C ⥤ₗ D) ⥤ C ⥤ D :=
  fullSubcategoryInclusion _
deriving Full, Faithful
#align category_theory.LeftExactFunctor.forget CategoryTheory.LeftExactFunctor.forget
-/

#print CategoryTheory.RightExactFunctor /-
/-- Bundled right-exact functors. -/
@[nolint has_nonempty_instance]
def RightExactFunctor :=
  FullSubcategory fun F : C ⥤ D => Nonempty (PreservesFiniteColimits F)
deriving Category
#align category_theory.RightExactFunctor CategoryTheory.RightExactFunctor
-/

infixr:26 " ⥤ᵣ " => RightExactFunctor

#print CategoryTheory.RightExactFunctor.forget /-
/-- A right exact functor is in particular a functor. -/
def RightExactFunctor.forget : (C ⥤ᵣ D) ⥤ C ⥤ D :=
  fullSubcategoryInclusion _
deriving Full, Faithful
#align category_theory.RightExactFunctor.forget CategoryTheory.RightExactFunctor.forget
-/

#print CategoryTheory.ExactFunctor /-
/-- Bundled exact functors. -/
@[nolint has_nonempty_instance]
def ExactFunctor :=
  FullSubcategory fun F : C ⥤ D =>
    Nonempty (PreservesFiniteLimits F) ∧ Nonempty (PreservesFiniteColimits F)
deriving Category
#align category_theory.ExactFunctor CategoryTheory.ExactFunctor
-/

infixr:26 " ⥤ₑ " => ExactFunctor

#print CategoryTheory.ExactFunctor.forget /-
/-- An exact functor is in particular a functor. -/
def ExactFunctor.forget : (C ⥤ₑ D) ⥤ C ⥤ D :=
  fullSubcategoryInclusion _
deriving Full, Faithful
#align category_theory.ExactFunctor.forget CategoryTheory.ExactFunctor.forget
-/

#print CategoryTheory.LeftExactFunctor.ofExact /-
/-- Turn an exact functor into a left exact functor. -/
def LeftExactFunctor.ofExact : (C ⥤ₑ D) ⥤ C ⥤ₗ D :=
  FullSubcategory.map fun X => And.left
deriving Full, Faithful
#align category_theory.LeftExactFunctor.of_exact CategoryTheory.LeftExactFunctor.ofExact
-/

#print CategoryTheory.RightExactFunctor.ofExact /-
/-- Turn an exact functor into a left exact functor. -/
def RightExactFunctor.ofExact : (C ⥤ₑ D) ⥤ C ⥤ᵣ D :=
  FullSubcategory.map fun X => And.right
deriving Full, Faithful
#align category_theory.RightExactFunctor.of_exact CategoryTheory.RightExactFunctor.ofExact
-/

variable {C D}

#print CategoryTheory.LeftExactFunctor.ofExact_obj /-
@[simp]
theorem LeftExactFunctor.ofExact_obj (F : C ⥤ₑ D) :
    (LeftExactFunctor.ofExact C D).obj F = ⟨F.1, F.2.1⟩ :=
  rfl
#align category_theory.LeftExactFunctor.of_exact_obj CategoryTheory.LeftExactFunctor.ofExact_obj
-/

#print CategoryTheory.RightExactFunctor.ofExact_obj /-
@[simp]
theorem RightExactFunctor.ofExact_obj (F : C ⥤ₑ D) :
    (RightExactFunctor.ofExact C D).obj F = ⟨F.1, F.2.2⟩ :=
  rfl
#align category_theory.RightExactFunctor.of_exact_obj CategoryTheory.RightExactFunctor.ofExact_obj
-/

#print CategoryTheory.LeftExactFunctor.ofExact_map /-
@[simp]
theorem LeftExactFunctor.ofExact_map {F G : C ⥤ₑ D} (α : F ⟶ G) :
    (LeftExactFunctor.ofExact C D).map α = α :=
  rfl
#align category_theory.LeftExactFunctor.of_exact_map CategoryTheory.LeftExactFunctor.ofExact_map
-/

#print CategoryTheory.RightExactFunctor.ofExact_map /-
@[simp]
theorem RightExactFunctor.ofExact_map {F G : C ⥤ₑ D} (α : F ⟶ G) :
    (RightExactFunctor.ofExact C D).map α = α :=
  rfl
#align category_theory.RightExactFunctor.of_exact_map CategoryTheory.RightExactFunctor.ofExact_map
-/

#print CategoryTheory.LeftExactFunctor.forget_obj /-
@[simp]
theorem LeftExactFunctor.forget_obj (F : C ⥤ₗ D) : (LeftExactFunctor.forget C D).obj F = F.1 :=
  rfl
#align category_theory.LeftExactFunctor.forget_obj CategoryTheory.LeftExactFunctor.forget_obj
-/

#print CategoryTheory.RightExactFunctor.forget_obj /-
@[simp]
theorem RightExactFunctor.forget_obj (F : C ⥤ᵣ D) : (RightExactFunctor.forget C D).obj F = F.1 :=
  rfl
#align category_theory.RightExactFunctor.forget_obj CategoryTheory.RightExactFunctor.forget_obj
-/

#print CategoryTheory.ExactFunctor.forget_obj /-
@[simp]
theorem ExactFunctor.forget_obj (F : C ⥤ₑ D) : (ExactFunctor.forget C D).obj F = F.1 :=
  rfl
#align category_theory.ExactFunctor.forget_obj CategoryTheory.ExactFunctor.forget_obj
-/

#print CategoryTheory.LeftExactFunctor.forget_map /-
@[simp]
theorem LeftExactFunctor.forget_map {F G : C ⥤ₗ D} (α : F ⟶ G) :
    (LeftExactFunctor.forget C D).map α = α :=
  rfl
#align category_theory.LeftExactFunctor.forget_map CategoryTheory.LeftExactFunctor.forget_map
-/

#print CategoryTheory.RightExactFunctor.forget_map /-
@[simp]
theorem RightExactFunctor.forget_map {F G : C ⥤ᵣ D} (α : F ⟶ G) :
    (RightExactFunctor.forget C D).map α = α :=
  rfl
#align category_theory.RightExactFunctor.forget_map CategoryTheory.RightExactFunctor.forget_map
-/

#print CategoryTheory.ExactFunctor.forget_map /-
@[simp]
theorem ExactFunctor.forget_map {F G : C ⥤ₑ D} (α : F ⟶ G) : (ExactFunctor.forget C D).map α = α :=
  rfl
#align category_theory.ExactFunctor.forget_map CategoryTheory.ExactFunctor.forget_map
-/

#print CategoryTheory.LeftExactFunctor.of /-
/-- Turn a left exact functor into an object of the category `LeftExactFunctor C D`. -/
def LeftExactFunctor.of (F : C ⥤ D) [PreservesFiniteLimits F] : C ⥤ₗ D :=
  ⟨F, ⟨inferInstance⟩⟩
#align category_theory.LeftExactFunctor.of CategoryTheory.LeftExactFunctor.of
-/

#print CategoryTheory.RightExactFunctor.of /-
/-- Turn a right exact functor into an object of the category `RightExactFunctor C D`. -/
def RightExactFunctor.of (F : C ⥤ D) [PreservesFiniteColimits F] : C ⥤ᵣ D :=
  ⟨F, ⟨inferInstance⟩⟩
#align category_theory.RightExactFunctor.of CategoryTheory.RightExactFunctor.of
-/

#print CategoryTheory.ExactFunctor.of /-
/-- Turn an exact functor into an object of the category `ExactFunctor C D`. -/
def ExactFunctor.of (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteColimits F] : C ⥤ₑ D :=
  ⟨F, ⟨⟨inferInstance⟩, ⟨inferInstance⟩⟩⟩
#align category_theory.ExactFunctor.of CategoryTheory.ExactFunctor.of
-/

#print CategoryTheory.LeftExactFunctor.of_fst /-
@[simp]
theorem LeftExactFunctor.of_fst (F : C ⥤ D) [PreservesFiniteLimits F] :
    (LeftExactFunctor.of F).obj = F :=
  rfl
#align category_theory.LeftExactFunctor.of_fst CategoryTheory.LeftExactFunctor.of_fst
-/

#print CategoryTheory.RightExactFunctor.of_fst /-
@[simp]
theorem RightExactFunctor.of_fst (F : C ⥤ D) [PreservesFiniteColimits F] :
    (RightExactFunctor.of F).obj = F :=
  rfl
#align category_theory.RightExactFunctor.of_fst CategoryTheory.RightExactFunctor.of_fst
-/

#print CategoryTheory.ExactFunctor.of_fst /-
@[simp]
theorem ExactFunctor.of_fst (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (ExactFunctor.of F).obj = F :=
  rfl
#align category_theory.ExactFunctor.of_fst CategoryTheory.ExactFunctor.of_fst
-/

#print CategoryTheory.LeftExactFunctor.forget_obj_of /-
theorem LeftExactFunctor.forget_obj_of (F : C ⥤ D) [PreservesFiniteLimits F] :
    (LeftExactFunctor.forget C D).obj (LeftExactFunctor.of F) = F :=
  rfl
#align category_theory.LeftExactFunctor.forget_obj_of CategoryTheory.LeftExactFunctor.forget_obj_of
-/

#print CategoryTheory.RightExactFunctor.forget_obj_of /-
theorem RightExactFunctor.forget_obj_of (F : C ⥤ D) [PreservesFiniteColimits F] :
    (RightExactFunctor.forget C D).obj (RightExactFunctor.of F) = F :=
  rfl
#align category_theory.RightExactFunctor.forget_obj_of CategoryTheory.RightExactFunctor.forget_obj_of
-/

#print CategoryTheory.ExactFunctor.forget_obj_of /-
theorem ExactFunctor.forget_obj_of (F : C ⥤ D) [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] : (ExactFunctor.forget C D).obj (ExactFunctor.of F) = F :=
  rfl
#align category_theory.ExactFunctor.forget_obj_of CategoryTheory.ExactFunctor.forget_obj_of
-/

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

