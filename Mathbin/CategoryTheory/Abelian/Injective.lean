/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer

! This file was ported from Lean 3 source module category_theory.abelian.injective
! leanprover-community/mathlib commit f8d8465c3c392a93b9ed226956e26dee00975946
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Abelian.Exact
import Mathbin.CategoryTheory.Preadditive.Injective
import Mathbin.CategoryTheory.Preadditive.Yoneda.Limits
import Mathbin.CategoryTheory.Preadditive.Yoneda.Injective

/-!
# Injective objects in abelian categories

* Objects in an abelian categories are injective if and only if the preadditive Yoneda functor
  on them preserves finite colimits.
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Injective

open Opposite

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/- warning: category_theory.preserves_finite_colimits_preadditive_yoneda_obj_of_injective -> CategoryTheory.preservesFiniteColimitsPreadditiveYonedaObjOfInjective is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Abelian.{u1, u2} C _inst_1] (J : C) [hP : CategoryTheory.Injective.{u1, u2} C _inst_1 J], CategoryTheory.Limits.PreservesFiniteColimits.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (ModuleCat.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) J) (CategoryTheory.Preadditive.CategoryTheory.End.ring.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2) J)) (ModuleCat.moduleCategory.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) J) (CategoryTheory.Preadditive.CategoryTheory.End.ring.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2) J)) (CategoryTheory.preadditiveYonedaObj.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2) J)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Abelian.{u1, u2} C _inst_1] (J : C) [hP : CategoryTheory.Injective.{u1, u2} C _inst_1 J], CategoryTheory.Limits.PreservesFiniteColimits.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (ModuleCat.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) J) (CategoryTheory.Preadditive.instRingEndToCategoryStruct.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2) J)) (ModuleCat.moduleCategory.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) J) (CategoryTheory.Preadditive.instRingEndToCategoryStruct.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2) J)) (CategoryTheory.preadditiveYonedaObj.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2) J)
Case conversion may be inaccurate. Consider using '#align category_theory.preserves_finite_colimits_preadditive_yoneda_obj_of_injective CategoryTheory.preservesFiniteColimitsPreadditiveYonedaObjOfInjectiveₓ'. -/
/-- The preadditive Yoneda functor on `J` preserves colimits if `J` is injective. -/
def preservesFiniteColimitsPreadditiveYonedaObjOfInjective (J : C) [hP : Injective J] :
    PreservesFiniteColimits (preadditiveYonedaObj J) :=
  by
  letI := (injective_iff_preserves_epimorphisms_preadditive_yoneda_obj' J).mp hP
  apply functor.preserves_finite_colimits_of_preserves_epis_and_kernels
#align category_theory.preserves_finite_colimits_preadditive_yoneda_obj_of_injective CategoryTheory.preservesFiniteColimitsPreadditiveYonedaObjOfInjective

/- warning: category_theory.injective_of_preserves_finite_colimits_preadditive_yoneda_obj -> CategoryTheory.injective_of_preservesFiniteColimits_preadditiveYonedaObj is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Abelian.{u1, u2} C _inst_1] (J : C) [hP : CategoryTheory.Limits.PreservesFiniteColimits.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (ModuleCat.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) J) (CategoryTheory.Preadditive.CategoryTheory.End.ring.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2) J)) (ModuleCat.moduleCategory.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) J) (CategoryTheory.Preadditive.CategoryTheory.End.ring.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2) J)) (CategoryTheory.preadditiveYonedaObj.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2) J)], CategoryTheory.Injective.{u1, u2} C _inst_1 J
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Abelian.{u1, u2} C _inst_1] (J : C) [hP : CategoryTheory.Limits.PreservesFiniteColimits.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (ModuleCat.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) J) (CategoryTheory.Preadditive.instRingEndToCategoryStruct.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2) J)) (ModuleCat.moduleCategory.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) J) (CategoryTheory.Preadditive.instRingEndToCategoryStruct.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2) J)) (CategoryTheory.preadditiveYonedaObj.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2) J)], CategoryTheory.Injective.{u1, u2} C _inst_1 J
Case conversion may be inaccurate. Consider using '#align category_theory.injective_of_preserves_finite_colimits_preadditive_yoneda_obj CategoryTheory.injective_of_preservesFiniteColimits_preadditiveYonedaObjₓ'. -/
/-- An object is injective if its preadditive Yoneda functor preserves finite colimits. -/
theorem injective_of_preservesFiniteColimits_preadditiveYonedaObj (J : C)
    [hP : PreservesFiniteColimits (preadditiveYonedaObj J)] : Injective J :=
  by
  rw [injective_iff_preserves_epimorphisms_preadditive_yoneda_obj']
  infer_instance
#align category_theory.injective_of_preserves_finite_colimits_preadditive_yoneda_obj CategoryTheory.injective_of_preservesFiniteColimits_preadditiveYonedaObj

end CategoryTheory

