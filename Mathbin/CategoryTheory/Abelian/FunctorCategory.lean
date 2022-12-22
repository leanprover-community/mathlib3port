/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.abelian.functor_category
! leanprover-community/mathlib commit 9116dd6709f303dcf781632e15fdef382b0fc579
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Abelian.Basic
import Mathbin.CategoryTheory.Preadditive.FunctorCategory
import Mathbin.CategoryTheory.Limits.Shapes.FunctorCategory
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# If `D` is abelian, then the functor category `C ⥤ D` is also abelian.

-/


noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

namespace Abelian

section

universe z w v u

variable {C : Type max v u} [Category.{v} C]

variable {D : Type w} [Category.{max z v u} D] [Abelian D]

namespace FunctorCategory

variable {F G : C ⥤ D} (α : F ⟶ G) (X : C)

/-- The abelian coimage in a functor category can be calculated componentwise. -/
@[simps]
def coimageObjIso : (Abelian.coimage α).obj X ≅ Abelian.coimage (α.app X) :=
  PreservesCokernel.iso ((evaluation C D).obj X) _ ≪≫
    cokernel.mapIso _ _ (PreservesKernel.iso ((evaluation C D).obj X) _) (Iso.refl _)
      (by 
        dsimp
        simp only [category.comp_id]
        exact (kernel_comparison_comp_ι _ ((evaluation C D).obj X)).symm)
#align
  category_theory.abelian.functor_category.coimage_obj_iso CategoryTheory.Abelian.FunctorCategory.coimageObjIso

/-- The abelian image in a functor category can be calculated componentwise. -/
@[simps]
def imageObjIso : (Abelian.image α).obj X ≅ Abelian.image (α.app X) :=
  PreservesKernel.iso ((evaluation C D).obj X) _ ≪≫
    kernel.mapIso _ _ (Iso.refl _) (PreservesCokernel.iso ((evaluation C D).obj X) _)
      (by 
        apply (cancel_mono (preserves_cokernel.iso ((evaluation C D).obj X) α).inv).1
        simp only [category.assoc, iso.hom_inv_id]
        dsimp
        simp only [category.id_comp, category.comp_id]
        exact (π_comp_cokernel_comparison _ ((evaluation C D).obj X)).symm)
#align
  category_theory.abelian.functor_category.image_obj_iso CategoryTheory.Abelian.FunctorCategory.imageObjIso

theorem coimage_image_comparison_app :
    coimageImageComparison (α.app X) =
      (coimage_obj_iso α X).inv ≫ (coimageImageComparison α).app X ≫ (image_obj_iso α X).Hom :=
  by 
  ext
  dsimp
  simp only [category.comp_id, category.id_comp, category.assoc, coimage_image_factorisation,
    limits.cokernel.π_desc_assoc, limits.kernel.lift_ι]
  simp only [← evaluation_obj_map C D X]
  erw [kernel_comparison_comp_ι _ ((evaluation C D).obj X)]
  erw [π_comp_cokernel_comparison_assoc _ ((evaluation C D).obj X)]
  simp only [← functor.map_comp]
  simp only [coimage_image_factorisation, evaluation_obj_map]
#align
  category_theory.abelian.functor_category.coimage_image_comparison_app CategoryTheory.Abelian.FunctorCategory.coimage_image_comparison_app

theorem coimage_image_comparison_app' :
    (coimageImageComparison α).app X =
      (coimage_obj_iso α X).Hom ≫ coimageImageComparison (α.app X) ≫ (image_obj_iso α X).inv :=
  by
  simp only [coimage_image_comparison_app, iso.hom_inv_id_assoc, iso.hom_inv_id, category.assoc,
    category.comp_id]
#align
  category_theory.abelian.functor_category.coimage_image_comparison_app' CategoryTheory.Abelian.FunctorCategory.coimage_image_comparison_app'

instance functor_category_is_iso_coimage_image_comparison :
    IsIso (Abelian.coimageImageComparison α) := by
  have : ∀ X : C, is_iso ((abelian.coimage_image_comparison α).app X) := by
    intros
    rw [coimage_image_comparison_app']
    infer_instance
  apply nat_iso.is_iso_of_is_iso_app
#align
  category_theory.abelian.functor_category.functor_category_is_iso_coimage_image_comparison CategoryTheory.Abelian.FunctorCategory.functor_category_is_iso_coimage_image_comparison

end FunctorCategory

noncomputable instance functorCategoryAbelian : Abelian (C ⥤ D) :=
  abelian.of_coimage_image_comparison_is_iso
#align
  category_theory.abelian.functor_category_abelian CategoryTheory.Abelian.functorCategoryAbelian

end

section

universe u

variable {C : Type u} [SmallCategory C]

variable {D : Type (u + 1)} [LargeCategory D] [Abelian D]

/-- A variant with specialized universes for a common case. -/
noncomputable instance functorCategoryAbelian' : Abelian (C ⥤ D) :=
  abelian.functor_category_abelian.{u, u + 1, u, u}
#align
  category_theory.abelian.functor_category_abelian' CategoryTheory.Abelian.functorCategoryAbelian'

end

end Abelian

end CategoryTheory

