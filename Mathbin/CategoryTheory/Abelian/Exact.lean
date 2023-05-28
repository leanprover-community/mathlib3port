/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Adam Topaz, Johan Commelin, Jakob von Raumer

! This file was ported from Lean 3 source module category_theory.abelian.exact
! leanprover-community/mathlib commit ef55335933293309ff8c0b1d20ffffeecbe5c39f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Abelian.Opposite
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathbin.CategoryTheory.Preadditive.LeftExact
import Mathbin.CategoryTheory.Adjunction.Limits
import Mathbin.Algebra.Homology.Exact
import Mathbin.Tactic.Tfae

/-!
# Exact sequences in abelian categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In an abelian category, we get several interesting results related to exactness which are not
true in more general settings.

## Main results
* `(f, g)` is exact if and only if `f ≫ g = 0` and `kernel.ι g ≫ cokernel.π f = 0`. This
  characterisation tends to be less cumbersome to work with than the original definition involving
  the comparison map `image f ⟶ kernel g`.
* If `(f, g)` is exact, then `image.ι f` has the universal property of the kernel of `g`.
* `f` is a monomorphism iff `kernel.ι f = 0` iff `exact 0 f`, and `f` is an epimorphism iff
  `cokernel.π = 0` iff `exact f 0`.
* A faithful functor between abelian categories that preserves zero morphisms reflects exact
  sequences.
* `X ⟶ Y ⟶ Z ⟶ 0` is exact if and only if the second map is a cokernel of the first, and
  `0 ⟶ X ⟶ Y ⟶ Z` is exact if and only if the first map is a kernel of the second.
* An exact functor preserves exactness, more specifically, `F` preserves finite colimits and
  finite limits, if and only if `exact f g` implies `exact (F.map f) (F.map g)`.
-/


universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Preadditive

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]

namespace CategoryTheory

namespace Abelian

variable {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

attribute [local instance] has_equalizers_of_has_kernels

#print CategoryTheory.Abelian.exact_iff_image_eq_kernel /-
/-- In an abelian category, a pair of morphisms `f : X ⟶ Y`, `g : Y ⟶ Z` is exact
iff `image_subobject f = kernel_subobject g`.
-/
theorem exact_iff_image_eq_kernel : Exact f g ↔ imageSubobject f = kernelSubobject g :=
  by
  constructor
  · intro h
    fapply subobject.eq_of_comm
    · suffices is_iso (imageToKernel _ _ h.w) by exact as_iso (imageToKernel _ _ h.w)
      exact is_iso_of_mono_of_epi _
    · simp
  · apply exact_of_image_eq_kernel
#align category_theory.abelian.exact_iff_image_eq_kernel CategoryTheory.Abelian.exact_iff_image_eq_kernel
-/

#print CategoryTheory.Abelian.exact_iff /-
theorem exact_iff : Exact f g ↔ f ≫ g = 0 ∧ kernel.ι g ≫ cokernel.π f = 0 :=
  by
  constructor
  · intro h
    exact ⟨h.1, kernel_comp_cokernel f g h⟩
  · refine' fun h => ⟨h.1, _⟩
    suffices hl :
      is_limit (kernel_fork.of_ι (image_subobject f).arrow (image_subobject_arrow_comp_eq_zero h.1))
    · have :
        imageToKernel f g h.1 =
          (is_limit.cone_point_unique_up_to_iso hl (limit.is_limit _)).Hom ≫
            (kernel_subobject_iso _).inv :=
        by
        ext
        simp
      rw [this]
      infer_instance
    refine' kernel_fork.is_limit.of_ι _ _ _ _ _
    · refine' fun W u hu =>
        kernel.lift (cokernel.π f) u _ ≫ (image_iso_image f).Hom ≫ (image_subobject_iso _).inv
      rw [← kernel.lift_ι g u hu, category.assoc, h.2, has_zero_morphisms.comp_zero]
    · tidy
    · intros
      rw [← cancel_mono (image_subobject f).arrow, w]
      simp
#align category_theory.abelian.exact_iff CategoryTheory.Abelian.exact_iff
-/

/- warning: category_theory.abelian.exact_iff' -> CategoryTheory.Abelian.exact_iff' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.abelian.exact_iff' CategoryTheory.Abelian.exact_iff'ₓ'. -/
theorem exact_iff' {cg : KernelFork g} (hg : IsLimit cg) {cf : CokernelCofork f}
    (hf : IsColimit cf) : Exact f g ↔ f ≫ g = 0 ∧ cg.ι ≫ cf.π = 0 :=
  by
  constructor
  · intro h
    exact ⟨h.1, fork_ι_comp_cofork_π f g h cg cf⟩
  · rw [exact_iff]
    refine' fun h => ⟨h.1, _⟩
    apply zero_of_epi_comp (is_limit.cone_point_unique_up_to_iso hg (limit.is_limit _)).Hom
    apply zero_of_comp_mono (is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit _) hf).Hom
    simp [h.2]
#align category_theory.abelian.exact_iff' CategoryTheory.Abelian.exact_iff'

#print CategoryTheory.Abelian.exact_tfae /-
theorem exact_tfae :
    TFAE
      [Exact f g, f ≫ g = 0 ∧ kernel.ι g ≫ cokernel.π f = 0,
        imageSubobject f = kernelSubobject g] :=
  by
  tfae_have 1 ↔ 2; · apply exact_iff
  tfae_have 1 ↔ 3; · apply exact_iff_image_eq_kernel
  tfae_finish
#align category_theory.abelian.exact_tfae CategoryTheory.Abelian.exact_tfae
-/

/- warning: category_theory.abelian.is_equivalence.exact_iff -> CategoryTheory.Abelian.IsEquivalence.exact_iff is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Abelian.{u1, u2} C _inst_1] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z) {D : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} D] [_inst_4 : CategoryTheory.Abelian.{u1, u2} D _inst_3] (F : CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 D _inst_3) [_inst_5 : CategoryTheory.IsEquivalence.{u1, u1, u2, u2} C _inst_1 D _inst_3 F], Iff (CategoryTheory.Exact.{u1, u2} D _inst_3 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} D _inst_3 (CategoryTheory.Abelian.CategoryTheory.Limits.hasStrongEpiMonoFactorisations.{u1, u2} D _inst_3 _inst_4)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} D _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u2} D _inst_3 _inst_4)) (CategoryTheory.Abelian.hasKernels.{u1, u2} D _inst_3 _inst_4) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 D _inst_3 F X) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 D _inst_3 F Y) (CategoryTheory.Functor.obj.{u1, u1, u2, u2} C _inst_1 D _inst_3 F Z) (CategoryTheory.Functor.map.{u1, u1, u2, u2} C _inst_1 D _inst_3 F X Y f) (CategoryTheory.Functor.map.{u1, u1, u2, u2} C _inst_1 D _inst_3 F Y Z g)) (CategoryTheory.Exact.{u1, u2} C _inst_1 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 (CategoryTheory.Abelian.CategoryTheory.Limits.hasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 _inst_2)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2)) (CategoryTheory.Abelian.hasKernels.{u1, u2} C _inst_1 _inst_2) X Y Z f g)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Abelian.{u1, u2} C _inst_1] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z) {D : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} D] [_inst_4 : CategoryTheory.Abelian.{u1, u2} D _inst_3] (F : CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 D _inst_3) [_inst_5 : CategoryTheory.IsEquivalence.{u1, u1, u2, u2} C _inst_1 D _inst_3 F], Iff (CategoryTheory.Exact.{u1, u2} D _inst_3 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} D _inst_3 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u2} D _inst_3 _inst_4)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} D _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u2} D _inst_3 _inst_4)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u2} D _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} D _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u2} D _inst_3 _inst_4)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} D _inst_3 _inst_4)) (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} D (CategoryTheory.Category.toCategoryStruct.{u1, u2} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 D _inst_3 F) X) (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} D (CategoryTheory.Category.toCategoryStruct.{u1, u2} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 D _inst_3 F) Y) (Prefunctor.obj.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} D (CategoryTheory.Category.toCategoryStruct.{u1, u2} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 D _inst_3 F) Z) (Prefunctor.map.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} D (CategoryTheory.Category.toCategoryStruct.{u1, u2} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 D _inst_3 F) X Y f) (Prefunctor.map.{succ u1, succ u1, u2, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} D (CategoryTheory.Category.toCategoryStruct.{u1, u2} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u2} C _inst_1 D _inst_3 F) Y Z g)) (CategoryTheory.Exact.{u1, u2} C _inst_1 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 _inst_2)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u2} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} C _inst_1 _inst_2)) X Y Z f g)
Case conversion may be inaccurate. Consider using '#align category_theory.abelian.is_equivalence.exact_iff CategoryTheory.Abelian.IsEquivalence.exact_iffₓ'. -/
theorem IsEquivalence.exact_iff {D : Type u₁} [Category.{v₁} D] [Abelian D] (F : C ⥤ D)
    [IsEquivalence F] : Exact (F.map f) (F.map g) ↔ Exact f g :=
  by
  simp only [exact_iff, ← F.map_eq_zero_iff, F.map_comp, category.assoc, ←
    kernel_comparison_comp_ι g F, ← π_comp_cokernel_comparison f F]
  rw [is_iso.comp_left_eq_zero (kernel_comparison g F), ← category.assoc,
    is_iso.comp_right_eq_zero _ (cokernel_comparison f F)]
#align category_theory.abelian.is_equivalence.exact_iff CategoryTheory.Abelian.IsEquivalence.exact_iff

#print CategoryTheory.Abelian.exact_epi_comp_iff /-
/-- The dual result is true even in non-abelian categories, see
    `category_theory.exact_comp_mono_iff`. -/
theorem exact_epi_comp_iff {W : C} (h : W ⟶ X) [Epi h] : Exact (h ≫ f) g ↔ Exact f g :=
  by
  refine' ⟨fun hfg => _, fun h => exact_epi_comp h⟩
  let hc :=
    is_cokernel_of_comp _ _ (colimit.is_colimit (parallel_pair (h ≫ f) 0))
      (by rw [← cancel_epi h, ← category.assoc, cokernel_cofork.condition, comp_zero]) rfl
  refine' (exact_iff' _ _ (limit.is_limit _) hc).2 ⟨_, ((exact_iff _ _).1 hfg).2⟩
  exact zero_of_epi_comp h (by rw [← hfg.1, category.assoc])
#align category_theory.abelian.exact_epi_comp_iff CategoryTheory.Abelian.exact_epi_comp_iff
-/

#print CategoryTheory.Abelian.isLimitImage /-
/-- If `(f, g)` is exact, then `abelian.image.ι f` is a kernel of `g`. -/
def isLimitImage (h : Exact f g) :
    IsLimit (KernelFork.ofι (Abelian.image.ι f) (image_ι_comp_eq_zero h.1) : KernelFork g) :=
  by
  rw [exact_iff] at h
  refine' kernel_fork.is_limit.of_ι _ _ _ _ _
  · refine' fun W u hu => kernel.lift (cokernel.π f) u _
    rw [← kernel.lift_ι g u hu, category.assoc, h.2, has_zero_morphisms.comp_zero]
  tidy
#align category_theory.abelian.is_limit_image CategoryTheory.Abelian.isLimitImage
-/

#print CategoryTheory.Abelian.isLimitImage' /-
/-- If `(f, g)` is exact, then `image.ι f` is a kernel of `g`. -/
def isLimitImage' (h : Exact f g) :
    IsLimit (KernelFork.ofι (Limits.image.ι f) (Limits.image_ι_comp_eq_zero h.1)) :=
  IsKernel.isoKernel _ _ (isLimitImage f g h) (imageIsoImage f).symm <| IsImage.lift_fac _ _
#align category_theory.abelian.is_limit_image' CategoryTheory.Abelian.isLimitImage'
-/

#print CategoryTheory.Abelian.isColimitCoimage /-
/-- If `(f, g)` is exact, then `coimages.coimage.π g` is a cokernel of `f`. -/
def isColimitCoimage (h : Exact f g) :
    IsColimit
      (CokernelCofork.ofπ (Abelian.coimage.π g) (Abelian.comp_coimage_π_eq_zero h.1) :
        CokernelCofork f) :=
  by
  rw [exact_iff] at h
  refine' cokernel_cofork.is_colimit.of_π _ _ _ _ _
  · refine' fun W u hu => cokernel.desc (kernel.ι g) u _
    rw [← cokernel.π_desc f u hu, ← category.assoc, h.2, has_zero_morphisms.zero_comp]
  tidy
#align category_theory.abelian.is_colimit_coimage CategoryTheory.Abelian.isColimitCoimage
-/

#print CategoryTheory.Abelian.isColimitImage /-
/-- If `(f, g)` is exact, then `factor_thru_image g` is a cokernel of `f`. -/
def isColimitImage (h : Exact f g) :
    IsColimit (CokernelCofork.ofπ (Limits.factorThruImage g) (comp_factorThruImage_eq_zero h.1)) :=
  IsCokernel.cokernelIso _ _ (isColimitCoimage f g h) (coimageIsoImage' g) <|
    (cancel_mono (Limits.image.ι g)).1 <| by simp
#align category_theory.abelian.is_colimit_image CategoryTheory.Abelian.isColimitImage
-/

#print CategoryTheory.Abelian.exact_cokernel /-
theorem exact_cokernel : Exact f (cokernel.π f) :=
  by
  rw [exact_iff]
  tidy
#align category_theory.abelian.exact_cokernel CategoryTheory.Abelian.exact_cokernel
-/

instance (h : Exact f g) : Mono (cokernel.desc f g h.w) :=
  suffices h :
    cokernel.desc f g h.w =
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (isColimitImage f g h)).Hom ≫
        Limits.image.ι g
    from by
    rw [h]
    apply mono_comp
  (cancel_epi (cokernel.π f)).1 <| by simp

/-- If `ex : exact f g` and `epi g`, then `cokernel.desc _ _ ex.w` is an isomorphism. -/
instance (ex : Exact f g) [Epi g] : IsIso (cokernel.desc f g ex.w) :=
  isIso_of_mono_of_epi (Limits.cokernel.desc f g ex.w)

#print CategoryTheory.Abelian.cokernel.desc.inv /-
@[simp, reassoc]
theorem cokernel.desc.inv [Epi g] (ex : Exact f g) :
    g ≫ inv (cokernel.desc _ _ ex.w) = cokernel.π _ := by simp
#align category_theory.abelian.cokernel.desc.inv CategoryTheory.Abelian.cokernel.desc.inv
-/

instance (ex : Exact f g) [Mono f] : IsIso (kernel.lift g f ex.w) :=
  isIso_of_mono_of_epi (Limits.kernel.lift g f ex.w)

#print CategoryTheory.Abelian.kernel.lift.inv /-
@[simp, reassoc]
theorem kernel.lift.inv [Mono f] (ex : Exact f g) : inv (kernel.lift _ _ ex.w) ≫ f = kernel.ι g :=
  by simp
#align category_theory.abelian.kernel.lift.inv CategoryTheory.Abelian.kernel.lift.inv
-/

#print CategoryTheory.Abelian.isColimitOfExactOfEpi /-
/-- If `X ⟶ Y ⟶ Z ⟶ 0` is exact, then the second map is a cokernel of the first. -/
def isColimitOfExactOfEpi [Epi g] (h : Exact f g) : IsColimit (CokernelCofork.ofπ _ h.w) :=
  IsColimit.ofIsoColimit (colimit.isColimit _) <|
    Cocones.ext
      ⟨cokernel.desc _ _ h.w, epiDesc g (cokernel.π f) ((exact_iff _ _).1 h).2,
        (cancel_epi (cokernel.π f)).1 (by tidy), (cancel_epi g).1 (by tidy)⟩
      fun j => by cases j <;> simp
#align category_theory.abelian.is_colimit_of_exact_of_epi CategoryTheory.Abelian.isColimitOfExactOfEpi
-/

#print CategoryTheory.Abelian.isLimitOfExactOfMono /-
/-- If `0 ⟶ X ⟶ Y ⟶ Z` is exact, then the first map is a kernel of the second. -/
def isLimitOfExactOfMono [Mono f] (h : Exact f g) : IsLimit (KernelFork.ofι _ h.w) :=
  IsLimit.ofIsoLimit (limit.isLimit _) <|
    Cones.ext
      ⟨monoLift f (kernel.ι g) ((exact_iff _ _).1 h).2, kernel.lift _ _ h.w,
        (cancel_mono (kernel.ι g)).1 (by tidy), (cancel_mono f).1 (by tidy)⟩
      fun j => by cases j <;> simp
#align category_theory.abelian.is_limit_of_exact_of_mono CategoryTheory.Abelian.isLimitOfExactOfMono
-/

#print CategoryTheory.Abelian.exact_of_is_cokernel /-
theorem exact_of_is_cokernel (w : f ≫ g = 0) (h : IsColimit (CokernelCofork.ofπ _ w)) : Exact f g :=
  by
  refine' (exact_iff _ _).2 ⟨w, _⟩
  have := h.fac (cokernel_cofork.of_π _ (cokernel.condition f)) walking_parallel_pair.one
  simp only [cofork.of_π_ι_app] at this
  rw [← this, ← category.assoc, kernel.condition, zero_comp]
#align category_theory.abelian.exact_of_is_cokernel CategoryTheory.Abelian.exact_of_is_cokernel
-/

#print CategoryTheory.Abelian.exact_of_is_kernel /-
theorem exact_of_is_kernel (w : f ≫ g = 0) (h : IsLimit (KernelFork.ofι _ w)) : Exact f g :=
  by
  refine' (exact_iff _ _).2 ⟨w, _⟩
  have := h.fac (kernel_fork.of_ι _ (kernel.condition g)) walking_parallel_pair.zero
  simp only [fork.of_ι_π_app] at this
  rw [← this, category.assoc, cokernel.condition, comp_zero]
#align category_theory.abelian.exact_of_is_kernel CategoryTheory.Abelian.exact_of_is_kernel
-/

#print CategoryTheory.Abelian.exact_iff_exact_image_ι /-
theorem exact_iff_exact_image_ι : Exact f g ↔ Exact (Abelian.image.ι f) g := by
  conv_lhs => rw [← abelian.image.fac f] <;> apply exact_epi_comp_iff
#align category_theory.abelian.exact_iff_exact_image_ι CategoryTheory.Abelian.exact_iff_exact_image_ι
-/

#print CategoryTheory.Abelian.exact_iff_exact_coimage_π /-
theorem exact_iff_exact_coimage_π : Exact f g ↔ Exact f (coimage.π g) := by
  conv_lhs => rw [← abelian.coimage.fac g] <;> apply exact_comp_mono_iff
#align category_theory.abelian.exact_iff_exact_coimage_π CategoryTheory.Abelian.exact_iff_exact_coimage_π
-/

section

variable (Z)

#print CategoryTheory.Abelian.tfae_mono /-
theorem tfae_mono : TFAE [Mono f, kernel.ι f = 0, Exact (0 : Z ⟶ X) f] :=
  by
  tfae_have 3 → 2
  · exact kernel_ι_eq_zero_of_exact_zero_left Z
  tfae_have 1 → 3
  · intros
    exact exact_zero_left_of_mono Z
  tfae_have 2 → 1
  · exact mono_of_kernel_ι_eq_zero _
  tfae_finish
#align category_theory.abelian.tfae_mono CategoryTheory.Abelian.tfae_mono
-/

#print CategoryTheory.Abelian.mono_iff_kernel_ι_eq_zero /-
-- Note we've already proved `mono_iff_exact_zero_left : mono f ↔ exact (0 : Z ⟶ X) f`
-- in any preadditive category with kernels and images.
theorem mono_iff_kernel_ι_eq_zero : Mono f ↔ kernel.ι f = 0 :=
  (tfae_mono X f).out 0 1
#align category_theory.abelian.mono_iff_kernel_ι_eq_zero CategoryTheory.Abelian.mono_iff_kernel_ι_eq_zero
-/

#print CategoryTheory.Abelian.tfae_epi /-
theorem tfae_epi : TFAE [Epi f, cokernel.π f = 0, Exact f (0 : Y ⟶ Z)] :=
  by
  tfae_have 3 → 2
  · rw [exact_iff]
    rintro ⟨-, h⟩
    exact zero_of_epi_comp _ h
  tfae_have 1 → 3
  · rw [exact_iff]
    intro
    exact ⟨by simp, by simp [cokernel.π_of_epi]⟩
  tfae_have 2 → 1
  · exact epi_of_cokernel_π_eq_zero _
  tfae_finish
#align category_theory.abelian.tfae_epi CategoryTheory.Abelian.tfae_epi
-/

#print CategoryTheory.Abelian.epi_iff_cokernel_π_eq_zero /-
-- Note we've already proved `epi_iff_exact_zero_right : epi f ↔ exact f (0 : Y ⟶ Z)`
-- in any preadditive category with equalizers and images.
theorem epi_iff_cokernel_π_eq_zero : Epi f ↔ cokernel.π f = 0 :=
  (tfae_epi X f).out 0 1
#align category_theory.abelian.epi_iff_cokernel_π_eq_zero CategoryTheory.Abelian.epi_iff_cokernel_π_eq_zero
-/

end

section Opposite

/- warning: category_theory.abelian.exact.op -> CategoryTheory.Abelian.Exact.op is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Abelian.{u1, u2} C _inst_1] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z), (CategoryTheory.Exact.{u1, u2} C _inst_1 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 (CategoryTheory.Abelian.CategoryTheory.Limits.hasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 _inst_2)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2)) (CategoryTheory.Abelian.hasKernels.{u1, u2} C _inst_1 _inst_2) X Y Z f g) -> (CategoryTheory.Exact.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Abelian.CategoryTheory.Limits.hasStrongEpiMonoFactorisations.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Opposite.abelian.{u2, u1} C _inst_1 _inst_2))) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u1, u2} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2))) (CategoryTheory.Abelian.hasKernels.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Opposite.abelian.{u2, u1} C _inst_1 _inst_2)) (Opposite.op.{succ u2} C Z) (Opposite.op.{succ u2} C Y) (Opposite.op.{succ u2} C X) (Quiver.Hom.op.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z g) (Quiver.Hom.op.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y f))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Abelian.{u1, u2} C _inst_1] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z), (CategoryTheory.Exact.{u1, u2} C _inst_1 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 _inst_2)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u2} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} C _inst_1 _inst_2)) X Y Z f g) -> (CategoryTheory.Exact.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.instAbelianOppositeOpposite.{u2, u1} C _inst_1 _inst_2))) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u1, u2} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2))) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u1, u2} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2))) (CategoryTheory.Limits.hasEqualizers_opposite.{u1, u2} C _inst_1 (CategoryTheory.Abelian.hasCoequalizers.{u1, u2} C _inst_1 _inst_2))) (Opposite.op.{succ u2} C Z) (Opposite.op.{succ u2} C Y) (Opposite.op.{succ u2} C X) (Quiver.Hom.op.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z g) (Quiver.Hom.op.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y f))
Case conversion may be inaccurate. Consider using '#align category_theory.abelian.exact.op CategoryTheory.Abelian.Exact.opₓ'. -/
theorem Exact.op (h : Exact f g) : Exact g.op f.op :=
  by
  rw [exact_iff]
  refine' ⟨by simp [← op_comp, h.w], Quiver.Hom.unop_inj _⟩
  simp only [unop_comp, cokernel.π_op, eq_to_hom_refl, kernel.ι_op, category.id_comp,
    category.assoc, kernel_comp_cokernel_assoc _ _ h, zero_comp, comp_zero, unop_zero]
#align category_theory.abelian.exact.op CategoryTheory.Abelian.Exact.op

/- warning: category_theory.abelian.exact.op_iff -> CategoryTheory.Abelian.Exact.op_iff is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Abelian.{u1, u2} C _inst_1] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z), Iff (CategoryTheory.Exact.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Abelian.CategoryTheory.Limits.hasStrongEpiMonoFactorisations.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Opposite.abelian.{u2, u1} C _inst_1 _inst_2))) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u1, u2} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2))) (CategoryTheory.Abelian.hasKernels.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Opposite.abelian.{u2, u1} C _inst_1 _inst_2)) (Opposite.op.{succ u2} C Z) (Opposite.op.{succ u2} C Y) (Opposite.op.{succ u2} C X) (Quiver.Hom.op.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z g) (Quiver.Hom.op.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y f)) (CategoryTheory.Exact.{u1, u2} C _inst_1 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 (CategoryTheory.Abelian.CategoryTheory.Limits.hasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 _inst_2)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2)) (CategoryTheory.Abelian.hasKernels.{u1, u2} C _inst_1 _inst_2) X Y Z f g)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Abelian.{u1, u2} C _inst_1] {X : C} {Y : C} {Z : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) (g : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z), Iff (CategoryTheory.Exact.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.instAbelianOppositeOpposite.{u2, u1} C _inst_1 _inst_2))) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u1, u2} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2))) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u1, u2} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2))) (CategoryTheory.Limits.hasEqualizers_opposite.{u1, u2} C _inst_1 (CategoryTheory.Abelian.hasCoequalizers.{u1, u2} C _inst_1 _inst_2))) (Opposite.op.{succ u2} C Z) (Opposite.op.{succ u2} C Y) (Opposite.op.{succ u2} C X) (Quiver.Hom.op.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z g) (Quiver.Hom.op.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y f)) (CategoryTheory.Exact.{u1, u2} C _inst_1 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 _inst_2)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u2} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} C _inst_1 _inst_2)) X Y Z f g)
Case conversion may be inaccurate. Consider using '#align category_theory.abelian.exact.op_iff CategoryTheory.Abelian.Exact.op_iffₓ'. -/
theorem Exact.op_iff : Exact g.op f.op ↔ Exact f g :=
  ⟨fun e => by
    rw [← is_equivalence.exact_iff _ _ (op_op_equivalence C).inverse]
    exact exact.op _ _ e, Exact.op _ _⟩
#align category_theory.abelian.exact.op_iff CategoryTheory.Abelian.Exact.op_iff

/- warning: category_theory.abelian.exact.unop -> CategoryTheory.Abelian.Exact.unop is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Abelian.{u1, u2} C _inst_1] {X : Opposite.{succ u2} C} {Y : Opposite.{succ u2} C} {Z : Opposite.{succ u2} C} (g : Quiver.Hom.{succ u1, u2} (Opposite.{succ u2} C) (Quiver.opposite.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1))) X Y) (f : Quiver.Hom.{succ u1, u2} (Opposite.{succ u2} C) (Quiver.opposite.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1))) Y Z), (CategoryTheory.Exact.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Abelian.CategoryTheory.Limits.hasStrongEpiMonoFactorisations.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Opposite.abelian.{u2, u1} C _inst_1 _inst_2))) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u1, u2} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2))) (CategoryTheory.Abelian.hasKernels.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Opposite.abelian.{u2, u1} C _inst_1 _inst_2)) X Y Z g f) -> (CategoryTheory.Exact.{u1, u2} C _inst_1 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 (CategoryTheory.Abelian.CategoryTheory.Limits.hasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 _inst_2)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2)) (CategoryTheory.Abelian.hasKernels.{u1, u2} C _inst_1 _inst_2) (Opposite.unop.{succ u2} C Z) (Opposite.unop.{succ u2} C Y) (Opposite.unop.{succ u2} C X) (Quiver.Hom.unop.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z f) (Quiver.Hom.unop.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y g))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Abelian.{u1, u2} C _inst_1] {X : Opposite.{succ u2} C} {Y : Opposite.{succ u2} C} {Z : Opposite.{succ u2} C} (g : Quiver.Hom.{succ u1, u2} (Opposite.{succ u2} C) (Quiver.opposite.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1))) X Y) (f : Quiver.Hom.{succ u1, u2} (Opposite.{succ u2} C) (Quiver.opposite.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1))) Y Z), (CategoryTheory.Exact.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.instAbelianOppositeOpposite.{u2, u1} C _inst_1 _inst_2))) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u1, u2} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2))) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u1, u2} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2))) (CategoryTheory.Limits.hasEqualizers_opposite.{u1, u2} C _inst_1 (CategoryTheory.Abelian.hasCoequalizers.{u1, u2} C _inst_1 _inst_2))) X Y Z g f) -> (CategoryTheory.Exact.{u1, u2} C _inst_1 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 _inst_2)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u2} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} C _inst_1 _inst_2)) (Opposite.unop.{succ u2} C Z) (Opposite.unop.{succ u2} C Y) (Opposite.unop.{succ u2} C X) (Quiver.Hom.unop.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z f) (Quiver.Hom.unop.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y g))
Case conversion may be inaccurate. Consider using '#align category_theory.abelian.exact.unop CategoryTheory.Abelian.Exact.unopₓ'. -/
theorem Exact.unop {X Y Z : Cᵒᵖ} (g : X ⟶ Y) (f : Y ⟶ Z) (h : Exact g f) : Exact f.unop g.unop :=
  by
  rw [← f.op_unop, ← g.op_unop] at h
  rwa [← exact.op_iff]
#align category_theory.abelian.exact.unop CategoryTheory.Abelian.Exact.unop

/- warning: category_theory.abelian.exact.unop_iff -> CategoryTheory.Abelian.Exact.unop_iff is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Abelian.{u1, u2} C _inst_1] {X : Opposite.{succ u2} C} {Y : Opposite.{succ u2} C} {Z : Opposite.{succ u2} C} (g : Quiver.Hom.{succ u1, u2} (Opposite.{succ u2} C) (Quiver.opposite.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1))) X Y) (f : Quiver.Hom.{succ u1, u2} (Opposite.{succ u2} C) (Quiver.opposite.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1))) Y Z), Iff (CategoryTheory.Exact.{u1, u2} C _inst_1 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 (CategoryTheory.Abelian.CategoryTheory.Limits.hasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 _inst_2)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2)) (CategoryTheory.Abelian.hasKernels.{u1, u2} C _inst_1 _inst_2) (Opposite.unop.{succ u2} C Z) (Opposite.unop.{succ u2} C Y) (Opposite.unop.{succ u2} C X) (Quiver.Hom.unop.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z f) (Quiver.Hom.unop.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y g)) (CategoryTheory.Exact.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Abelian.CategoryTheory.Limits.hasStrongEpiMonoFactorisations.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Opposite.abelian.{u2, u1} C _inst_1 _inst_2))) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u1, u2} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2))) (CategoryTheory.Abelian.hasKernels.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Opposite.abelian.{u2, u1} C _inst_1 _inst_2)) X Y Z g f)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Abelian.{u1, u2} C _inst_1] {X : Opposite.{succ u2} C} {Y : Opposite.{succ u2} C} {Z : Opposite.{succ u2} C} (g : Quiver.Hom.{succ u1, u2} (Opposite.{succ u2} C) (Quiver.opposite.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1))) X Y) (f : Quiver.Hom.{succ u1, u2} (Opposite.{succ u2} C) (Quiver.opposite.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1))) Y Z), Iff (CategoryTheory.Exact.{u1, u2} C _inst_1 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u2} C _inst_1 _inst_2)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u2} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2)) (CategoryTheory.Abelian.hasEqualizers.{u1, u2} C _inst_1 _inst_2)) (Opposite.unop.{succ u2} C Z) (Opposite.unop.{succ u2} C Y) (Opposite.unop.{succ u2} C X) (Quiver.Hom.unop.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Y Z f) (Quiver.Hom.unop.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y g)) (CategoryTheory.Exact.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.instAbelianOppositeOpposite.{u2, u1} C _inst_1 _inst_2))) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u1, u2} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2))) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Limits.hasZeroMorphismsOpposite.{u1, u2} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} C _inst_1 (CategoryTheory.Abelian.toPreadditive.{u1, u2} C _inst_1 _inst_2))) (CategoryTheory.Limits.hasEqualizers_opposite.{u1, u2} C _inst_1 (CategoryTheory.Abelian.hasCoequalizers.{u1, u2} C _inst_1 _inst_2))) X Y Z g f)
Case conversion may be inaccurate. Consider using '#align category_theory.abelian.exact.unop_iff CategoryTheory.Abelian.Exact.unop_iffₓ'. -/
theorem Exact.unop_iff {X Y Z : Cᵒᵖ} (g : X ⟶ Y) (f : Y ⟶ Z) : Exact f.unop g.unop ↔ Exact g f :=
  ⟨fun e => by rwa [← f.op_unop, ← g.op_unop, ← exact.op_iff] at e, fun e => @Exact.unop _ _ g f e⟩
#align category_theory.abelian.exact.unop_iff CategoryTheory.Abelian.Exact.unop_iff

end Opposite

end Abelian

namespace Functor

section

variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

variable (F : C ⥤ D) [PreservesZeroMorphisms F]

#print CategoryTheory.Functor.reflectsExactSequencesOfPreservesZeroMorphismsOfFaithful /-
instance (priority := 100) reflectsExactSequencesOfPreservesZeroMorphismsOfFaithful [Faithful F] :
    ReflectsExactSequences F
    where reflects X Y Z f g hfg :=
    by
    rw [abelian.exact_iff, ← F.map_comp, F.map_eq_zero_iff] at hfg
    refine' (abelian.exact_iff _ _).2 ⟨hfg.1, F.zero_of_map_zero _ _⟩
    obtain ⟨k, hk⟩ :=
      kernel.lift' (F.map g) (F.map (kernel.ι g))
        (by simp only [← F.map_comp, kernel.condition, CategoryTheory.Functor.map_zero])
    obtain ⟨l, hl⟩ :=
      cokernel.desc' (F.map f) (F.map (cokernel.π f))
        (by simp only [← F.map_comp, cokernel.condition, CategoryTheory.Functor.map_zero])
    rw [F.map_comp, ← hk, ← hl, category.assoc, reassoc_of hfg.2, zero_comp, comp_zero]
#align category_theory.functor.reflects_exact_sequences_of_preserves_zero_morphisms_of_faithful CategoryTheory.Functor.reflectsExactSequencesOfPreservesZeroMorphismsOfFaithful
-/

end

end Functor

namespace Functor

open Limits Abelian

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]

variable [Abelian A] [Abelian B]

variable (L : A ⥤ B)

section

variable [PreservesFiniteLimits L] [PreservesFiniteColimits L]

/- warning: category_theory.functor.map_exact -> CategoryTheory.Functor.map_exact is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u3}} {B : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u1, u3} A] [_inst_4 : CategoryTheory.Category.{u2, u4} B] [_inst_5 : CategoryTheory.Abelian.{u1, u3} A _inst_3] [_inst_6 : CategoryTheory.Abelian.{u2, u4} B _inst_4] (L : CategoryTheory.Functor.{u1, u2, u3, u4} A _inst_3 B _inst_4) [_inst_7 : CategoryTheory.Limits.PreservesFiniteLimits.{u1, u2, u3, u4} A _inst_3 B _inst_4 L] [_inst_8 : CategoryTheory.Limits.PreservesFiniteColimits.{u1, u2, u3, u4} A _inst_3 B _inst_4 L] {X : A} {Y : A} {Z : A} (f : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) X Y) (g : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) Y Z), (CategoryTheory.Exact.{u1, u3} A _inst_3 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u3} A _inst_3 (CategoryTheory.Abelian.CategoryTheory.Limits.hasStrongEpiMonoFactorisations.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u3} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Abelian.hasKernels.{u1, u3} A _inst_3 _inst_5) X Y Z f g) -> (CategoryTheory.Exact.{u2, u4} B _inst_4 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u2, u4} B _inst_4 (CategoryTheory.Abelian.CategoryTheory.Limits.hasStrongEpiMonoFactorisations.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u4} B _inst_4 (CategoryTheory.Abelian.toPreadditive.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Abelian.hasKernels.{u2, u4} B _inst_4 _inst_6) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} A _inst_3 B _inst_4 L X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} A _inst_3 B _inst_4 L Y) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} A _inst_3 B _inst_4 L Z) (CategoryTheory.Functor.map.{u1, u2, u3, u4} A _inst_3 B _inst_4 L X Y f) (CategoryTheory.Functor.map.{u1, u2, u3, u4} A _inst_3 B _inst_4 L Y Z g))
but is expected to have type
  forall {A : Type.{u3}} {B : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u1, u3} A] [_inst_4 : CategoryTheory.Category.{u2, u4} B] [_inst_5 : CategoryTheory.Abelian.{u1, u3} A _inst_3] [_inst_6 : CategoryTheory.Abelian.{u2, u4} B _inst_4] (L : CategoryTheory.Functor.{u1, u2, u3, u4} A _inst_3 B _inst_4) [_inst_7 : CategoryTheory.Limits.PreservesFiniteLimits.{u1, u2, u3, u4} A _inst_3 B _inst_4 L] [_inst_8 : CategoryTheory.Limits.PreservesFiniteColimits.{u1, u2, u3, u4} A _inst_3 B _inst_4 L] {X : A} {Y : A} {Z : A} (f : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) X Y) (g : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) Y Z), (CategoryTheory.Exact.{u1, u3} A _inst_3 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u3} A _inst_3 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u3} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u3} A _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u3} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Abelian.hasEqualizers.{u1, u3} A _inst_3 _inst_5)) X Y Z f g) -> (CategoryTheory.Exact.{u2, u4} B _inst_4 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u2, u4} B _inst_4 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u4} B _inst_4 (CategoryTheory.Abelian.toPreadditive.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u2, u4} B _inst_4 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u4} B _inst_4 (CategoryTheory.Abelian.toPreadditive.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Abelian.hasEqualizers.{u2, u4} B _inst_4 _inst_6)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) Y) (Prefunctor.obj.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) Z) (Prefunctor.map.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) X Y f) (Prefunctor.map.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) Y Z g))
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_exact CategoryTheory.Functor.map_exactₓ'. -/
/-- A functor preserving finite limits and finite colimits preserves exactness. The converse
result is also true, see `functor.preserves_finite_limits_of_map_exact` and
`functor.preserves_finite_colimits_of_map_exact`. -/
theorem map_exact {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) (e1 : Exact f g) :
    Exact (L.map f) (L.map g) :=
  by
  let hcoker := is_colimit_of_has_cokernel_of_preserves_colimit L f
  let hker := is_limit_of_has_kernel_of_preserves_limit L g
  refine' (exact_iff' _ _ hker hcoker).2 ⟨by simp [← L.map_comp, e1.1], _⟩
  rw [fork.ι_of_ι, cofork.π_of_π, ← L.map_comp, kernel_comp_cokernel _ _ e1, L.map_zero]
#align category_theory.functor.map_exact CategoryTheory.Functor.map_exact

end

section

variable (h : ∀ ⦃X Y Z : A⦄ {f : X ⟶ Y} {g : Y ⟶ Z}, Exact f g → Exact (L.map f) (L.map g))

include h

open ZeroObject

/- warning: category_theory.functor.preserves_zero_morphisms_of_map_exact -> CategoryTheory.Functor.preservesZeroMorphisms_of_map_exact is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u3}} {B : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u1, u3} A] [_inst_4 : CategoryTheory.Category.{u2, u4} B] [_inst_5 : CategoryTheory.Abelian.{u1, u3} A _inst_3] [_inst_6 : CategoryTheory.Abelian.{u2, u4} B _inst_4] (L : CategoryTheory.Functor.{u1, u2, u3, u4} A _inst_3 B _inst_4), (forall {{X : A}} {{Y : A}} {{Z : A}} {f : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) X Y} {g : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) Y Z}, (CategoryTheory.Exact.{u1, u3} A _inst_3 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u3} A _inst_3 (CategoryTheory.Abelian.CategoryTheory.Limits.hasStrongEpiMonoFactorisations.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u3} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Abelian.hasKernels.{u1, u3} A _inst_3 _inst_5) X Y Z f g) -> (CategoryTheory.Exact.{u2, u4} B _inst_4 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u2, u4} B _inst_4 (CategoryTheory.Abelian.CategoryTheory.Limits.hasStrongEpiMonoFactorisations.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u4} B _inst_4 (CategoryTheory.Abelian.toPreadditive.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Abelian.hasKernels.{u2, u4} B _inst_4 _inst_6) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} A _inst_3 B _inst_4 L X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} A _inst_3 B _inst_4 L Y) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} A _inst_3 B _inst_4 L Z) (CategoryTheory.Functor.map.{u1, u2, u3, u4} A _inst_3 B _inst_4 L X Y f) (CategoryTheory.Functor.map.{u1, u2, u3, u4} A _inst_3 B _inst_4 L Y Z g))) -> (CategoryTheory.Functor.PreservesZeroMorphisms.{u1, u2, u3, u4} A _inst_3 B _inst_4 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u3} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u4} B _inst_4 (CategoryTheory.Abelian.toPreadditive.{u2, u4} B _inst_4 _inst_6)) L)
but is expected to have type
  forall {A : Type.{u3}} {B : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u1, u3} A] [_inst_4 : CategoryTheory.Category.{u2, u4} B] [_inst_5 : CategoryTheory.Abelian.{u1, u3} A _inst_3] [_inst_6 : CategoryTheory.Abelian.{u2, u4} B _inst_4] (L : CategoryTheory.Functor.{u1, u2, u3, u4} A _inst_3 B _inst_4), (forall {{X : A}} {{Y : A}} {{Z : A}} {f : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) X Y} {g : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) Y Z}, (CategoryTheory.Exact.{u1, u3} A _inst_3 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u3} A _inst_3 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u3} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u3} A _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u3} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Abelian.hasEqualizers.{u1, u3} A _inst_3 _inst_5)) X Y Z f g) -> (CategoryTheory.Exact.{u2, u4} B _inst_4 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u2, u4} B _inst_4 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u4} B _inst_4 (CategoryTheory.Abelian.toPreadditive.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u2, u4} B _inst_4 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u4} B _inst_4 (CategoryTheory.Abelian.toPreadditive.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Abelian.hasEqualizers.{u2, u4} B _inst_4 _inst_6)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) Y) (Prefunctor.obj.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) Z) (Prefunctor.map.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) X Y f) (Prefunctor.map.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) Y Z g))) -> (CategoryTheory.Functor.PreservesZeroMorphisms.{u1, u2, u3, u4} A _inst_3 B _inst_4 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u3} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u4} B _inst_4 (CategoryTheory.Abelian.toPreadditive.{u2, u4} B _inst_4 _inst_6)) L)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.preserves_zero_morphisms_of_map_exact CategoryTheory.Functor.preservesZeroMorphisms_of_map_exactₓ'. -/
/-- A functor which preserves exactness preserves zero morphisms. -/
theorem preservesZeroMorphisms_of_map_exact : L.PreservesZeroMorphisms :=
  by
  replace h := (h (exact_of_zero (𝟙 0) (𝟙 0))).w
  rw [L.map_id, category.comp_id] at h
  exact preserves_zero_morphisms_of_map_zero_object (id_zero_equiv_iso_zero _ h)
#align category_theory.functor.preserves_zero_morphisms_of_map_exact CategoryTheory.Functor.preservesZeroMorphisms_of_map_exact

/- warning: category_theory.functor.preserves_monomorphisms_of_map_exact -> CategoryTheory.Functor.preservesMonomorphisms_of_map_exact is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u3}} {B : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u1, u3} A] [_inst_4 : CategoryTheory.Category.{u2, u4} B] [_inst_5 : CategoryTheory.Abelian.{u1, u3} A _inst_3] [_inst_6 : CategoryTheory.Abelian.{u2, u4} B _inst_4] (L : CategoryTheory.Functor.{u1, u2, u3, u4} A _inst_3 B _inst_4), (forall {{X : A}} {{Y : A}} {{Z : A}} {f : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) X Y} {g : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) Y Z}, (CategoryTheory.Exact.{u1, u3} A _inst_3 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u3} A _inst_3 (CategoryTheory.Abelian.CategoryTheory.Limits.hasStrongEpiMonoFactorisations.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u3} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Abelian.hasKernels.{u1, u3} A _inst_3 _inst_5) X Y Z f g) -> (CategoryTheory.Exact.{u2, u4} B _inst_4 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u2, u4} B _inst_4 (CategoryTheory.Abelian.CategoryTheory.Limits.hasStrongEpiMonoFactorisations.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u4} B _inst_4 (CategoryTheory.Abelian.toPreadditive.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Abelian.hasKernels.{u2, u4} B _inst_4 _inst_6) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} A _inst_3 B _inst_4 L X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} A _inst_3 B _inst_4 L Y) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} A _inst_3 B _inst_4 L Z) (CategoryTheory.Functor.map.{u1, u2, u3, u4} A _inst_3 B _inst_4 L X Y f) (CategoryTheory.Functor.map.{u1, u2, u3, u4} A _inst_3 B _inst_4 L Y Z g))) -> (CategoryTheory.Functor.PreservesMonomorphisms.{u1, u2, u3, u4} A _inst_3 B _inst_4 L)
but is expected to have type
  forall {A : Type.{u3}} {B : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u1, u3} A] [_inst_4 : CategoryTheory.Category.{u2, u4} B] [_inst_5 : CategoryTheory.Abelian.{u1, u3} A _inst_3] [_inst_6 : CategoryTheory.Abelian.{u2, u4} B _inst_4] (L : CategoryTheory.Functor.{u1, u2, u3, u4} A _inst_3 B _inst_4), (forall {{X : A}} {{Y : A}} {{Z : A}} {f : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) X Y} {g : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) Y Z}, (CategoryTheory.Exact.{u1, u3} A _inst_3 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u3} A _inst_3 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u3} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u3} A _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u3} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Abelian.hasEqualizers.{u1, u3} A _inst_3 _inst_5)) X Y Z f g) -> (CategoryTheory.Exact.{u2, u4} B _inst_4 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u2, u4} B _inst_4 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u4} B _inst_4 (CategoryTheory.Abelian.toPreadditive.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u2, u4} B _inst_4 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u4} B _inst_4 (CategoryTheory.Abelian.toPreadditive.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Abelian.hasEqualizers.{u2, u4} B _inst_4 _inst_6)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) Y) (Prefunctor.obj.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) Z) (Prefunctor.map.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) X Y f) (Prefunctor.map.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) Y Z g))) -> (CategoryTheory.Functor.PreservesMonomorphisms.{u1, u2, u3, u4} A _inst_3 B _inst_4 L)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.preserves_monomorphisms_of_map_exact CategoryTheory.Functor.preservesMonomorphisms_of_map_exactₓ'. -/
/-- A functor which preserves exactness preserves monomorphisms. -/
theorem preservesMonomorphisms_of_map_exact : L.PreservesMonomorphisms :=
  {
    preserves := fun X Y f hf =>
      by
      letI := preserves_zero_morphisms_of_map_exact L h
      apply ((tfae_mono (L.obj 0) (L.map f)).out 2 0).mp
      rw [← L.map_zero]
      exact h (((tfae_mono 0 f).out 0 2).mp hf) }
#align category_theory.functor.preserves_monomorphisms_of_map_exact CategoryTheory.Functor.preservesMonomorphisms_of_map_exact

/- warning: category_theory.functor.preserves_epimorphisms_of_map_exact -> CategoryTheory.Functor.preservesEpimorphisms_of_map_exact is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u3}} {B : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u1, u3} A] [_inst_4 : CategoryTheory.Category.{u2, u4} B] [_inst_5 : CategoryTheory.Abelian.{u1, u3} A _inst_3] [_inst_6 : CategoryTheory.Abelian.{u2, u4} B _inst_4] (L : CategoryTheory.Functor.{u1, u2, u3, u4} A _inst_3 B _inst_4), (forall {{X : A}} {{Y : A}} {{Z : A}} {f : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) X Y} {g : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) Y Z}, (CategoryTheory.Exact.{u1, u3} A _inst_3 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u3} A _inst_3 (CategoryTheory.Abelian.CategoryTheory.Limits.hasStrongEpiMonoFactorisations.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u3} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Abelian.hasKernels.{u1, u3} A _inst_3 _inst_5) X Y Z f g) -> (CategoryTheory.Exact.{u2, u4} B _inst_4 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u2, u4} B _inst_4 (CategoryTheory.Abelian.CategoryTheory.Limits.hasStrongEpiMonoFactorisations.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u4} B _inst_4 (CategoryTheory.Abelian.toPreadditive.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Abelian.hasKernels.{u2, u4} B _inst_4 _inst_6) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} A _inst_3 B _inst_4 L X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} A _inst_3 B _inst_4 L Y) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} A _inst_3 B _inst_4 L Z) (CategoryTheory.Functor.map.{u1, u2, u3, u4} A _inst_3 B _inst_4 L X Y f) (CategoryTheory.Functor.map.{u1, u2, u3, u4} A _inst_3 B _inst_4 L Y Z g))) -> (CategoryTheory.Functor.PreservesEpimorphisms.{u1, u2, u3, u4} A _inst_3 B _inst_4 L)
but is expected to have type
  forall {A : Type.{u3}} {B : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u1, u3} A] [_inst_4 : CategoryTheory.Category.{u2, u4} B] [_inst_5 : CategoryTheory.Abelian.{u1, u3} A _inst_3] [_inst_6 : CategoryTheory.Abelian.{u2, u4} B _inst_4] (L : CategoryTheory.Functor.{u1, u2, u3, u4} A _inst_3 B _inst_4), (forall {{X : A}} {{Y : A}} {{Z : A}} {f : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) X Y} {g : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) Y Z}, (CategoryTheory.Exact.{u1, u3} A _inst_3 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u3} A _inst_3 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u3} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u3} A _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u3} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Abelian.hasEqualizers.{u1, u3} A _inst_3 _inst_5)) X Y Z f g) -> (CategoryTheory.Exact.{u2, u4} B _inst_4 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u2, u4} B _inst_4 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u4} B _inst_4 (CategoryTheory.Abelian.toPreadditive.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u2, u4} B _inst_4 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u4} B _inst_4 (CategoryTheory.Abelian.toPreadditive.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Abelian.hasEqualizers.{u2, u4} B _inst_4 _inst_6)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) Y) (Prefunctor.obj.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) Z) (Prefunctor.map.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) X Y f) (Prefunctor.map.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) Y Z g))) -> (CategoryTheory.Functor.PreservesEpimorphisms.{u1, u2, u3, u4} A _inst_3 B _inst_4 L)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.preserves_epimorphisms_of_map_exact CategoryTheory.Functor.preservesEpimorphisms_of_map_exactₓ'. -/
/-- A functor which preserves exactness preserves epimorphisms. -/
theorem preservesEpimorphisms_of_map_exact : L.PreservesEpimorphisms :=
  {
    preserves := fun X Y f hf =>
      by
      letI := preserves_zero_morphisms_of_map_exact L h
      apply ((tfae_epi (L.obj 0) (L.map f)).out 2 0).mp
      rw [← L.map_zero]
      exact h (((tfae_epi 0 f).out 0 2).mp hf) }
#align category_theory.functor.preserves_epimorphisms_of_map_exact CategoryTheory.Functor.preservesEpimorphisms_of_map_exact

/- warning: category_theory.functor.preserves_kernels_of_map_exact -> CategoryTheory.Functor.preservesKernelsOfMapExact is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u3}} {B : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u1, u3} A] [_inst_4 : CategoryTheory.Category.{u2, u4} B] [_inst_5 : CategoryTheory.Abelian.{u1, u3} A _inst_3] [_inst_6 : CategoryTheory.Abelian.{u2, u4} B _inst_4] (L : CategoryTheory.Functor.{u1, u2, u3, u4} A _inst_3 B _inst_4), (forall {{X : A}} {{Y : A}} {{Z : A}} {f : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) X Y} {g : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) Y Z}, (CategoryTheory.Exact.{u1, u3} A _inst_3 (CategoryTheory.Functor.preservesKernelsOfMapExact._proof_1.{u3, u1} A _inst_3 _inst_5) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u3} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Abelian.hasKernels.{u1, u3} A _inst_3 _inst_5) X Y Z f g) -> (CategoryTheory.Exact.{u2, u4} B _inst_4 (CategoryTheory.Functor.preservesKernelsOfMapExact._proof_2.{u4, u2} B _inst_4 _inst_6) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u4} B _inst_4 (CategoryTheory.Abelian.toPreadditive.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Abelian.hasKernels.{u2, u4} B _inst_4 _inst_6) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} A _inst_3 B _inst_4 L X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} A _inst_3 B _inst_4 L Y) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} A _inst_3 B _inst_4 L Z) (CategoryTheory.Functor.map.{u1, u2, u3, u4} A _inst_3 B _inst_4 L X Y f) (CategoryTheory.Functor.map.{u1, u2, u3, u4} A _inst_3 B _inst_4 L Y Z g))) -> (forall (X : A) (Y : A) (f : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) X Y), CategoryTheory.Limits.PreservesLimit.{0, 0, u1, u2, u3, u4} A _inst_3 B _inst_4 CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory (CategoryTheory.Limits.parallelPair.{u1, u3} A _inst_3 X Y f (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) X Y) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) X Y) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) X Y) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u3} A _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u3} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u3} A _inst_3 _inst_5)) X Y))))) L)
but is expected to have type
  forall {A : Type.{u3}} {B : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u1, u3} A] [_inst_4 : CategoryTheory.Category.{u2, u4} B] [_inst_5 : CategoryTheory.Abelian.{u1, u3} A _inst_3] [_inst_6 : CategoryTheory.Abelian.{u2, u4} B _inst_4] (L : CategoryTheory.Functor.{u1, u2, u3, u4} A _inst_3 B _inst_4), (forall {{X : A}} {{Y : A}} {{Z : A}} {f : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) X Y} {g : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) Y Z}, (CategoryTheory.Exact.{u1, u3} A _inst_3 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u3} A _inst_3 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u3} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u3} A _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u3} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Abelian.hasEqualizers.{u1, u3} A _inst_3 _inst_5)) X Y Z f g) -> (CategoryTheory.Exact.{u2, u4} B _inst_4 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u2, u4} B _inst_4 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u4} B _inst_4 (CategoryTheory.Abelian.toPreadditive.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u2, u4} B _inst_4 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u4} B _inst_4 (CategoryTheory.Abelian.toPreadditive.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Abelian.hasEqualizers.{u2, u4} B _inst_4 _inst_6)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) Y) (Prefunctor.obj.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) Z) (Prefunctor.map.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) X Y f) (Prefunctor.map.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) Y Z g))) -> (forall (X : A) (Y : A) (f : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) X Y), CategoryTheory.Limits.PreservesLimit.{0, 0, u1, u2, u3, u4} A _inst_3 B _inst_4 CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory (CategoryTheory.Limits.parallelPair.{u1, u3} A _inst_3 X Y f (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) X Y) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) X Y) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u3} A _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u3} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u3} A _inst_3 _inst_5)) X Y)))) L)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.preserves_kernels_of_map_exact CategoryTheory.Functor.preservesKernelsOfMapExactₓ'. -/
/-- A functor which preserves exactness preserves kernels. -/
def preservesKernelsOfMapExact (X Y : A) (f : X ⟶ Y) : PreservesLimit (parallelPair f 0) L
    where preserves c ic :=
    by
    letI := preserves_zero_morphisms_of_map_exact L h
    letI := preserves_monomorphisms_of_map_exact L h
    letI := mono_of_is_limit_fork ic
    have hf :=
      (is_limit_map_cone_fork_equiv' L (kernel_fork.condition c)).symm
        (is_limit_of_exact_of_mono (L.map (fork.ι c)) (L.map f)
          (h
            (exact_of_is_kernel (fork.ι c) f (kernel_fork.condition c)
              (ic.of_iso_limit (iso_of_ι _)))))
    exact hf.of_iso_limit ((cones.functoriality _ L).mapIso (iso_of_ι _).symm)
#align category_theory.functor.preserves_kernels_of_map_exact CategoryTheory.Functor.preservesKernelsOfMapExact

/- warning: category_theory.functor.preserves_cokernels_of_map_exact -> CategoryTheory.Functor.preservesCokernelsOfMapExact is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u3}} {B : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u1, u3} A] [_inst_4 : CategoryTheory.Category.{u2, u4} B] [_inst_5 : CategoryTheory.Abelian.{u1, u3} A _inst_3] [_inst_6 : CategoryTheory.Abelian.{u2, u4} B _inst_4] (L : CategoryTheory.Functor.{u1, u2, u3, u4} A _inst_3 B _inst_4), (forall {{X : A}} {{Y : A}} {{Z : A}} {f : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) X Y} {g : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) Y Z}, (CategoryTheory.Exact.{u1, u3} A _inst_3 (CategoryTheory.Functor.preservesCokernelsOfMapExact._proof_1.{u3, u1} A _inst_3 _inst_5) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u3} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Abelian.hasKernels.{u1, u3} A _inst_3 _inst_5) X Y Z f g) -> (CategoryTheory.Exact.{u2, u4} B _inst_4 (CategoryTheory.Functor.preservesCokernelsOfMapExact._proof_2.{u4, u2} B _inst_4 _inst_6) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u4} B _inst_4 (CategoryTheory.Abelian.toPreadditive.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Abelian.hasKernels.{u2, u4} B _inst_4 _inst_6) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} A _inst_3 B _inst_4 L X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} A _inst_3 B _inst_4 L Y) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} A _inst_3 B _inst_4 L Z) (CategoryTheory.Functor.map.{u1, u2, u3, u4} A _inst_3 B _inst_4 L X Y f) (CategoryTheory.Functor.map.{u1, u2, u3, u4} A _inst_3 B _inst_4 L Y Z g))) -> (forall (X : A) (Y : A) (f : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) X Y), CategoryTheory.Limits.PreservesColimit.{0, 0, u1, u2, u3, u4} A _inst_3 B _inst_4 CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory (CategoryTheory.Limits.parallelPair.{u1, u3} A _inst_3 X Y f (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) X Y) 0 (OfNat.mk.{u1} (Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) X Y) 0 (Zero.zero.{u1} (Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) X Y) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u1, u3} A _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u3} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u3} A _inst_3 _inst_5)) X Y))))) L)
but is expected to have type
  forall {A : Type.{u3}} {B : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u1, u3} A] [_inst_4 : CategoryTheory.Category.{u2, u4} B] [_inst_5 : CategoryTheory.Abelian.{u1, u3} A _inst_3] [_inst_6 : CategoryTheory.Abelian.{u2, u4} B _inst_4] (L : CategoryTheory.Functor.{u1, u2, u3, u4} A _inst_3 B _inst_4), (forall {{X : A}} {{Y : A}} {{Z : A}} {f : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) X Y} {g : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) Y Z}, (CategoryTheory.Exact.{u1, u3} A _inst_3 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u3} A _inst_3 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u3} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u3} A _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u3} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Abelian.hasEqualizers.{u1, u3} A _inst_3 _inst_5)) X Y Z f g) -> (CategoryTheory.Exact.{u2, u4} B _inst_4 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u2, u4} B _inst_4 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u4} B _inst_4 (CategoryTheory.Abelian.toPreadditive.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u2, u4} B _inst_4 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u4} B _inst_4 (CategoryTheory.Abelian.toPreadditive.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Abelian.hasEqualizers.{u2, u4} B _inst_4 _inst_6)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) Y) (Prefunctor.obj.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) Z) (Prefunctor.map.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) X Y f) (Prefunctor.map.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) Y Z g))) -> (forall (X : A) (Y : A) (f : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) X Y), CategoryTheory.Limits.PreservesColimit.{0, 0, u1, u2, u3, u4} A _inst_3 B _inst_4 CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory (CategoryTheory.Limits.parallelPair.{u1, u3} A _inst_3 X Y f (OfNat.ofNat.{u1} (Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) X Y) 0 (Zero.toOfNat0.{u1} (Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) X Y) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u1, u3} A _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u3} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u3} A _inst_3 _inst_5)) X Y)))) L)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.preserves_cokernels_of_map_exact CategoryTheory.Functor.preservesCokernelsOfMapExactₓ'. -/
/-- A functor which preserves exactness preserves zero cokernels. -/
def preservesCokernelsOfMapExact (X Y : A) (f : X ⟶ Y) : PreservesColimit (parallelPair f 0) L
    where preserves c ic :=
    by
    letI := preserves_zero_morphisms_of_map_exact L h
    letI := preserves_epimorphisms_of_map_exact L h
    letI := epi_of_is_colimit_cofork ic
    have hf :=
      (is_colimit_map_cocone_cofork_equiv' L (cokernel_cofork.condition c)).symm
        (is_colimit_of_exact_of_epi (L.map f) (L.map (cofork.π c))
          (h
            (exact_of_is_cokernel f (cofork.π c) (cokernel_cofork.condition c)
              (ic.of_iso_colimit (iso_of_π _)))))
    exact hf.of_iso_colimit ((cocones.functoriality _ L).mapIso (iso_of_π _).symm)
#align category_theory.functor.preserves_cokernels_of_map_exact CategoryTheory.Functor.preservesCokernelsOfMapExact

/- warning: category_theory.functor.preserves_finite_limits_of_map_exact -> CategoryTheory.Functor.preservesFiniteLimitsOfMapExact is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u3}} {B : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u1, u3} A] [_inst_4 : CategoryTheory.Category.{u2, u4} B] [_inst_5 : CategoryTheory.Abelian.{u1, u3} A _inst_3] [_inst_6 : CategoryTheory.Abelian.{u2, u4} B _inst_4] (L : CategoryTheory.Functor.{u1, u2, u3, u4} A _inst_3 B _inst_4), (forall {{X : A}} {{Y : A}} {{Z : A}} {f : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) X Y} {g : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) Y Z}, (CategoryTheory.Exact.{u1, u3} A _inst_3 (CategoryTheory.Functor.preservesFiniteLimitsOfMapExact._proof_1.{u3, u1} A _inst_3 _inst_5) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u3} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Abelian.hasKernels.{u1, u3} A _inst_3 _inst_5) X Y Z f g) -> (CategoryTheory.Exact.{u2, u4} B _inst_4 (CategoryTheory.Functor.preservesFiniteLimitsOfMapExact._proof_2.{u4, u2} B _inst_4 _inst_6) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u4} B _inst_4 (CategoryTheory.Abelian.toPreadditive.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Abelian.hasKernels.{u2, u4} B _inst_4 _inst_6) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} A _inst_3 B _inst_4 L X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} A _inst_3 B _inst_4 L Y) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} A _inst_3 B _inst_4 L Z) (CategoryTheory.Functor.map.{u1, u2, u3, u4} A _inst_3 B _inst_4 L X Y f) (CategoryTheory.Functor.map.{u1, u2, u3, u4} A _inst_3 B _inst_4 L Y Z g))) -> (CategoryTheory.Limits.PreservesFiniteLimits.{u1, u2, u3, u4} A _inst_3 B _inst_4 L)
but is expected to have type
  forall {A : Type.{u3}} {B : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u1, u3} A] [_inst_4 : CategoryTheory.Category.{u2, u4} B] [_inst_5 : CategoryTheory.Abelian.{u1, u3} A _inst_3] [_inst_6 : CategoryTheory.Abelian.{u2, u4} B _inst_4] (L : CategoryTheory.Functor.{u1, u2, u3, u4} A _inst_3 B _inst_4), (forall {{X : A}} {{Y : A}} {{Z : A}} {f : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) X Y} {g : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) Y Z}, (CategoryTheory.Exact.{u1, u3} A _inst_3 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u3} A _inst_3 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u3} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u3} A _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u3} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Abelian.hasEqualizers.{u1, u3} A _inst_3 _inst_5)) X Y Z f g) -> (CategoryTheory.Exact.{u2, u4} B _inst_4 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u2, u4} B _inst_4 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u4} B _inst_4 (CategoryTheory.Abelian.toPreadditive.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u2, u4} B _inst_4 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u4} B _inst_4 (CategoryTheory.Abelian.toPreadditive.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Abelian.hasEqualizers.{u2, u4} B _inst_4 _inst_6)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) Y) (Prefunctor.obj.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) Z) (Prefunctor.map.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) X Y f) (Prefunctor.map.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) Y Z g))) -> (CategoryTheory.Limits.PreservesFiniteLimits.{u1, u2, u3, u4} A _inst_3 B _inst_4 L)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.preserves_finite_limits_of_map_exact CategoryTheory.Functor.preservesFiniteLimitsOfMapExactₓ'. -/
/-- A functor which preserves exactness is left exact, i.e. preserves finite limits.
This is part of the inverse implication to `functor.map_exact`. -/
def preservesFiniteLimitsOfMapExact : PreservesFiniteLimits L :=
  by
  letI := preserves_zero_morphisms_of_map_exact L h
  letI := preserves_kernels_of_map_exact L h
  apply preserves_finite_limits_of_preserves_kernels
#align category_theory.functor.preserves_finite_limits_of_map_exact CategoryTheory.Functor.preservesFiniteLimitsOfMapExact

/- warning: category_theory.functor.preserves_finite_colimits_of_map_exact -> CategoryTheory.Functor.preservesFiniteColimitsOfMapExact is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u3}} {B : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u1, u3} A] [_inst_4 : CategoryTheory.Category.{u2, u4} B] [_inst_5 : CategoryTheory.Abelian.{u1, u3} A _inst_3] [_inst_6 : CategoryTheory.Abelian.{u2, u4} B _inst_4] (L : CategoryTheory.Functor.{u1, u2, u3, u4} A _inst_3 B _inst_4), (forall {{X : A}} {{Y : A}} {{Z : A}} {f : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) X Y} {g : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) Y Z}, (CategoryTheory.Exact.{u1, u3} A _inst_3 (CategoryTheory.Functor.preservesFiniteColimitsOfMapExact._proof_1.{u3, u1} A _inst_3 _inst_5) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u3} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Abelian.hasKernels.{u1, u3} A _inst_3 _inst_5) X Y Z f g) -> (CategoryTheory.Exact.{u2, u4} B _inst_4 (CategoryTheory.Functor.preservesFiniteColimitsOfMapExact._proof_2.{u4, u2} B _inst_4 _inst_6) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u4} B _inst_4 (CategoryTheory.Abelian.toPreadditive.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Abelian.hasKernels.{u2, u4} B _inst_4 _inst_6) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} A _inst_3 B _inst_4 L X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} A _inst_3 B _inst_4 L Y) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} A _inst_3 B _inst_4 L Z) (CategoryTheory.Functor.map.{u1, u2, u3, u4} A _inst_3 B _inst_4 L X Y f) (CategoryTheory.Functor.map.{u1, u2, u3, u4} A _inst_3 B _inst_4 L Y Z g))) -> (CategoryTheory.Limits.PreservesFiniteColimits.{u1, u2, u3, u4} A _inst_3 B _inst_4 L)
but is expected to have type
  forall {A : Type.{u3}} {B : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u1, u3} A] [_inst_4 : CategoryTheory.Category.{u2, u4} B] [_inst_5 : CategoryTheory.Abelian.{u1, u3} A _inst_3] [_inst_6 : CategoryTheory.Abelian.{u2, u4} B _inst_4] (L : CategoryTheory.Functor.{u1, u2, u3, u4} A _inst_3 B _inst_4), (forall {{X : A}} {{Y : A}} {{Z : A}} {f : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) X Y} {g : Quiver.Hom.{succ u1, u3} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) Y Z}, (CategoryTheory.Exact.{u1, u3} A _inst_3 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u1, u3} A _inst_3 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u3} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u1, u3} A _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u3} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u1, u3} A _inst_3 _inst_5)) (CategoryTheory.Abelian.hasEqualizers.{u1, u3} A _inst_3 _inst_5)) X Y Z f g) -> (CategoryTheory.Exact.{u2, u4} B _inst_4 (CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations.{u2, u4} B _inst_4 (CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u4} B _inst_4 (CategoryTheory.Abelian.toPreadditive.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Limits.hasKernels_of_hasEqualizers.{u2, u4} B _inst_4 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u4} B _inst_4 (CategoryTheory.Abelian.toPreadditive.{u2, u4} B _inst_4 _inst_6)) (CategoryTheory.Abelian.hasEqualizers.{u2, u4} B _inst_4 _inst_6)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) Y) (Prefunctor.obj.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) Z) (Prefunctor.map.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) X Y f) (Prefunctor.map.{succ u1, succ u2, u3, u4} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} A (CategoryTheory.Category.toCategoryStruct.{u1, u3} A _inst_3)) B (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} B (CategoryTheory.Category.toCategoryStruct.{u2, u4} B _inst_4)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} A _inst_3 B _inst_4 L) Y Z g))) -> (CategoryTheory.Limits.PreservesFiniteColimits.{u1, u2, u3, u4} A _inst_3 B _inst_4 L)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.preserves_finite_colimits_of_map_exact CategoryTheory.Functor.preservesFiniteColimitsOfMapExactₓ'. -/
/-- A functor which preserves exactness is right exact, i.e. preserves finite colimits.
This is part of the inverse implication to `functor.map_exact`. -/
def preservesFiniteColimitsOfMapExact : PreservesFiniteColimits L :=
  by
  letI := preserves_zero_morphisms_of_map_exact L h
  letI := preserves_cokernels_of_map_exact L h
  apply preserves_finite_colimits_of_preserves_cokernels
#align category_theory.functor.preserves_finite_colimits_of_map_exact CategoryTheory.Functor.preservesFiniteColimitsOfMapExact

end

section

#print CategoryTheory.Functor.preservesFiniteLimitsOfPreservesMonosAndCokernels /-
/-- A functor preserving zero morphisms, monos, and cokernels preserves finite limits. -/
def preservesFiniteLimitsOfPreservesMonosAndCokernels [PreservesZeroMorphisms L]
    [PreservesMonomorphisms L] [∀ {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) L] :
    PreservesFiniteLimits L :=
  by
  apply preserves_finite_limits_of_map_exact
  intro X Y Z f g h
  rw [← abelian.coimage.fac g, L.map_comp, exact_comp_mono_iff]
  exact
    exact_of_is_cokernel _ _ _ (is_colimit_cofork_map_of_is_colimit' L _ (is_colimit_coimage f g h))
#align category_theory.functor.preserves_finite_limits_of_preserves_monos_and_cokernels CategoryTheory.Functor.preservesFiniteLimitsOfPreservesMonosAndCokernels
-/

#print CategoryTheory.Functor.preservesFiniteColimitsOfPreservesEpisAndKernels /-
/-- A functor preserving zero morphisms, epis, and kernels preserves finite colimits. -/
def preservesFiniteColimitsOfPreservesEpisAndKernels [PreservesZeroMorphisms L]
    [PreservesEpimorphisms L] [∀ {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) L] :
    PreservesFiniteColimits L :=
  by
  apply preserves_finite_colimits_of_map_exact
  intro X Y Z f g h
  rw [← abelian.image.fac f, L.map_comp, exact_epi_comp_iff]
  exact exact_of_is_kernel _ _ _ (is_limit_fork_map_of_is_limit' L _ (is_limit_image f g h))
#align category_theory.functor.preserves_finite_colimits_of_preserves_epis_and_kernels CategoryTheory.Functor.preservesFiniteColimitsOfPreservesEpisAndKernels
-/

end

end Functor

end CategoryTheory

