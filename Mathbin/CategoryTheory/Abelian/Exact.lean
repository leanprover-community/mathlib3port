/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathbin.CategoryTheory.Abelian.Basic
import Mathbin.Algebra.Homology.Exact
import Mathbin.Tactic.Tfae

/-!
# Exact sequences in abelian categories

In an abelian category, we get several interesting results related to exactness which are not
true in more general settings.

## Main results
* `(f, g)` is exact if and only if `f ≫ g = 0` and `kernel.ι g ≫ cokernel.π f = 0`. This
  characterisation tends to be less cumbersome to work with than the original definition involving
  the comparison map `image f ⟶ kernel g`.
* If `(f, g)` is exact, then `image.ι f` has the universal property of the kernel of `g`.
* `f` is a monomorphism iff `kernel.ι f = 0` iff `exact 0 f`, and `f` is an epimorphism iff
  `cokernel.π = 0` iff `exact f 0`.

-/


universe v u

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Preadditive

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace CategoryTheory.Abelian

variable {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

attribute [local instance] has_equalizers_of_has_kernels

/-- In an abelian category, a pair of morphisms `f : X ⟶ Y`, `g : Y ⟶ Z` is exact
iff `image_subobject f = kernel_subobject g`.
-/
theorem exact_iff_image_eq_kernel : Exact f g ↔ imageSubobject f = kernelSubobject g := by
  constructor
  · intro h
    fapply subobject.eq_of_comm
    · suffices is_iso (imageToKernel _ _ h.w) by
        exact as_iso (imageToKernel _ _ h.w)
      exact is_iso_of_mono_of_epi _
      
    · simp
      
    
  · apply exact_of_image_eq_kernel
    

theorem exact_iff : Exact f g ↔ f ≫ g = 0 ∧ kernel.ι g ≫ cokernel.π f = 0 := by
  constructor
  · intro h
    exact ⟨h.1, kernel_comp_cokernel f g⟩
    
  · refine' fun h => ⟨h.1, _⟩
    suffices hl : is_limit (kernel_fork.of_ι (image_subobject f).arrow (image_subobject_arrow_comp_eq_zero h.1))
    · have :
        imageToKernel f g h.1 =
          (is_limit.cone_point_unique_up_to_iso hl (limit.is_limit _)).Hom ≫ (kernel_subobject_iso _).inv :=
        by
        ext
        simp
      rw [this]
      infer_instance
      
    refine' is_limit.of_ι _ _ _ _ _
    · refine' fun W u hu => kernel.lift (cokernel.π f) u _ ≫ (image_iso_image f).Hom ≫ (image_subobject_iso _).inv
      rw [← kernel.lift_ι g u hu, category.assoc, h.2, has_zero_morphisms.comp_zero]
      
    · tidy
      
    · intros
      rw [← cancel_mono (image_subobject f).arrow, w]
      simp
      
    

theorem exact_iff' {cg : KernelFork g} (hg : IsLimit cg) {cf : CokernelCofork f} (hf : IsColimit cf) :
    Exact f g ↔ f ≫ g = 0 ∧ cg.ι ≫ cf.π = 0 := by
  constructor
  · intro h
    exact ⟨h.1, fork_ι_comp_cofork_π f g cg cf⟩
    
  · rw [exact_iff]
    refine' fun h => ⟨h.1, _⟩
    apply zero_of_epi_comp (is_limit.cone_point_unique_up_to_iso hg (limit.is_limit _)).Hom
    apply zero_of_comp_mono (is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit _) hf).Hom
    simp [h.2]
    

theorem exact_tfae :
    Tfae [Exact f g, f ≫ g = 0 ∧ kernel.ι g ≫ cokernel.π f = 0, imageSubobject f = kernelSubobject g] := by
  tfae_have 1 ↔ 2
  · apply exact_iff
    
  tfae_have 1 ↔ 3
  · apply exact_iff_image_eq_kernel
    
  tfae_finish

/-- If `(f, g)` is exact, then `images.image.ι f` is a kernel of `g`. -/
def isLimitImage [h : Exact f g] :
    IsLimit (KernelFork.ofι (Images.image.ι f) (Images.image_ι_comp_eq_zero h.1) : KernelFork g) := by
  rw [exact_iff] at h
  refine' is_limit.of_ι _ _ _ _ _
  · refine' fun W u hu => kernel.lift (cokernel.π f) u _
    rw [← kernel.lift_ι g u hu, category.assoc, h.2, has_zero_morphisms.comp_zero]
    
  tidy

/-- If `(f, g)` is exact, then `image.ι f` is a kernel of `g`. -/
def isLimitImage' [h : Exact f g] : IsLimit (KernelFork.ofι (image.ι f) (image_ι_comp_eq_zero h.1)) :=
  IsKernel.isoKernel _ _ (isLimitImage f g) (imageIsoImage f).symm <| IsImage.lift_fac _ _

/-- If `(f, g)` is exact, then `coimages.coimage.π g` is a cokernel of `f`. -/
def isColimitCoimage [h : Exact f g] :
    IsColimit (CokernelCofork.ofπ (Coimages.coimage.π g) (Coimages.comp_coimage_π_eq_zero h.1) : CokernelCofork f) := by
  rw [exact_iff] at h
  refine' is_colimit.of_π _ _ _ _ _
  · refine' fun W u hu => cokernel.desc (kernel.ι g) u _
    rw [← cokernel.π_desc f u hu, ← category.assoc, h.2, has_zero_morphisms.zero_comp]
    
  tidy

/-- If `(f, g)` is exact, then `factor_thru_image g` is a cokernel of `f`. -/
def isColimitImage [h : Exact f g] :
    IsColimit (CokernelCofork.ofπ (factorThruImage g) (comp_factor_thru_image_eq_zero h.1)) :=
  IsCokernel.cokernelIso _ _ (isColimitCoimage f g) (coimageIsoImage' g) <|
    (cancel_mono (image.ι g)).1 <| by
      simp

theorem exact_cokernel : Exact f (cokernel.π f) := by
  rw [exact_iff]
  tidy

instance [Exact f g] :
    Mono
      (cokernel.desc f g
        (by
          simp )) :=
  suffices h :
    cokernel.desc f g
        (by
          simp ) =
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (isColimitImage f g)).Hom ≫ image.ι g
    from by
    rw [h]
    apply mono_comp
  (cancel_epi (cokernel.π f)).1 <| by
    simp

section

variable (Z)

theorem tfae_mono : Tfae [Mono f, kernel.ι f = 0, Exact (0 : Z ⟶ X) f] := by
  tfae_have 3 → 2
  · intros
    exact kernel_ι_eq_zero_of_exact_zero_left Z
    
  tfae_have 1 → 3
  · intros
    exact exact_zero_left_of_mono Z
    
  tfae_have 2 → 1
  · exact mono_of_kernel_ι_eq_zero _
    
  tfae_finish

-- Note we've already proved `mono_iff_exact_zero_left : mono f ↔ exact (0 : Z ⟶ X) f`
-- in any preadditive category with kernels and images.
theorem mono_iff_kernel_ι_eq_zero : Mono f ↔ kernel.ι f = 0 :=
  (tfae_mono X f).out 0 1

theorem tfae_epi : Tfae [Epi f, cokernel.π f = 0, Exact f (0 : Y ⟶ Z)] := by
  tfae_have 3 → 2
  · rw [exact_iff]
    rintro ⟨-, h⟩
    exact zero_of_epi_comp _ h
    
  tfae_have 1 → 3
  · rw [exact_iff]
    intro
    exact
      ⟨by
        simp , by
        simp [cokernel.π_of_epi]⟩
    
  tfae_have 2 → 1
  · exact epi_of_cokernel_π_eq_zero _
    
  tfae_finish

-- Note we've already proved `epi_iff_exact_zero_right : epi f ↔ exact f (0 : Y ⟶ Z)`
-- in any preadditive category with equalizers and images.
theorem epi_iff_cokernel_π_eq_zero : Epi f ↔ cokernel.π f = 0 :=
  (tfae_epi X f).out 0 1

end

end CategoryTheory.Abelian

