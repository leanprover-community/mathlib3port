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

variable {C : Type u} [category.{v} C] [abelian C]

namespace CategoryTheory.Abelian

variable {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

attribute [local instance] has_equalizers_of_has_kernels

/-- In an abelian category, a pair of morphisms `f : X ⟶ Y`, `g : Y ⟶ Z` is exact
iff `image_subobject f = kernel_subobject g`.
-/
theorem exact_iff_image_eq_kernel : exact f g ↔ image_subobject f = kernel_subobject g := by
  constructor
  · intro h
    fapply subobject.eq_of_comm
    · suffices is_iso (imageToKernel _ _ h.w) by
        exact as_iso (imageToKernel _ _ h.w)
      exact is_iso_of_mono_of_epi _
      
    · simp
      
    
  · apply exact_of_image_eq_kernel
    

theorem exact_iff : exact f g ↔ f ≫ g = 0 ∧ kernel.ι g ≫ cokernel.π f = 0 := by
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
      
    

theorem exact_iff' {cg : kernel_fork g} (hg : is_limit cg) {cf : cokernel_cofork f} (hf : is_colimit cf) :
    exact f g ↔ f ≫ g = 0 ∧ cg.ι ≫ cf.π = 0 := by
  constructor
  · intro h
    exact ⟨h.1, fork_ι_comp_cofork_π f g cg cf⟩
    
  · rw [exact_iff]
    refine' fun h => ⟨h.1, _⟩
    apply zero_of_epi_comp (is_limit.cone_point_unique_up_to_iso hg (limit.is_limit _)).Hom
    apply zero_of_comp_mono (is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit _) hf).Hom
    simp [h.2]
    

theorem exact_tfae :
    tfae [exact f g, f ≫ g = 0 ∧ kernel.ι g ≫ cokernel.π f = 0, image_subobject f = kernel_subobject g] := by
  tfae_have 1 ↔ 2
  · apply exact_iff
    
  tfae_have 1 ↔ 3
  · apply exact_iff_image_eq_kernel
    
  tfae_finish

/-- If `(f, g)` is exact, then `images.image.ι f` is a kernel of `g`. -/
def is_limit_image [h : exact f g] :
    is_limit (kernel_fork.of_ι (images.image.ι f) (images.image_ι_comp_eq_zero h.1) : kernel_fork g) := by
  rw [exact_iff] at h
  refine' is_limit.of_ι _ _ _ _ _
  · refine' fun W u hu => kernel.lift (cokernel.π f) u _
    rw [← kernel.lift_ι g u hu, category.assoc, h.2, has_zero_morphisms.comp_zero]
    
  tidy

/-- If `(f, g)` is exact, then `image.ι f` is a kernel of `g`. -/
def is_limit_image' [h : exact f g] : is_limit (kernel_fork.of_ι (image.ι f) (image_ι_comp_eq_zero h.1)) :=
  is_kernel.iso_kernel _ _ (is_limit_image f g) (image_iso_image f).symm $ is_image.lift_fac _ _

/-- If `(f, g)` is exact, then `coimages.coimage.π g` is a cokernel of `f`. -/
def is_colimit_coimage [h : exact f g] :
    is_colimit
      (cokernel_cofork.of_π (coimages.coimage.π g) (coimages.comp_coimage_π_eq_zero h.1) : cokernel_cofork f) :=
  by
  rw [exact_iff] at h
  refine' is_colimit.of_π _ _ _ _ _
  · refine' fun W u hu => cokernel.desc (kernel.ι g) u _
    rw [← cokernel.π_desc f u hu, ← category.assoc, h.2, has_zero_morphisms.zero_comp]
    
  tidy

/-- If `(f, g)` is exact, then `factor_thru_image g` is a cokernel of `f`. -/
def is_colimit_image [h : exact f g] :
    is_colimit (cokernel_cofork.of_π (factor_thru_image g) (comp_factor_thru_image_eq_zero h.1)) :=
  is_cokernel.cokernel_iso _ _ (is_colimit_coimage f g) (coimage_iso_image' g) $
    (cancel_mono (image.ι g)).1 $ by
      simp

theorem exact_cokernel : exact f (cokernel.π f) := by
  rw [exact_iff]
  tidy

instance [exact f g] :
    mono
      (cokernel.desc f g
        (by
          simp )) :=
  suffices h :
    cokernel.desc f g
        (by
          simp ) =
      (is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit _) (is_colimit_image f g)).Hom ≫ image.ι g
    from by
    rw [h]
    apply mono_comp
  (cancel_epi (cokernel.π f)).1 $ by
    simp

section

variable (Z)

theorem tfae_mono : tfae [mono f, kernel.ι f = 0, exact (0 : Z ⟶ X) f] := by
  tfae_have 3 → 2
  · intros
    exact kernel_ι_eq_zero_of_exact_zero_left Z
    
  tfae_have 1 → 3
  · intros
    exact exact_zero_left_of_mono Z
    
  tfae_have 2 → 1
  · exact mono_of_kernel_ι_eq_zero _
    
  tfae_finish

theorem mono_iff_kernel_ι_eq_zero : mono f ↔ kernel.ι f = 0 :=
  (tfae_mono X f).out 0 1

theorem tfae_epi : tfae [epi f, cokernel.π f = 0, exact f (0 : Y ⟶ Z)] := by
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

theorem epi_iff_cokernel_π_eq_zero : epi f ↔ cokernel.π f = 0 :=
  (tfae_epi X f).out 0 1

end

end CategoryTheory.Abelian

