/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.abelian.transfer
! leanprover-community/mathlib commit 0ebfdb71919ac6ca5d7fbc61a082fa2519556818
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Abelian.Basic
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathbin.CategoryTheory.Adjunction.Limits

/-!
# Transferring "abelian-ness" across a functor

If `C` is an additive category, `D` is an abelian category,
we have `F : C ⥤ D` `G : D ⥤ C` (both preserving zero morphisms),
`G` is left exact (that is, preserves finite limits),
and further we have `adj : G ⊣ F` and `i : F ⋙ G ≅ 𝟭 C`,
then `C` is also abelian.

See <https://stacks.math.columbia.edu/tag/03A3>

## Notes
The hypotheses, following the statement from the Stacks project,
may appear suprising: we don't ask that the counit of the adjunction is an isomorphism,
but just that we have some potentially unrelated isomorphism `i : F ⋙ G ≅ 𝟭 C`.

However Lemma A1.1.1 from [Elephant] shows that in this situation the counit itself
must be an isomorphism, and thus that `C` is a reflective subcategory of `D`.

Someone may like to formalize that lemma, and restate this theorem in terms of `reflective`.
(That lemma has a nice string diagrammatic proof that holds in any bicategory.)
-/


noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

universe v u₁ u₂

namespace AbelianOfAdjunction

variable {C : Type u₁} [Category.{v} C] [Preadditive C]

variable {D : Type u₂} [Category.{v} D] [Abelian D]

variable (F : C ⥤ D)

variable (G : D ⥤ C) [Functor.PreservesZeroMorphisms G]

variable (i : F ⋙ G ≅ 𝟭 C) (adj : G ⊣ F)

include i

/-- No point making this an instance, as it requires `i`. -/
theorem hasKernels [PreservesFiniteLimits G] : HasKernels C :=
  {
    HasLimit := fun X Y f => by
      have := NatIso.naturality_1 i f
      simp at this
      rw [← this]
      haveI : HasKernel (G.map (F.map f) ≫ i.hom.app _) := Limits.hasKernel_comp_mono _ _
      apply Limits.hasKernel_iso_comp }
#align category_theory.abelian_of_adjunction.has_kernels CategoryTheory.AbelianOfAdjunction.hasKernels

include adj

/-- No point making this an instance, as it requires `i` and `adj`. -/
theorem hasCokernels : HasCokernels C :=
  {
    HasColimit := fun X Y f =>
      by
      haveI : PreservesColimits G := adj.left_adjoint_preserves_colimits
      have := NatIso.naturality_1 i f
      simp at this
      rw [← this]
      haveI : HasCokernel (G.map (F.map f) ≫ i.hom.app _) := Limits.hasCokernel_comp_iso _ _
      apply Limits.hasCokernel_epi_comp }
#align category_theory.abelian_of_adjunction.has_cokernels CategoryTheory.AbelianOfAdjunction.hasCokernels

variable [Limits.HasCokernels C]

/-- Auxiliary construction for `coimage_iso_image` -/
def cokernelIso {X Y : C} (f : X ⟶ Y) : G.obj (cokernel (F.map f)) ≅ cokernel f :=
  by
  -- We have to write an explicit `preserves_colimits` type here,
  -- as `left_adjoint_preserves_colimits` has universe variables.
  haveI : PreservesColimits G := adj.left_adjoint_preserves_colimits
  calc
    G.obj (cokernel (F.map f)) ≅ cokernel (G.map (F.map f)) := (asIso (cokernelComparison _ G)).symm
    _ ≅ cokernel (_ ≫ f ≫ _) := cokernelIsoOfEq (NatIso.naturality_2 i f).symm
    _ ≅ cokernel (f ≫ _) := cokernelEpiComp _ _
    _ ≅ cokernel f := cokernelCompIsIso _ _
    
#align category_theory.abelian_of_adjunction.cokernel_iso CategoryTheory.AbelianOfAdjunction.cokernelIso

variable [Limits.HasKernels C] [PreservesFiniteLimits G]

/-- Auxiliary construction for `coimage_iso_image` -/
def coimageIsoImageAux {X Y : C} (f : X ⟶ Y) :
    kernel (G.map (cokernel.π (F.map f))) ≅ kernel (cokernel.π f) :=
  by
  haveI : PreservesColimits G := adj.left_adjoint_preserves_colimits
  calc
    kernel (G.map (cokernel.π (F.map f))) ≅
        kernel (cokernel.π (G.map (F.map f)) ≫ cokernelComparison (F.map f) G) :=
      kernelIsoOfEq (π_comp_cokernelComparison _ _).symm
    _ ≅ kernel (cokernel.π (G.map (F.map f))) := kernelCompMono _ _
    _ ≅ kernel (cokernel.π (_ ≫ f ≫ _) ≫ (cokernelIsoOfEq _).hom) :=
      kernelIsoOfEq (π_comp_cokernelIsoOfEq_hom (NatIso.naturality_2 i f)).symm
    _ ≅ kernel (cokernel.π (_ ≫ f ≫ _)) := kernelCompMono _ _
    _ ≅ kernel (cokernel.π (f ≫ i.inv.app Y) ≫ (cokernelEpiComp (i.hom.app X) _).inv) :=
      kernelIsoOfEq (by simp only [cokernel.π_desc, cokernelEpiComp_inv])
    _ ≅ kernel (cokernel.π (f ≫ _)) := kernelCompMono _ _
    _ ≅ kernel (inv (i.inv.app Y) ≫ cokernel.π f ≫ (cokernelCompIsIso f (i.inv.app Y)).inv) :=
      kernelIsoOfEq
        (by
          simp only [cokernel.π_desc, cokernelCompIsIso_inv, Iso.hom_inv_id_app_assoc,
            NatIso.inv_inv_app])
    _ ≅ kernel (cokernel.π f ≫ _) := kernelIsIsoComp _ _
    _ ≅ kernel (cokernel.π f) := kernelCompMono _ _
    
#align category_theory.abelian_of_adjunction.coimage_iso_image_aux CategoryTheory.AbelianOfAdjunction.coimageIsoImageAux

variable [Functor.PreservesZeroMorphisms F]

/-- Auxiliary definition: the abelian coimage and abelian image agree.
We still need to check that this agrees with the canonical morphism.
-/
def coimageIsoImage {X Y : C} (f : X ⟶ Y) : Abelian.coimage f ≅ Abelian.image f :=
  by
  haveI : PreservesLimits F := adj.right_adjoint_preserves_limits
  haveI : PreservesColimits G := adj.left_adjoint_preserves_colimits
  calc
    Abelian.coimage f ≅ cokernel (kernel.ι f) := Iso.refl _
    _ ≅ G.obj (cokernel (F.map (kernel.ι f))) := (cokernelIso _ _ i adj _).symm
    _ ≅ G.obj (cokernel (kernelComparison f F ≫ kernel.ι (F.map f))) :=
      G.map_iso (cokernelIsoOfEq (by simp))
    _ ≅ G.obj (cokernel (kernel.ι (F.map f))) := G.map_iso (cokernelEpiComp _ _)
    _ ≅ G.obj (Abelian.coimage (F.map f)) := Iso.refl _
    _ ≅ G.obj (Abelian.image (F.map f)) := G.map_iso (Abelian.coimageIsoImage _)
    _ ≅ G.obj (kernel (cokernel.π (F.map f))) := Iso.refl _
    _ ≅ kernel (G.map (cokernel.π (F.map f))) := PreservesKernel.iso _ _
    _ ≅ kernel (cokernel.π f) := coimageIsoImageAux F G i adj f
    _ ≅ Abelian.image f := Iso.refl _
    
#align category_theory.abelian_of_adjunction.coimage_iso_image CategoryTheory.AbelianOfAdjunction.coimageIsoImage

attribute [local simp] cokernel_iso coimage_iso_image coimage_iso_image_aux

-- The account of this proof in the Stacks project omits this calculation.
theorem coimageIsoImage_hom {X Y : C} (f : X ⟶ Y) :
    (coimageIsoImage F G i adj f).hom = Abelian.coimageImageComparison f :=
  by
  ext
  simpa only [← G.map_comp_assoc, coimageIsoImage, NatIso.inv_inv_app, cokernelIso,
    coimageIsoImageAux, Iso.trans_symm, Iso.symm_symm_eq, Iso.refl_trans, Iso.trans_refl,
    Iso.trans_hom, Iso.symm_hom, cokernelCompIsIso_inv, cokernelEpiComp_inv, asIso_hom,
    Functor.mapIso_hom, cokernelEpiComp_hom, PreservesKernel.iso_hom, kernelCompMono_hom,
    kernelIsIsoComp_hom, cokernelIsoOfEq_hom_comp_desc_assoc, cokernel.π_desc_assoc, Category.assoc,
    π_comp_cokernelIsoOfEq_inv_assoc, π_comp_cokernelComparison_assoc, kernel.lift_ι,
    kernel.lift_ι_assoc, kernelIsoOfEq_hom_comp_ι_assoc, kernelComparison_comp_ι_assoc,
    Abelian.coimage_image_factorisation] using NatIso.naturality_1 i f
#align category_theory.abelian_of_adjunction.coimage_iso_image_hom CategoryTheory.AbelianOfAdjunction.coimageIsoImage_hom

end AbelianOfAdjunction

open AbelianOfAdjunction

/-- If `C` is an additive category, `D` is an abelian category,
we have `F : C ⥤ D` `G : D ⥤ C` (both preserving zero morphisms),
`G` is left exact (that is, preserves finite limits),
and further we have `adj : G ⊣ F` and `i : F ⋙ G ≅ 𝟭 C`,
then `C` is also abelian.

See <https://stacks.math.columbia.edu/tag/03A3>
-/
def abelianOfAdjunction {C : Type u₁} [Category.{v} C] [Preadditive C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v} D] [Abelian D] (F : C ⥤ D) [Functor.PreservesZeroMorphisms F]
    (G : D ⥤ C) [Functor.PreservesZeroMorphisms G] [PreservesFiniteLimits G] (i : F ⋙ G ≅ 𝟭 C)
    (adj : G ⊣ F) : Abelian C := by
  haveI := has_kernels F G i
  haveI := has_cokernels F G i adj
  have : ∀ {X Y : C} (f : X ⟶ Y), IsIso (Abelian.coimageImageComparison f) :=
    by
    intro X Y f
    rw [← coimageIsoImage_hom F G i adj f]
    infer_instance
  apply Abelian.ofCoimageImageComparisonIsIso
#align category_theory.abelian_of_adjunction CategoryTheory.abelianOfAdjunction

/-- If `C` is an additive category equivalent to an abelian category `D`
via a functor that preserves zero morphisms,
then `C` is also abelian.
-/
def abelianOfEquivalence {C : Type u₁} [Category.{v} C] [Preadditive C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v} D] [Abelian D] (F : C ⥤ D) [Functor.PreservesZeroMorphisms F]
    [IsEquivalence F] : Abelian C :=
  abelianOfAdjunction F F.inv F.asEquivalence.unitIso.symm F.asEquivalence.symm.toAdjunction
#align category_theory.abelian_of_equivalence CategoryTheory.abelianOfEquivalence

end CategoryTheory

