/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Jakob von Raumer

! This file was ported from Lean 3 source module category_theory.preadditive.left_exact
! leanprover-community/mathlib commit 0ebfdb71919ac6ca5d7fbc61a082fa2519556818
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathbin.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathbin.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Left exactness of functors between preadditive categories

We show that a functor is left exact in the sense that it preserves finite limits, if it
preserves kernels. The dual result holds for right exact functors and cokernels.
## Main results
* We first derive preservation of binary product in the lemma
  `preserves_binary_products_of_preserves_kernels`,
* then show the preservation of equalizers in `preserves_equalizer_of_preserves_kernels`,
* and then derive the preservation of all finite limits with the usual construction.

-/


universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Preadditive

namespace CategoryTheory

namespace Functor

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] {D : Type u₂} [Category.{v₂} D]
  [Preadditive D] (F : C ⥤ D) [PreservesZeroMorphisms F]

section FiniteLimits

/-- A functor between preadditive categories which preserves kernels preserves that an
arbitrary binary fan is a limit.
-/
def isLimitMapConeBinaryFanOfPreservesKernels {X Y Z : C} (π₁ : Z ⟶ X) (π₂ : Z ⟶ Y)
    [PreservesLimit (parallelPair π₂ 0) F] (i : IsLimit (BinaryFan.mk π₁ π₂)) :
    IsLimit (F.mapCone (BinaryFan.mk π₁ π₂)) :=
  by
  let bc := BinaryBicone.ofLimitCone i
  let presf : PreservesLimit (parallelPair bc.snd 0) F := by simpa
  let hf : IsLimit bc.snd_kernel_fork := BinaryBicone.isLimitSndKernelFork i
  exact
    (isLimitMapConeBinaryFanEquiv F π₁ π₂).invFun
      (BinaryBicone.isBilimitOfKernelInl (F.map_binary_bicone bc)
          (isLimitMapConeForkEquiv' F _ (isLimitOfPreserves F hf))).isLimit
#align category_theory.functor.is_limit_map_cone_binary_fan_of_preserves_kernels CategoryTheory.Functor.isLimitMapConeBinaryFanOfPreservesKernels

/-- A kernel preserving functor between preadditive categories preserves any pair being a limit. -/
def preservesBinaryProductOfPreservesKernels
    [∀ {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F] {X Y : C} :
    PreservesLimit (pair X Y) F
    where preserves c hc :=
    IsLimit.ofIsoLimit
      (isLimitMapConeBinaryFanOfPreservesKernels F _ _ (IsLimit.ofIsoLimit hc (isoBinaryFanMk c)))
      ((Cones.functoriality _ F).mapIso (isoBinaryFanMk c).symm)
#align category_theory.functor.preserves_binary_product_of_preserves_kernels CategoryTheory.Functor.preservesBinaryProductOfPreservesKernels

attribute [local instance] preserves_binary_product_of_preserves_kernels

/-- A kernel preserving functor between preadditive categories preserves binary products. -/
def preservesBinaryProductsOfPreservesKernels
    [∀ {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F] :
    PreservesLimitsOfShape (Discrete WalkingPair) F
    where PreservesLimit p := preservesLimitOfIsoDiagram F (diagramIsoPair p).symm
#align category_theory.functor.preserves_binary_products_of_preserves_kernels CategoryTheory.Functor.preservesBinaryProductsOfPreservesKernels

attribute [local instance] preserves_binary_products_of_preserves_kernels

variable [HasBinaryBiproducts C]

/-- A functor between preadditive categories preserves the equalizer of two
morphisms if it preserves all kernels. -/
def preservesEqualizerOfPreservesKernels [∀ {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F]
    {X Y : C} (f g : X ⟶ Y) : PreservesLimit (parallelPair f g) F :=
  by
  letI := preservesBinaryBiproductsOfPreservesBinaryProducts F
  haveI := additive_of_preservesBinaryBiproducts F
  constructor; intro c i
  let c' := isLimitKernelForkOfFork (i.of_iso_limit (Fork.isoForkOfι c))
  dsimp only [kernelForkOfFork_ofι] at c'
  let iFc := isLimitForkMapOfIsLimit' F _ c'
  apply IsLimit.ofIsoLimit _ ((Cones.functoriality _ F).mapIso (Fork.isoForkOfι c).symm)
  apply (isLimitMapConeForkEquiv F (Fork.condition c)).invFun
  let p : parallelPair (F.map (f - g)) 0 ≅ parallelPair (F.map f - F.map g) 0 :=
    parallelPair.eqOfHomEq F.map_sub rfl
  refine'
    IsLimit.ofIsoLimit (isLimitForkOfKernelFork ((IsLimit.postcomposeHomEquiv p _).symm iFc)) _
  convert Fork.isoForkOfι _
  rw [forkOfKernelFork_ι, Fork.ι_postcompose, KernelFork.ι_ofι, parallelPair.eqOfHomEq_hom_app]
  erw [Category.comp_id]
#align category_theory.functor.preserves_equalizer_of_preserves_kernels CategoryTheory.Functor.preservesEqualizerOfPreservesKernels

/-- A functor between preadditive categories preserves all equalizers if it preserves all kernels.
-/
def preservesEqualizersOfPreservesKernels
    [∀ {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F] :
    PreservesLimitsOfShape WalkingParallelPair F
    where PreservesLimit K :=
    by
    letI :=
      preservesEqualizerOfPreservesKernels F (K.map WalkingParallelPairHom.left)
        (K.map WalkingParallelPairHom.right)
    apply preservesLimitOfIsoDiagram F (diagramIsoParallelPair K).symm
#align category_theory.functor.preserves_equalizers_of_preserves_kernels CategoryTheory.Functor.preservesEqualizersOfPreservesKernels

/-- A functor between preadditive categories which preserves kernels preserves all finite limits.
-/
def preservesFiniteLimitsOfPreservesKernels [HasFiniteProducts C] [HasEqualizers C]
    [HasZeroObject C] [HasZeroObject D] [∀ {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F] :
    PreservesFiniteLimits F :=
  by
  letI := preservesEqualizersOfPreservesKernels F
  letI := preservesTerminalObjectOfPreservesZeroMorphisms F
  letI := preservesLimitsOfShapePemptyOfPreservesTerminal F
  letI p_prod := preservesFiniteProductsOfPreservesBinaryAndTerminal F
  apply @preserves_finite_limits_of_preserves_equalizers_and_finite_products _ _ _ _ _ _ _ _ @p_prod
#align category_theory.functor.preserves_finite_limits_of_preserves_kernels CategoryTheory.Functor.preservesFiniteLimitsOfPreservesKernels

end FiniteLimits

section FiniteColimits

/-- A functor between preadditive categories which preserves cokernels preserves finite coproducts.
-/
def isColimitMapCoconeBinaryCofanOfPreservesCokernels {X Y Z : C} (ι₁ : X ⟶ Z) (ι₂ : Y ⟶ Z)
    [PreservesColimit (parallelPair ι₂ 0) F] (i : IsColimit (BinaryCofan.mk ι₁ ι₂)) :
    IsColimit (F.mapCocone (BinaryCofan.mk ι₁ ι₂)) :=
  by
  let bc := BinaryBicone.ofColimitCocone i
  let presf : PreservesColimit (parallelPair bc.inr 0) F := by simpa
  let hf : IsColimit bc.inr_cokernel_cofork := BinaryBicone.isColimitInrCokernelCofork i
  exact
    (isColimitMapCoconeBinaryCofanEquiv F ι₁ ι₂).invFun
      (BinaryBicone.isBilimitOfCokernelFst (F.map_binary_bicone bc)
          (isColimitMapCoconeCoforkEquiv' F _ (isColimitOfPreserves F hf))).isColimit
#align category_theory.functor.is_colimit_map_cocone_binary_cofan_of_preserves_cokernels CategoryTheory.Functor.isColimitMapCoconeBinaryCofanOfPreservesCokernels

/-- A cokernel preserving functor between preadditive categories preserves any pair being
a colimit. -/
def preservesCoproductOfPreservesCokernels
    [∀ {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F] {X Y : C} :
    PreservesColimit (pair X Y) F
    where preserves c hc :=
    IsColimit.ofIsoColimit
      (isColimitMapCoconeBinaryCofanOfPreservesCokernels F _ _
        (IsColimit.ofIsoColimit hc (isoBinaryCofanMk c)))
      ((Cocones.functoriality _ F).mapIso (isoBinaryCofanMk c).symm)
#align category_theory.functor.preserves_coproduct_of_preserves_cokernels CategoryTheory.Functor.preservesCoproductOfPreservesCokernels

attribute [local instance] preserves_coproduct_of_preserves_cokernels

/-- A cokernel preserving functor between preadditive categories preserves binary coproducts. -/
def preservesBinaryCoproductsOfPreservesCokernels
    [∀ {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F] :
    PreservesColimitsOfShape (Discrete WalkingPair) F
    where PreservesColimit p := preservesColimitOfIsoDiagram F (diagramIsoPair p).symm
#align category_theory.functor.preserves_binary_coproducts_of_preserves_cokernels CategoryTheory.Functor.preservesBinaryCoproductsOfPreservesCokernels

attribute [local instance] preserves_binary_coproducts_of_preserves_cokernels

variable [HasBinaryBiproducts C]

/-- A functor between preadditive categoris preserves the coequalizer of two
morphisms if it preserves all cokernels. -/
def preservesCoequalizerOfPreservesCokernels
    [∀ {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F] {X Y : C} (f g : X ⟶ Y) :
    PreservesColimit (parallelPair f g) F :=
  by
  letI := preservesBinaryBiproductsOfPreservesBinaryCoproducts F
  haveI := additive_of_preservesBinaryBiproducts F
  constructor
  intro c i
  let c' := isColimitCokernelCoforkOfCofork (i.of_iso_colimit (Cofork.isoCoforkOfπ c))
  dsimp only [cokernelCoforkOfCofork_ofπ] at c'
  let iFc := isColimitCoforkMapOfIsColimit' F _ c'
  apply IsColimit.ofIsoColimit _ ((Cocones.functoriality _ F).mapIso (Cofork.isoCoforkOfπ c).symm)
  apply (isColimitMapCoconeCoforkEquiv F (Cofork.condition c)).invFun
  let p : parallelPair (F.map (f - g)) 0 ≅ parallelPair (F.map f - F.map g) 0 :=
    parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp)
  refine'
    IsColimit.ofIsoColimit
      (isColimitCoforkOfCokernelCofork ((IsColimit.precomposeHomEquiv p.symm _).symm iFc)) _
  convert Cofork.isoCoforkOfπ _
  rw [coforkOfCokernelCofork_π, Cofork.π_precompose, CokernelCofork.π_ofπ, Iso.symm_hom,
    parallelPair.ext_inv_app, Iso.refl_inv]
  erw [Category.id_comp]
#align category_theory.functor.preserves_coequalizer_of_preserves_cokernels CategoryTheory.Functor.preservesCoequalizerOfPreservesCokernels

/-- A functor between preadditive categories preserves all coequalizers if it preserves all kernels.
-/
def preservesCoequalizersOfPreservesCokernels
    [∀ {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F] :
    PreservesColimitsOfShape WalkingParallelPair F
    where PreservesColimit K :=
    by
    letI :=
      preservesCoequalizerOfPreservesCokernels F (K.map Limits.WalkingParallelPairHom.left)
        (K.map Limits.WalkingParallelPairHom.right)
    apply preservesColimitOfIsoDiagram F (diagramIsoParallelPair K).symm
#align category_theory.functor.preserves_coequalizers_of_preserves_cokernels CategoryTheory.Functor.preservesCoequalizersOfPreservesCokernels

/-- A functor between preadditive categories which preserves kernels preserves all finite limits.
-/
def preservesFiniteColimitsOfPreservesCokernels [HasFiniteCoproducts C] [HasCoequalizers C]
    [HasZeroObject C] [HasZeroObject D]
    [∀ {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F] : PreservesFiniteColimits F :=
  by
  letI := preservesCoequalizersOfPreservesCokernels F
  letI := preservesInitialObjectOfPreservesZeroMorphisms F
  letI := preservesColimitsOfShapePemptyOfPreservesInitial F
  letI p_prod := preservesFiniteCoproductsOfPreservesBinaryAndInitial F
  apply
    @preserves_finite_colimits_of_preserves_coequalizers_and_finite_coproducts C _ _ _ _ _ _ _
      @p_prod
#align category_theory.functor.preserves_finite_colimits_of_preserves_cokernels CategoryTheory.Functor.preservesFiniteColimitsOfPreservesCokernels

end FiniteColimits

end Functor

end CategoryTheory

