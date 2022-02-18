import Mathbin.LinearAlgebra.Isomorphisms
import Mathbin.Algebra.Category.Module.Kernels
import Mathbin.Algebra.Category.Module.Limits
import Mathbin.CategoryTheory.Abelian.Exact

/-!
# The category of left R-modules is abelian.

Additionally, two linear maps are exact in the categorical sense iff `range f = ker g`.
-/


open CategoryTheory

open CategoryTheory.Limits

noncomputable section

universe v u

namespace ModuleCat

variable {R : Type u} [Ringₓ R] {M N : ModuleCat.{v} R} (f : M ⟶ N)

/-- In the category of modules, every monomorphism is normal. -/
def normal_mono (hf : Mono f) : NormalMono f where
  z := of R (N ⧸ f.range)
  g := f.range.mkq
  w := LinearMap.range_mkq_comp _
  IsLimit :=
    IsKernel.isoKernel _ _ (kernelIsLimit _)
        (LinearEquiv.toModuleIso'
          ((Submodule.quotEquivOfEqBot _ (ker_eq_bot_of_mono _)).symm ≪≫ₗ
            (LinearMap.quotKerEquivRange f ≪≫ₗ LinearEquiv.ofEq _ _ (Submodule.ker_mkq _).symm))) <|
      by
      ext
      rfl

/-- In the category of modules, every epimorphism is normal. -/
def normal_epi (hf : Epi f) : NormalEpi f where
  w := of R f.ker
  g := f.ker.Subtype
  w := LinearMap.comp_ker_subtype _
  IsColimit :=
    IsCokernel.cokernelIso _ _ (cokernelIsColimit _)
        (LinearEquiv.toModuleIso'
          (Submodule.quotEquivOfEq _ _ (Submodule.range_subtype _) ≪≫ₗ LinearMap.quotKerEquivRange f ≪≫ₗ
            LinearEquiv.ofTop _ (range_eq_top_of_epi _))) <|
      by
      ext
      rfl

/-- The category of R-modules is abelian. -/
instance : Abelian (ModuleCat R) where
  HasFiniteProducts :=
    ⟨by
      infer_instance⟩
  HasKernels := by
    infer_instance
  HasCokernels := has_cokernels_Module
  normalMonoOfMono := fun X Y => normalMono
  normalEpiOfEpi := fun X Y => normalEpi

variable {O : ModuleCat.{v} R} (g : N ⟶ O)

open LinearMap

attribute [local instance] preadditive.has_equalizers_of_has_kernels

theorem exact_iff : Exact f g ↔ f.range = g.ker := by
  rw [abelian.exact_iff' f g (kernel_is_limit _) (cokernel_is_colimit _)]
  exact
    ⟨fun h => le_antisymmₓ (range_le_ker_iff.2 h.1) (ker_le_range_iff.2 h.2), fun h =>
      ⟨range_le_ker_iff.1 <| le_of_eqₓ h, ker_le_range_iff.1 <| le_of_eqₓ h.symm⟩⟩

end ModuleCat

