/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathbin.Algebra.Category.Module.EpiMono
import Mathbin.Algebra.Category.Module.Kernels
import Mathbin.CategoryTheory.Subobject.WellPowered
import Mathbin.CategoryTheory.Subobject.Limits

#align_import algebra.category.Module.subobject from "leanprover-community/mathlib"@"44e2ae8cffc713925494e4975ee31ec1d06929b3"

/-!
# Subobjects in the category of `R`-modules

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We construct an explicit order isomorphism between the categorical subobjects of an `R`-module `M`
and its submodules. This immediately implies that the category of `R`-modules is well-powered.

-/


open CategoryTheory

open CategoryTheory.Subobject

open CategoryTheory.Limits

open scoped ModuleCat

universe v u

namespace ModuleCat

variable {R : Type u} [Ring R] (M : ModuleCat.{v} R)

#print ModuleCat.subobjectModule /-
/-- The categorical subobjects of a module `M` are in one-to-one correspondence with its
    submodules.-/
noncomputable def subobjectModule : Subobject M ≃o Submodule R M :=
  OrderIso.symm
    { invFun := fun S => S.arrow.range
      toFun := fun N => Subobject.mk (↾N.Subtype)
      right_inv := fun S =>
        Eq.symm
          (by
            fapply eq_mk_of_comm
            · apply LinearEquiv.toModuleIso'Left
              apply LinearEquiv.ofBijective (LinearMap.codRestrict S.arrow.range S.arrow _)
              constructor
              ·
                simpa only [← LinearMap.ker_eq_bot, LinearMap.ker_codRestrict] using
                  ker_eq_bot_of_mono _
              ·
                rw [← LinearMap.range_eq_top, LinearMap.range_codRestrict,
                  Submodule.comap_subtype_self]
              · exact LinearMap.mem_range_self _
            · apply LinearMap.ext
              intro x
              rfl)
      left_inv := fun N =>
        by
        convert congr_arg LinearMap.range (underlying_iso_arrow (↾N.subtype)) using 1
        · have :
            (underlying_iso (↾N.subtype)).inv = (underlying_iso (↾N.subtype)).symm.toLinearEquiv :=
            by
            apply LinearMap.ext
            intro x
            rfl
          rw [this, comp_def, LinearEquiv.range_comp]
        · exact (Submodule.range_subtype _).symm
      map_rel_iff' := fun S T =>
        by
        refine' ⟨fun h => _, fun h => mk_le_mk_of_comm (↟(Submodule.ofLe h)) (by ext; rfl)⟩
        convert LinearMap.range_comp_le_range (of_mk_le_mk _ _ h) (↾T.subtype)
        · simpa only [← comp_def, of_mk_le_mk_comp] using (Submodule.range_subtype _).symm
        · exact (Submodule.range_subtype _).symm }
#align Module.subobject_Module ModuleCat.subobjectModule
-/

#print ModuleCat.wellPowered_moduleCat /-
instance wellPowered_moduleCat : WellPowered (ModuleCat.{v} R) :=
  ⟨fun M => ⟨⟨_, ⟨(subobjectModule M).toEquiv⟩⟩⟩⟩
#align Module.well_powered_Module ModuleCat.wellPowered_moduleCat
-/

attribute [local instance] has_kernels_Module

#print ModuleCat.toKernelSubobject /-
/-- Bundle an element `m : M` such that `f m = 0` as a term of `kernel_subobject f`. -/
noncomputable def toKernelSubobject {M N : ModuleCat R} {f : M ⟶ N} :
    LinearMap.ker f →ₗ[R] kernelSubobject f :=
  (kernelSubobjectIso f ≪≫ ModuleCat.kernelIsoKer f).inv
#align Module.to_kernel_subobject ModuleCat.toKernelSubobject
-/

#print ModuleCat.toKernelSubobject_arrow /-
@[simp]
theorem toKernelSubobject_arrow {M N : ModuleCat R} {f : M ⟶ N} (x : LinearMap.ker f) :
    (kernelSubobject f).arrow (toKernelSubobject x) = x.1 := by simp [to_kernel_subobject]
#align Module.to_kernel_subobject_arrow ModuleCat.toKernelSubobject_arrow
-/

#print ModuleCat.cokernel_π_imageSubobject_ext /-
/-- An extensionality lemma showing that two elements of a cokernel by an image
are equal if they differ by an element of the image.

The application is for homology:
two elements in homology are equal if they differ by a boundary.
-/
@[ext]
theorem cokernel_π_imageSubobject_ext {L M N : ModuleCat.{v} R} (f : L ⟶ M) [HasImage f]
    (g : (imageSubobject f : ModuleCat.{v} R) ⟶ N) [HasCokernel g] {x y : N} (l : L)
    (w : x = y + g (factorThruImageSubobject f l)) : cokernel.π g x = cokernel.π g y := by subst w;
  simp
#align Module.cokernel_π_image_subobject_ext ModuleCat.cokernel_π_imageSubobject_ext
-/

end ModuleCat

