/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import CategoryTheory.Limits.Shapes.Pullbacks
import CategoryTheory.Limits.Shapes.BinaryProducts
import CategoryTheory.Limits.Preserves.Shapes.Pullbacks

#align_import category_theory.limits.constructions.epi_mono from "leanprover-community/mathlib"@"f47581155c818e6361af4e4fda60d27d020c226b"

/-!
# Relating monomorphisms and epimorphisms to limits and colimits

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

If `F` preserves (resp. reflects) pullbacks, then it preserves (resp. reflects) monomorphisms.

We also provide the dual version for epimorphisms.

-/


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

variable (F : C ⥤ D)

#print CategoryTheory.preserves_mono_of_preservesLimit /-
/-- If `F` preserves pullbacks, then it preserves monomorphisms. -/
theorem preserves_mono_of_preservesLimit {X Y : C} (f : X ⟶ Y) [PreservesLimit (cospan f f) F]
    [Mono f] : Mono (F.map f) :=
  by
  have := is_limit_pullback_cone_map_of_is_limit F _ (pullback_cone.is_limit_mk_id_id f)
  simp_rw [F.map_id] at this
  apply pullback_cone.mono_of_is_limit_mk_id_id _ this
#align category_theory.preserves_mono_of_preserves_limit CategoryTheory.preserves_mono_of_preservesLimit
-/

#print CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape /-
instance (priority := 100) preservesMonomorphisms_of_preservesLimitsOfShape
    [PreservesLimitsOfShape WalkingCospan F] : F.PreservesMonomorphisms
    where preserves X Y f hf := preserves_mono_of_preserves_limit F f
#align category_theory.preserves_monomorphisms_of_preserves_limits_of_shape CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape
-/

#print CategoryTheory.reflects_mono_of_reflectsLimit /-
/-- If `F` reflects pullbacks, then it reflects monomorphisms. -/
theorem reflects_mono_of_reflectsLimit {X Y : C} (f : X ⟶ Y) [ReflectsLimit (cospan f f) F]
    [Mono (F.map f)] : Mono f :=
  by
  have := pullback_cone.is_limit_mk_id_id (F.map f)
  simp_rw [← F.map_id] at this
  apply pullback_cone.mono_of_is_limit_mk_id_id _ (is_limit_of_is_limit_pullback_cone_map F _ this)
#align category_theory.reflects_mono_of_reflects_limit CategoryTheory.reflects_mono_of_reflectsLimit
-/

#print CategoryTheory.reflectsMonomorphisms_of_reflectsLimitsOfShape /-
instance (priority := 100) reflectsMonomorphisms_of_reflectsLimitsOfShape
    [ReflectsLimitsOfShape WalkingCospan F] : F.ReflectsMonomorphisms
    where reflects X Y f hf := reflects_mono_of_reflects_limit F f
#align category_theory.reflects_monomorphisms_of_reflects_limits_of_shape CategoryTheory.reflectsMonomorphisms_of_reflectsLimitsOfShape
-/

#print CategoryTheory.preserves_epi_of_preservesColimit /-
/-- If `F` preserves pushouts, then it preserves epimorphisms. -/
theorem preserves_epi_of_preservesColimit {X Y : C} (f : X ⟶ Y) [PreservesColimit (span f f) F]
    [Epi f] : Epi (F.map f) :=
  by
  have := is_colimit_pushout_cocone_map_of_is_colimit F _ (pushout_cocone.is_colimit_mk_id_id f)
  simp_rw [F.map_id] at this
  apply pushout_cocone.epi_of_is_colimit_mk_id_id _ this
#align category_theory.preserves_epi_of_preserves_colimit CategoryTheory.preserves_epi_of_preservesColimit
-/

#print CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape /-
instance (priority := 100) preservesEpimorphisms_of_preservesColimitsOfShape
    [PreservesColimitsOfShape WalkingSpan F] : F.PreservesEpimorphisms
    where preserves X Y f hf := preserves_epi_of_preserves_colimit F f
#align category_theory.preserves_epimorphisms_of_preserves_colimits_of_shape CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape
-/

#print CategoryTheory.reflects_epi_of_reflectsColimit /-
/-- If `F` reflects pushouts, then it reflects epimorphisms. -/
theorem reflects_epi_of_reflectsColimit {X Y : C} (f : X ⟶ Y) [ReflectsColimit (span f f) F]
    [Epi (F.map f)] : Epi f :=
  by
  have := pushout_cocone.is_colimit_mk_id_id (F.map f)
  simp_rw [← F.map_id] at this
  apply
    pushout_cocone.epi_of_is_colimit_mk_id_id _
      (is_colimit_of_is_colimit_pushout_cocone_map F _ this)
#align category_theory.reflects_epi_of_reflects_colimit CategoryTheory.reflects_epi_of_reflectsColimit
-/

#print CategoryTheory.reflectsEpimorphisms_of_reflectsColimitsOfShape /-
instance (priority := 100) reflectsEpimorphisms_of_reflectsColimitsOfShape
    [ReflectsColimitsOfShape WalkingSpan F] : F.ReflectsEpimorphisms
    where reflects X Y f hf := reflects_epi_of_reflects_colimit F f
#align category_theory.reflects_epimorphisms_of_reflects_colimits_of_shape CategoryTheory.reflectsEpimorphisms_of_reflectsColimitsOfShape
-/

end CategoryTheory

