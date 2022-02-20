/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Relating monomorphisms and epimorphisms to limits and colimits

If `F` preserves (resp. reflects) pullbacks, then it preserves (resp. reflects) monomorphisms.

We also provide the dual version for epimorphisms.

-/


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

variable (F : C ⥤ D)

/-- If `F` preserves pullbacks, then it preserves monomorphisms. -/
instance preserves_mono {X Y : C} (f : X ⟶ Y) [PreservesLimit (cospan f f) F] [Mono f] : Mono (F.map f) := by
  have := is_limit_pullback_cone_map_of_is_limit F _ (pullback_cone.is_limit_mk_id_id f)
  simp_rw [F.map_id]  at this
  apply pullback_cone.mono_of_is_limit_mk_id_id _ this

/-- If `F` reflects pullbacks, then it reflects monomorphisms. -/
theorem reflects_mono {X Y : C} (f : X ⟶ Y) [ReflectsLimit (cospan f f) F] [Mono (F.map f)] : Mono f := by
  have := pullback_cone.is_limit_mk_id_id (F.map f)
  simp_rw [← F.map_id]  at this
  apply pullback_cone.mono_of_is_limit_mk_id_id _ (is_limit_of_is_limit_pullback_cone_map F _ this)

/-- If `F` preserves pushouts, then it preserves epimorphisms. -/
instance preserves_epi {X Y : C} (f : X ⟶ Y) [PreservesColimit (span f f) F] [Epi f] : Epi (F.map f) := by
  have := is_colimit_pushout_cocone_map_of_is_colimit F _ (pushout_cocone.is_colimit_mk_id_id f)
  simp_rw [F.map_id]  at this
  apply pushout_cocone.epi_of_is_colimit_mk_id_id _ this

/-- If `F` reflects pushouts, then it reflects epimorphisms. -/
theorem reflects_epi {X Y : C} (f : X ⟶ Y) [ReflectsColimit (span f f) F] [Epi (F.map f)] : Epi f := by
  have := pushout_cocone.is_colimit_mk_id_id (F.map f)
  simp_rw [← F.map_id]  at this
  apply pushout_cocone.epi_of_is_colimit_mk_id_id _ (is_colimit_of_is_colimit_pushout_cocone_map F _ this)

end CategoryTheory

