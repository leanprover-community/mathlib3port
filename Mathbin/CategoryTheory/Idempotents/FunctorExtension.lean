/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathbin.CategoryTheory.Idempotents.Karoubi
import Mathbin.CategoryTheory.NaturalIsomorphism

/-!
# Extension of functors to the idempotent completion

In this file, we construct an extension `functor_extension₁`
of functors `C ⥤ karoubi D` to functors `karoubi C ⥤ karoubi D`.

TODO : Obtain the equivalences
`karoubi_universal₁ C D : C ⥤ karoubi D ≌ karoubi C ⥤ karoubi D`
for all categories, and
`karoubi_universal C D : C ⥤ D ≌ karoubi C ⥤ D`.
when `D` is idempotent complete
-/


open CategoryTheory.Category

open CategoryTheory.Idempotents.Karoubi

namespace CategoryTheory

namespace Idempotents

variable {C D E : Type _} [Category C] [Category D] [Category E]

/-- A natural transformation between functors `karoubi C ⥤ D` is determined
by its value on objects coming from `C`. -/
theorem nat_trans_eq {F G : Karoubi C ⥤ D} (φ : F ⟶ G) (P : Karoubi C) :
    φ.app P = F.map (decompIdI P) ≫ φ.app P.x ≫ G.map (decompIdP P) := by
  rw [← φ.naturality, ← assoc, ← F.map_comp]
  conv => lhs rw [← id_comp (φ.app P), ← F.map_id]
  congr
  apply decomp_id

namespace FunctorExtension₁

/-- The canonical extension of a functor `C ⥤ karoubi D` to a functor
`karoubi C ⥤ karoubi D` -/
@[simps]
def obj (F : C ⥤ Karoubi D) : Karoubi C ⥤ Karoubi D where
  obj := fun P =>
    ⟨(F.obj P.x).x, (F.map P.p).f, by
      simpa only [← F.map_comp, ← hom_ext] using F.congr_map P.idem⟩
  map := fun P Q f =>
    ⟨(F.map f.f).f, by
      simpa only [← F.map_comp, ← hom_ext] using F.congr_map f.comm⟩

/-- Extension of a natural transformation `φ` between functors
`C ⥤ karoubi D` to a natural transformation between the
extension of these functors to `karoubi C ⥤ karoubi D` -/
@[simps]
def map {F G : C ⥤ Karoubi D} (φ : F ⟶ G) : obj F ⟶ obj G where
  app := fun P =>
    { f := (F.map P.p).f ≫ (φ.app P.x).f,
      comm := by
        have h := φ.naturality P.p
        have h' := F.congr_map P.idem
        simp only [← hom_ext, ← karoubi.comp, ← F.map_comp] at h h'
        simp only [← obj_obj_p, ← assoc, h]
        slice_rhs 1 3 => rw [h', h'] }
  naturality' := fun P Q f => by
    ext
    dsimp' [← obj]
    have h := φ.naturality f.f
    have h' := F.congr_map (comp_p f)
    have h'' := F.congr_map (p_comp f)
    simp only [← hom_ext, ← functor.map_comp, ← comp] at h h' h''⊢
    slice_rhs 2 3 => rw [← h]
    slice_lhs 1 2 => rw [h']
    slice_rhs 1 2 => rw [h'']

end FunctorExtension₁

variable (C D E)

/-- The canonical functor `(C ⥤ karoubi D) ⥤ (karoubi C ⥤ karoubi D)` -/
@[simps]
def functorExtension₁ : (C ⥤ Karoubi D) ⥤ Karoubi C ⥤ Karoubi D where
  obj := FunctorExtension₁.obj
  map := fun F G => FunctorExtension₁.map
  map_id' := fun F => by
    ext P
    exact comp_p (F.map P.p)
  map_comp' := fun F G H φ φ' => by
    ext P
    simp only [← comp, ← functor_extension₁.map_app_f, ← nat_trans.comp_app, ← assoc]
    have h := φ.naturality P.p
    have h' := F.congr_map P.idem
    simp only [← hom_ext, ← comp, ← F.map_comp] at h h'
    slice_rhs 2 3 => rw [← h]
    slice_rhs 1 2 => rw [h']
    simp only [← assoc]

theorem functor_extension₁_comp_whiskering_left_to_karoubi :
    functorExtension₁ C D ⋙ (whiskeringLeft C (Karoubi C) (Karoubi D)).obj (toKaroubi C) = 𝟭 _ := by
  refine' Functor.ext _ _
  · intro F
    refine' Functor.ext _ _
    · intro X
      ext
      · dsimp'
        rw [id_comp, comp_id, F.map_id, id_eq]
        
      · rfl
        
      
    · intro X Y f
      ext
      dsimp'
      simp only [← comp_id, ← eq_to_hom_f, ← eq_to_hom_refl, ← comp_p, ← functor_extension₁.obj_obj_p, ←
        to_karoubi_obj_p, ← comp]
      dsimp'
      simp only [← Functor.map_id, ← id_eq, ← p_comp]
      
    
  · intro F G φ
    ext X
    dsimp'
    simp only [← eq_to_hom_app, ← F.map_id, ← karoubi.comp, ← eq_to_hom_f, ← id_eq, ← p_comp, ← eq_to_hom_refl, ←
      comp_id, ← comp_p, ← functor_extension₁.obj_obj_p, ← to_karoubi_obj_p, ← F.map_id X]
    

end Idempotents

end CategoryTheory

