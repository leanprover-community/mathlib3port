/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module category_theory.idempotents.functor_extension
! leanprover-community/mathlib commit 19cb3751e5e9b3d97adb51023949c50c13b5fdfd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Idempotents.Karoubi

/-!
# Extension of functors to the idempotent completion

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we construct an extension `functor_extension₁`
of functors `C ⥤ karoubi D` to functors `karoubi C ⥤ karoubi D`. This results in an
equivalence `karoubi_universal₁ C D : (C ⥤ karoubi D) ≌ (karoubi C ⥤ karoubi D)`.

We also construct an extension `functor_extension₂` of functors
`(C ⥤ D) ⥤ (karoubi C ⥤ karoubi D)`. Moreover,
when `D` is idempotent complete, we get equivalences
`karoubi_universal₂ C D : C ⥤ D ≌ karoubi C ⥤ karoubi D`
and `karoubi_universal C D : C ⥤ D ≌ karoubi C ⥤ D`.

We occasionally state and use equalities of functors because it is
sometimes convenient to use rewrites when proving properties of
functors obtained using the constructions in this file. Users are
encouraged to use the corresponding natural isomorphism
whenever possible.

-/


open CategoryTheory.Category

open CategoryTheory.Idempotents.Karoubi

namespace CategoryTheory

namespace Idempotents

variable {C D E : Type _} [Category C] [Category D] [Category E]

/- warning: category_theory.idempotents.nat_trans_eq -> CategoryTheory.Idempotents.natTrans_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.nat_trans_eq CategoryTheory.Idempotents.natTrans_eqₓ'. -/
/-- A natural transformation between functors `karoubi C ⥤ D` is determined
by its value on objects coming from `C`. -/
theorem natTrans_eq {F G : Karoubi C ⥤ D} (φ : F ⟶ G) (P : Karoubi C) :
    φ.app P = F.map (decompId_i P) ≫ φ.app P.pt ≫ G.map (decompId_p P) :=
  by
  rw [← φ.naturality, ← assoc, ← F.map_comp]
  conv =>
    lhs
    rw [← id_comp (φ.app P), ← F.map_id]
  congr
  apply decomp_id
#align category_theory.idempotents.nat_trans_eq CategoryTheory.Idempotents.natTrans_eq

namespace FunctorExtension₁

/- warning: category_theory.idempotents.functor_extension₁.obj -> CategoryTheory.Idempotents.FunctorExtension₁.obj is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D], (CategoryTheory.Functor.{u3, u4, u1, max u2 u4} C _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} D _inst_2)) -> (CategoryTheory.Functor.{u3, u4, max u1 u3, max u2 u4} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} D _inst_2))
but is expected to have type
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D], (CategoryTheory.Functor.{u3, u4, u1, max u4 u2} C _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u2, u4} D _inst_2)) -> (CategoryTheory.Functor.{u3, u4, max u3 u1, max u4 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u2, u4} D _inst_2))
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.functor_extension₁.obj CategoryTheory.Idempotents.FunctorExtension₁.objₓ'. -/
/-- The canonical extension of a functor `C ⥤ karoubi D` to a functor
`karoubi C ⥤ karoubi D` -/
@[simps]
def obj (F : C ⥤ Karoubi D) : Karoubi C ⥤ Karoubi D
    where
  obj P :=
    ⟨(F.obj P.pt).pt, (F.map P.p).f, by simpa only [F.map_comp, hom_ext] using F.congr_map P.idem⟩
  map P Q f := ⟨(F.map f.f).f, by simpa only [F.map_comp, hom_ext] using F.congr_map f.comm⟩
#align category_theory.idempotents.functor_extension₁.obj CategoryTheory.Idempotents.FunctorExtension₁.obj

/- warning: category_theory.idempotents.functor_extension₁.map -> CategoryTheory.Idempotents.FunctorExtension₁.map is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] {F : CategoryTheory.Functor.{u3, u4, u1, max u2 u4} C _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} D _inst_2)} {G : CategoryTheory.Functor.{u3, u4, u1, max u2 u4} C _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} D _inst_2)}, (Quiver.Hom.{succ (max u1 u4), max u3 u4 u1 u2 u4} (CategoryTheory.Functor.{u3, u4, u1, max u2 u4} C _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} D _inst_2)) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u4, max u3 u4 u1 u2 u4} (CategoryTheory.Functor.{u3, u4, u1, max u2 u4} C _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} D _inst_2)) (CategoryTheory.Category.toCategoryStruct.{max u1 u4, max u3 u4 u1 u2 u4} (CategoryTheory.Functor.{u3, u4, u1, max u2 u4} C _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} D _inst_2)) (CategoryTheory.Functor.category.{u3, u4, u1, max u2 u4} C _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} D _inst_2)))) F G) -> (Quiver.Hom.{succ (max (max u1 u3) u4), max u3 u4 (max u1 u3) u2 u4} (CategoryTheory.Functor.{u3, u4, max u1 u3, max u2 u4} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} D _inst_2)) (CategoryTheory.CategoryStruct.toQuiver.{max (max u1 u3) u4, max u3 u4 (max u1 u3) u2 u4} (CategoryTheory.Functor.{u3, u4, max u1 u3, max u2 u4} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} D _inst_2)) (CategoryTheory.Category.toCategoryStruct.{max (max u1 u3) u4, max u3 u4 (max u1 u3) u2 u4} (CategoryTheory.Functor.{u3, u4, max u1 u3, max u2 u4} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} D _inst_2)) (CategoryTheory.Functor.category.{u3, u4, max u1 u3, max u2 u4} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} D _inst_2)))) (CategoryTheory.Idempotents.FunctorExtension₁.obj.{u1, u2, u3, u4} C D _inst_1 _inst_2 F) (CategoryTheory.Idempotents.FunctorExtension₁.obj.{u1, u2, u3, u4} C D _inst_1 _inst_2 G))
but is expected to have type
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] {F : CategoryTheory.Functor.{u3, u4, u1, max u4 u2} C _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u2, u4} D _inst_2)} {G : CategoryTheory.Functor.{u3, u4, u1, max u4 u2} C _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u2, u4} D _inst_2)}, (Quiver.Hom.{max (succ u1) (succ u4), max (max (max u1 u2) u3) u4} (CategoryTheory.Functor.{u3, u4, u1, max u4 u2} C _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u2, u4} D _inst_2)) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u4, max (max (max u1 u2) u3) u4} (CategoryTheory.Functor.{u3, u4, u1, max u4 u2} C _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u2, u4} D _inst_2)) (CategoryTheory.Category.toCategoryStruct.{max u1 u4, max (max (max u1 u2) u3) u4} (CategoryTheory.Functor.{u3, u4, u1, max u4 u2} C _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u2, u4} D _inst_2)) (CategoryTheory.Functor.category.{u3, u4, u1, max u2 u4} C _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u2, u4} D _inst_2)))) F G) -> (Quiver.Hom.{max (max (succ u1) (succ u3)) (succ u4), max (max (max u4 u3) u2) u1} (CategoryTheory.Functor.{u3, u4, max u3 u1, max u4 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u2, u4} D _inst_2)) (CategoryTheory.CategoryStruct.toQuiver.{max (max u1 u3) u4, max (max (max u1 u2) u3) u4} (CategoryTheory.Functor.{u3, u4, max u3 u1, max u4 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u2, u4} D _inst_2)) (CategoryTheory.Category.toCategoryStruct.{max (max u1 u3) u4, max (max (max u1 u2) u3) u4} (CategoryTheory.Functor.{u3, u4, max u3 u1, max u4 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u2, u4} D _inst_2)) (CategoryTheory.Functor.category.{u3, u4, max u1 u3, max u2 u4} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u2, u4} D _inst_2)))) (CategoryTheory.Idempotents.FunctorExtension₁.obj.{u1, u2, u3, u4} C D _inst_1 _inst_2 F) (CategoryTheory.Idempotents.FunctorExtension₁.obj.{u1, u2, u3, u4} C D _inst_1 _inst_2 G))
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.functor_extension₁.map CategoryTheory.Idempotents.FunctorExtension₁.mapₓ'. -/
/-- Extension of a natural transformation `φ` between functors
`C ⥤ karoubi D` to a natural transformation between the
extension of these functors to `karoubi C ⥤ karoubi D` -/
@[simps]
def map {F G : C ⥤ Karoubi D} (φ : F ⟶ G) : obj F ⟶ obj G
    where
  app P :=
    { f := (F.map P.p).f ≫ (φ.app P.pt).f
      comm := by
        have h := φ.naturality P.p
        have h' := F.congr_map P.idem
        simp only [hom_ext, karoubi.comp_f, F.map_comp] at h h'
        simp only [obj_obj_p, assoc, ← h]
        slice_rhs 1 3 => rw [h', h'] }
  naturality' P Q f := by
    ext
    dsimp [obj]
    have h := φ.naturality f.f
    have h' := F.congr_map (comp_p f)
    have h'' := F.congr_map (p_comp f)
    simp only [hom_ext, functor.map_comp, comp_f] at h h' h''⊢
    slice_rhs 2 3 => rw [← h]
    slice_lhs 1 2 => rw [h']
    slice_rhs 1 2 => rw [h'']
#align category_theory.idempotents.functor_extension₁.map CategoryTheory.Idempotents.FunctorExtension₁.map

end FunctorExtension₁

variable (C D E)

/- warning: category_theory.idempotents.functor_extension₁ -> CategoryTheory.Idempotents.functorExtension₁ is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u1}) (D : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D], CategoryTheory.Functor.{max u1 u4, max (max u1 u3) u4, max u3 u4 u1 u2 u4, max u3 u4 (max u1 u3) u2 u4} (CategoryTheory.Functor.{u3, u4, u1, max u2 u4} C _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} D _inst_2)) (CategoryTheory.Functor.category.{u3, u4, u1, max u2 u4} C _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} D _inst_2)) (CategoryTheory.Functor.{u3, u4, max u1 u3, max u2 u4} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} D _inst_2)) (CategoryTheory.Functor.category.{u3, u4, max u1 u3, max u2 u4} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} D _inst_2))
but is expected to have type
  forall (C : Type.{u1}) (D : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D], CategoryTheory.Functor.{max u1 u4, max (max u1 u3) u4, max (max (max (max u4 u2) u1) u4) u3, max (max (max (max u4 u2) u3 u1) u4) u3} (CategoryTheory.Functor.{u3, u4, u1, max u4 u2} C _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u2, u4} D _inst_2)) (CategoryTheory.Functor.category.{u3, u4, u1, max u2 u4} C _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u2, u4} D _inst_2)) (CategoryTheory.Functor.{u3, u4, max u3 u1, max u4 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u2, u4} D _inst_2)) (CategoryTheory.Functor.category.{u3, u4, max u1 u3, max u2 u4} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u2, u4} D _inst_2))
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.functor_extension₁ CategoryTheory.Idempotents.functorExtension₁ₓ'. -/
/-- The canonical functor `(C ⥤ karoubi D) ⥤ (karoubi C ⥤ karoubi D)` -/
@[simps]
def functorExtension₁ : (C ⥤ Karoubi D) ⥤ Karoubi C ⥤ Karoubi D
    where
  obj := FunctorExtension₁.obj
  map F G := FunctorExtension₁.map
  map_id' F := by ext P; exact comp_p (F.map P.p)
  map_comp' F G H φ φ' := by
    ext P
    simp only [comp_f, functor_extension₁.map_app_f, nat_trans.comp_app, assoc]
    have h := φ.naturality P.p
    have h' := F.congr_map P.idem
    simp only [hom_ext, comp_f, F.map_comp] at h h'
    slice_rhs 2 3 => rw [← h]
    slice_rhs 1 2 => rw [h']
    simp only [assoc]
#align category_theory.idempotents.functor_extension₁ CategoryTheory.Idempotents.functorExtension₁

/- warning: category_theory.idempotents.functor_extension₁_comp_whiskering_left_to_karoubi -> CategoryTheory.Idempotents.functorExtension₁_comp_whiskeringLeft_toKaroubi is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.functor_extension₁_comp_whiskering_left_to_karoubi CategoryTheory.Idempotents.functorExtension₁_comp_whiskeringLeft_toKaroubiₓ'. -/
theorem functorExtension₁_comp_whiskeringLeft_toKaroubi :
    functorExtension₁ C D ⋙ (whiskeringLeft C (Karoubi C) (Karoubi D)).obj (toKaroubi C) = 𝟭 _ :=
  by
  refine' Functor.ext _ _
  · intro F
    refine' Functor.ext _ _
    · intro X
      ext
      · dsimp
        rw [id_comp, comp_id, F.map_id, id_eq]
      · rfl
    · intro X Y f
      ext
      dsimp
      simp only [comp_id, eq_to_hom_f, eq_to_hom_refl, comp_p, functor_extension₁.obj_obj_p,
        to_karoubi_obj_p, comp_f]
      dsimp
      simp only [Functor.map_id, id_eq, p_comp]
  · intro F G φ
    ext X
    dsimp
    simp only [eq_to_hom_app, F.map_id, comp_f, eq_to_hom_f, id_eq, p_comp, eq_to_hom_refl, comp_id,
      comp_p, functor_extension₁.obj_obj_p, to_karoubi_obj_p, F.map_id X]
#align category_theory.idempotents.functor_extension₁_comp_whiskering_left_to_karoubi CategoryTheory.Idempotents.functorExtension₁_comp_whiskeringLeft_toKaroubi

/- warning: category_theory.idempotents.functor_extension₁_comp_whiskering_left_to_karoubi_iso -> CategoryTheory.Idempotents.functorExtension₁_comp_whiskeringLeft_toKaroubi_iso is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.functor_extension₁_comp_whiskering_left_to_karoubi_iso CategoryTheory.Idempotents.functorExtension₁_comp_whiskeringLeft_toKaroubi_isoₓ'. -/
/-- The natural isomorphism expressing that functors `karoubi C ⥤ karoubi D` obtained
using `functor_extension₁` actually extends the original functors `C ⥤ karoubi D`. -/
@[simps]
def functorExtension₁_comp_whiskeringLeft_toKaroubi_iso :
    functorExtension₁ C D ⋙ (whiskeringLeft C (Karoubi C) (Karoubi D)).obj (toKaroubi C) ≅ 𝟭 _ :=
  eqToIso (functorExtension₁_comp_whiskeringLeft_toKaroubi C D)
#align category_theory.idempotents.functor_extension₁_comp_whiskering_left_to_karoubi_iso CategoryTheory.Idempotents.functorExtension₁_comp_whiskeringLeft_toKaroubi_iso

/- warning: category_theory.idempotents.karoubi_universal₁.counit_iso -> CategoryTheory.Idempotents.KaroubiUniversal₁.counitIso is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.karoubi_universal₁.counit_iso CategoryTheory.Idempotents.KaroubiUniversal₁.counitIsoₓ'. -/
/-- The counit isomorphism of the equivalence `(C ⥤ karoubi D) ≌ (karoubi C ⥤ karoubi D)`. -/
@[simps]
def KaroubiUniversal₁.counitIso :
    (whiskeringLeft C (Karoubi C) (Karoubi D)).obj (toKaroubi C) ⋙ functorExtension₁ C D ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun G =>
      { Hom :=
          { app := fun P =>
              { f := (G.map (decompId_p P)).f
                comm := by
                  simpa only [hom_ext, G.map_comp, G.map_id] using
                    G.congr_map
                      (show P.decomp_id_p = (to_karoubi C).map P.p ≫ P.decomp_id_p ≫ 𝟙 _ by simp) }
            naturality' := fun P Q f => by
              simpa only [hom_ext, G.map_comp] using (G.congr_map (decomp_id_p_naturality f)).symm }
        inv :=
          { app := fun P =>
              { f := (G.map (decompId_i P)).f
                comm := by
                  simpa only [hom_ext, G.map_comp, G.map_id] using
                    G.congr_map
                      (show P.decomp_id_i = 𝟙 _ ≫ P.decomp_id_i ≫ (to_karoubi C).map P.p by simp) }
            naturality' := fun P Q f => by
              simpa only [hom_ext, G.map_comp] using G.congr_map (decomp_id_i_naturality f) }
        hom_inv_id' := by
          ext P
          simpa only [hom_ext, G.map_comp, G.map_id] using G.congr_map P.decomp_p.symm
        inv_hom_id' := by
          ext P
          simpa only [hom_ext, G.map_comp, G.map_id] using G.congr_map P.decomp_id.symm })
    fun G₁ G₂ φ => by
    ext P
    dsimp
    simpa only [nat_trans_eq φ P, comp_f, functor_extension₁.map_app_f, functor.comp_map,
      whisker_left_app, assoc, P.decomp_p, G₁.map_comp]
#align category_theory.idempotents.karoubi_universal₁.counit_iso CategoryTheory.Idempotents.KaroubiUniversal₁.counitIso

/- warning: category_theory.idempotents.karoubi_universal₁ -> CategoryTheory.Idempotents.karoubiUniversal₁ is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u1}) (D : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D], CategoryTheory.Equivalence.{max u1 u4, max (max u1 u3) u4, max u3 u4 u1 u2 u4, max u3 u4 (max u1 u3) u2 u4} (CategoryTheory.Functor.{u3, u4, u1, max u2 u4} C _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} D _inst_2)) (CategoryTheory.Functor.category.{u3, u4, u1, max u2 u4} C _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} D _inst_2)) (CategoryTheory.Functor.{u3, u4, max u1 u3, max u2 u4} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} D _inst_2)) (CategoryTheory.Functor.category.{u3, u4, max u1 u3, max u2 u4} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} D _inst_2))
but is expected to have type
  forall (C : Type.{u1}) (D : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D], CategoryTheory.Equivalence.{max u1 u4, max (max u1 u3) u4, max (max (max (max u4 u2) u1) u4) u3, max (max (max (max u4 u2) u3 u1) u4) u3} (CategoryTheory.Functor.{u3, u4, u1, max u4 u2} C _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u2, u4} D _inst_2)) (CategoryTheory.Functor.{u3, u4, max u3 u1, max u4 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u2, u4} D _inst_2)) (CategoryTheory.Functor.category.{u3, u4, u1, max u2 u4} C _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u2, u4} D _inst_2)) (CategoryTheory.Functor.category.{u3, u4, max u1 u3, max u2 u4} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u2, u4} D _inst_2))
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.karoubi_universal₁ CategoryTheory.Idempotents.karoubiUniversal₁ₓ'. -/
/-- The equivalence of categories `(C ⥤ karoubi D) ≌ (karoubi C ⥤ karoubi D)`. -/
@[simps]
def karoubiUniversal₁ : C ⥤ Karoubi D ≌ Karoubi C ⥤ Karoubi D
    where
  Functor := functorExtension₁ C D
  inverse := (whiskeringLeft C (Karoubi C) (Karoubi D)).obj (toKaroubi C)
  unitIso := (functorExtension₁_comp_whiskeringLeft_toKaroubi_iso C D).symm
  counitIso := KaroubiUniversal₁.counitIso C D
  functor_unitIso_comp' F := by
    ext P
    dsimp [functor_extension₁.map, karoubi_universal₁.counit_iso]
    simpa only [comp_f, eq_to_hom_app, eq_to_hom_f, eq_to_hom_refl, comp_id, hom_ext, F.map_comp,
      comp_p] using F.congr_map P.idem
#align category_theory.idempotents.karoubi_universal₁ CategoryTheory.Idempotents.karoubiUniversal₁

/- warning: category_theory.idempotents.functor_extension₁_comp -> CategoryTheory.Idempotents.functorExtension₁_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.functor_extension₁_comp CategoryTheory.Idempotents.functorExtension₁_compₓ'. -/
theorem functorExtension₁_comp (F : C ⥤ Karoubi D) (G : D ⥤ Karoubi E) :
    (functorExtension₁ C E).obj (F ⋙ (functorExtension₁ D E).obj G) =
      (functorExtension₁ C D).obj F ⋙ (functorExtension₁ D E).obj G :=
  Functor.ext (by tidy) fun X Y f => by dsimp; simpa only [id_comp, comp_id]
#align category_theory.idempotents.functor_extension₁_comp CategoryTheory.Idempotents.functorExtension₁_comp

/- warning: category_theory.idempotents.functor_extension₂ -> CategoryTheory.Idempotents.functorExtension₂ is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u1}) (D : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D], CategoryTheory.Functor.{max u1 u4, max (max u1 u3) u4, max u3 u4 u1 u2, max u3 u4 (max u1 u3) u2 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.{u3, u4, max u1 u3, max u2 u4} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} D _inst_2)) (CategoryTheory.Functor.category.{u3, u4, max u1 u3, max u2 u4} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} D _inst_2))
but is expected to have type
  forall (C : Type.{u1}) (D : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D], CategoryTheory.Functor.{max u1 u4, max (max u1 u3) u4, max (max (max u2 u1) u4) u3, max (max (max (max u4 u2) u3 u1) u4) u3} (CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.{u3, u4, max u3 u1, max u4 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u2, u4} D _inst_2)) (CategoryTheory.Functor.category.{u3, u4, max u1 u3, max u2 u4} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u2, u4} D _inst_2))
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.functor_extension₂ CategoryTheory.Idempotents.functorExtension₂ₓ'. -/
/-- The canonical functor `(C ⥤ D) ⥤ (karoubi C ⥤ karoubi D)` -/
@[simps]
def functorExtension₂ : (C ⥤ D) ⥤ Karoubi C ⥤ Karoubi D :=
  (whiskeringRight C D (Karoubi D)).obj (toKaroubi D) ⋙ functorExtension₁ C D
#align category_theory.idempotents.functor_extension₂ CategoryTheory.Idempotents.functorExtension₂

/- warning: category_theory.idempotents.functor_extension₂_comp_whiskering_left_to_karoubi -> CategoryTheory.Idempotents.functorExtension₂_comp_whiskeringLeft_toKaroubi is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.functor_extension₂_comp_whiskering_left_to_karoubi CategoryTheory.Idempotents.functorExtension₂_comp_whiskeringLeft_toKaroubiₓ'. -/
theorem functorExtension₂_comp_whiskeringLeft_toKaroubi :
    functorExtension₂ C D ⋙ (whiskeringLeft C (Karoubi C) (Karoubi D)).obj (toKaroubi C) =
      (whiskeringRight C D (Karoubi D)).obj (toKaroubi D) :=
  by
  simp only [functor_extension₂, functor.assoc, functor_extension₁_comp_whiskering_left_to_karoubi,
    functor.comp_id]
#align category_theory.idempotents.functor_extension₂_comp_whiskering_left_to_karoubi CategoryTheory.Idempotents.functorExtension₂_comp_whiskeringLeft_toKaroubi

/- warning: category_theory.idempotents.functor_extension₂_comp_whiskering_left_to_karoubi_iso -> CategoryTheory.Idempotents.functorExtension₂CompWhiskeringLeftToKaroubiIso is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.functor_extension₂_comp_whiskering_left_to_karoubi_iso CategoryTheory.Idempotents.functorExtension₂CompWhiskeringLeftToKaroubiIsoₓ'. -/
/-- The natural isomorphism expressing that functors `karoubi C ⥤ karoubi D` obtained
using `functor_extension₂` actually extends the original functors `C ⥤ D`. -/
@[simps]
def functorExtension₂CompWhiskeringLeftToKaroubiIso :
    functorExtension₂ C D ⋙ (whiskeringLeft C (Karoubi C) (Karoubi D)).obj (toKaroubi C) ≅
      (whiskeringRight C D (Karoubi D)).obj (toKaroubi D) :=
  eqToIso (functorExtension₂_comp_whiskeringLeft_toKaroubi C D)
#align category_theory.idempotents.functor_extension₂_comp_whiskering_left_to_karoubi_iso CategoryTheory.Idempotents.functorExtension₂CompWhiskeringLeftToKaroubiIso

section IsIdempotentComplete

variable [IsIdempotentComplete D]

noncomputable instance : IsEquivalence (toKaroubi D) :=
  toKaroubi_isEquivalence D

/- warning: category_theory.idempotents.karoubi_universal₂ -> CategoryTheory.Idempotents.karoubiUniversal₂ is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u1}) (D : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] [_inst_4 : CategoryTheory.IsIdempotentComplete.{u2, u4} D _inst_2], CategoryTheory.Equivalence.{max u1 u4, max (max u1 u3) u4, max u3 u4 u1 u2, max u3 u4 (max u1 u3) u2 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.{u3, u4, max u1 u3, max u2 u4} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} D _inst_2)) (CategoryTheory.Functor.category.{u3, u4, max u1 u3, max u2 u4} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} D _inst_2))
but is expected to have type
  forall (C : Type.{u1}) (D : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] [_inst_4 : CategoryTheory.IsIdempotentComplete.{u2, u4} D _inst_2], CategoryTheory.Equivalence.{max u1 u4, max (max u1 u3) u4, max (max (max u2 u1) u4) u3, max (max (max (max u4 u2) u3 u1) u4) u3} (CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.{u3, u4, max u3 u1, max u4 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u2, u4} D _inst_2)) (CategoryTheory.Functor.category.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u3, u4, max u1 u3, max u2 u4} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u2, u4} D _inst_2))
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.karoubi_universal₂ CategoryTheory.Idempotents.karoubiUniversal₂ₓ'. -/
/-- The equivalence of categories `(C ⥤ D) ≌ (karoubi C ⥤ karoubi D)` when `D`
is idempotent complete. -/
@[simps]
noncomputable def karoubiUniversal₂ : C ⥤ D ≌ Karoubi C ⥤ Karoubi D :=
  (Equivalence.congrRight (toKaroubi D).asEquivalence).trans (karoubiUniversal₁ C D)
#align category_theory.idempotents.karoubi_universal₂ CategoryTheory.Idempotents.karoubiUniversal₂

/- warning: category_theory.idempotents.karoubi_universal₂_functor_eq -> CategoryTheory.Idempotents.karoubiUniversal₂_functor_eq is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u1}) (D : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] [_inst_4 : CategoryTheory.IsIdempotentComplete.{u2, u4} D _inst_2], Eq.{succ (max (max u1 u4) (max (max u1 u3) u4) (max u3 u4 u1 u2) u3 u4 (max u1 u3) u2 u4)} (CategoryTheory.Functor.{max u1 u4, max (max u1 u3) u4, max u3 u4 u1 u2, max u3 u4 (max u1 u3) u2 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.{u3, u4, max u1 u3, max u2 u4} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} D _inst_2)) (CategoryTheory.Functor.category.{u3, u4, max u1 u3, max u2 u4} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} D _inst_2))) (CategoryTheory.Equivalence.functor.{max u1 u4, max (max u1 u3) u4, max u3 u4 u1 u2, max u3 u4 (max u1 u3) u2 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.{u3, u4, max u1 u3, max u2 u4} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} D _inst_2)) (CategoryTheory.Functor.category.{u3, u4, max u1 u3, max u2 u4} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u2, u4} D _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} D _inst_2)) (CategoryTheory.Idempotents.karoubiUniversal₂.{u1, u2, u3, u4} C D _inst_1 _inst_2 _inst_4)) (CategoryTheory.Idempotents.functorExtension₂.{u1, u2, u3, u4} C D _inst_1 _inst_2)
but is expected to have type
  forall (C : Type.{u4}) (D : Type.{u3}) [_inst_1 : CategoryTheory.Category.{u2, u4} C] [_inst_2 : CategoryTheory.Category.{u1, u3} D] [_inst_4 : CategoryTheory.IsIdempotentComplete.{u3, u1} D _inst_2], Eq.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} (CategoryTheory.Functor.{max u4 u1, max (max u4 u2) u1, max (max (max u4 u3) u2) u1, max (max (max u4 u3) u2) u1} (CategoryTheory.Functor.{u2, u1, u4, u3} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u2, u1, u4, u3} C _inst_1 D _inst_2) (CategoryTheory.Functor.{u2, u1, max u2 u4, max u1 u3} (CategoryTheory.Idempotents.Karoubi.{u4, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u4, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u3, u1} D _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u3, u1} D _inst_2)) (CategoryTheory.Functor.category.{u2, u1, max u4 u2, max u3 u1} (CategoryTheory.Idempotents.Karoubi.{u4, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u4, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u3, u1} D _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u3, u1} D _inst_2))) (CategoryTheory.Equivalence.functor.{max u4 u1, max (max u4 u2) u1, max (max (max u4 u3) u2) u1, max (max (max u4 u3) u2) u1} (CategoryTheory.Functor.{u2, u1, u4, u3} C _inst_1 D _inst_2) (CategoryTheory.Functor.{u2, u1, max u2 u4, max u1 u3} (CategoryTheory.Idempotents.Karoubi.{u4, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u4, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u3, u1} D _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u3, u1} D _inst_2)) (CategoryTheory.Functor.category.{u2, u1, u4, u3} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u2, u1, max u4 u2, max u3 u1} (CategoryTheory.Idempotents.Karoubi.{u4, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u4, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u3, u1} D _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u3, u1} D _inst_2)) (CategoryTheory.Idempotents.karoubiUniversal₂.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_4)) (CategoryTheory.Idempotents.functorExtension₂.{u4, u3, u2, u1} C D _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.karoubi_universal₂_functor_eq CategoryTheory.Idempotents.karoubiUniversal₂_functor_eqₓ'. -/
theorem karoubiUniversal₂_functor_eq : (karoubiUniversal₂ C D).Functor = functorExtension₂ C D :=
  rfl
#align category_theory.idempotents.karoubi_universal₂_functor_eq CategoryTheory.Idempotents.karoubiUniversal₂_functor_eq

noncomputable instance : IsEquivalence (functorExtension₂ C D) := by
  rw [← karoubi_universal₂_functor_eq]; infer_instance

/- warning: category_theory.idempotents.functor_extension -> CategoryTheory.Idempotents.functorExtension is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u1}) (D : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] [_inst_4 : CategoryTheory.IsIdempotentComplete.{u2, u4} D _inst_2], CategoryTheory.Functor.{max u1 u4, max (max u1 u3) u4, max u3 u4 u1 u2, max u3 u4 (max u1 u3) u2} (CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.{u3, u4, max u1 u3, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u3, u4, max u1 u3, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u3} C _inst_1) D _inst_2)
but is expected to have type
  forall (C : Type.{u1}) (D : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] [_inst_4 : CategoryTheory.IsIdempotentComplete.{u2, u4} D _inst_2], CategoryTheory.Functor.{max u1 u4, max (max u1 u3) u4, max (max (max u2 u1) u4) u3, max (max (max u2 u3 u1) u4) u3} (CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.{u3, u4, max u3 u1, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u3, u4, max u1 u3, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u3} C _inst_1) D _inst_2)
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.functor_extension CategoryTheory.Idempotents.functorExtensionₓ'. -/
/-- The extension of functors functor `(C ⥤ D) ⥤ (karoubi C ⥤ D)`
when `D` is idempotent compltete. -/
@[simps]
noncomputable def functorExtension : (C ⥤ D) ⥤ Karoubi C ⥤ D :=
  functorExtension₂ C D ⋙
    (whiskeringRight (Karoubi C) (Karoubi D) D).obj (toKaroubi_isEquivalence D).inverse
#align category_theory.idempotents.functor_extension CategoryTheory.Idempotents.functorExtension

/- warning: category_theory.idempotents.karoubi_universal -> CategoryTheory.Idempotents.karoubiUniversal is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u1}) (D : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] [_inst_4 : CategoryTheory.IsIdempotentComplete.{u2, u4} D _inst_2], CategoryTheory.Equivalence.{max u1 u4, max (max u1 u3) u4, max u3 u4 u1 u2, max u3 u4 (max u1 u3) u2} (CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.{u3, u4, max u1 u3, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u3, u4, max u1 u3, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u3} C _inst_1) D _inst_2)
but is expected to have type
  forall (C : Type.{u1}) (D : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] [_inst_4 : CategoryTheory.IsIdempotentComplete.{u2, u4} D _inst_2], CategoryTheory.Equivalence.{max u1 u4, max (max u1 u3) u4, max (max (max u2 u1) u4) u3, max (max (max u2 u3 u1) u4) u3} (CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.{u3, u4, max u3 u1, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u3, u4, max u1 u3, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u3} C _inst_1) D _inst_2)
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.karoubi_universal CategoryTheory.Idempotents.karoubiUniversalₓ'. -/
/-- The equivalence `(C ⥤ D) ≌ (karoubi C ⥤ D)` when `D` is idempotent complete. -/
@[simps]
noncomputable def karoubiUniversal : C ⥤ D ≌ Karoubi C ⥤ D :=
  (karoubiUniversal₂ C D).trans (Equivalence.congrRight (toKaroubi D).asEquivalence.symm)
#align category_theory.idempotents.karoubi_universal CategoryTheory.Idempotents.karoubiUniversal

/- warning: category_theory.idempotents.karoubi_universal_functor_eq -> CategoryTheory.Idempotents.karoubiUniversal_functor_eq is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u1}) (D : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] [_inst_4 : CategoryTheory.IsIdempotentComplete.{u2, u4} D _inst_2], Eq.{succ (max (max u1 u4) (max (max u1 u3) u4) (max u3 u4 u1 u2) u3 u4 (max u1 u3) u2)} (CategoryTheory.Functor.{max u1 u4, max (max u1 u3) u4, max u3 u4 u1 u2, max u3 u4 (max u1 u3) u2} (CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.{u3, u4, max u1 u3, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u3, u4, max u1 u3, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u3} C _inst_1) D _inst_2)) (CategoryTheory.Equivalence.functor.{max u1 u4, max (max u1 u3) u4, max u3 u4 u1 u2, max u3 u4 (max u1 u3) u2} (CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} C _inst_1 D _inst_2) (CategoryTheory.Functor.{u3, u4, max u1 u3, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u3} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u3, u4, max u1 u3, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u3} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u3} C _inst_1) D _inst_2) (CategoryTheory.Idempotents.karoubiUniversal.{u1, u2, u3, u4} C D _inst_1 _inst_2 _inst_4)) (CategoryTheory.Idempotents.functorExtension.{u1, u2, u3, u4} C D _inst_1 _inst_2 _inst_4)
but is expected to have type
  forall (C : Type.{u4}) (D : Type.{u3}) [_inst_1 : CategoryTheory.Category.{u2, u4} C] [_inst_2 : CategoryTheory.Category.{u1, u3} D] [_inst_4 : CategoryTheory.IsIdempotentComplete.{u3, u1} D _inst_2], Eq.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} (CategoryTheory.Functor.{max u4 u1, max (max u4 u2) u1, max (max (max u4 u3) u2) u1, max (max (max u4 u3) u2) u1} (CategoryTheory.Functor.{u2, u1, u4, u3} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u2, u1, u4, u3} C _inst_1 D _inst_2) (CategoryTheory.Functor.{u2, u1, max u2 u4, u3} (CategoryTheory.Idempotents.Karoubi.{u4, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u4, u2} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, u1, max u4 u2, u3} (CategoryTheory.Idempotents.Karoubi.{u4, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u4, u2} C _inst_1) D _inst_2)) (CategoryTheory.Equivalence.functor.{max u4 u1, max (max u4 u2) u1, max (max (max u4 u3) u2) u1, max (max (max u4 u3) u2) u1} (CategoryTheory.Functor.{u2, u1, u4, u3} C _inst_1 D _inst_2) (CategoryTheory.Functor.{u2, u1, max u2 u4, u3} (CategoryTheory.Idempotents.Karoubi.{u4, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u4, u2} C _inst_1) D _inst_2) (CategoryTheory.Functor.category.{u2, u1, u4, u3} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u2, u1, max u4 u2, u3} (CategoryTheory.Idempotents.Karoubi.{u4, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u4, u2} C _inst_1) D _inst_2) (CategoryTheory.Idempotents.karoubiUniversal.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_4)) (CategoryTheory.Idempotents.functorExtension.{u4, u3, u2, u1} C D _inst_1 _inst_2 _inst_4)
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.karoubi_universal_functor_eq CategoryTheory.Idempotents.karoubiUniversal_functor_eqₓ'. -/
theorem karoubiUniversal_functor_eq : (karoubiUniversal C D).Functor = functorExtension C D :=
  rfl
#align category_theory.idempotents.karoubi_universal_functor_eq CategoryTheory.Idempotents.karoubiUniversal_functor_eq

noncomputable instance : IsEquivalence (functorExtension C D) := by
  rw [← karoubi_universal_functor_eq]; infer_instance

noncomputable instance : IsEquivalence ((whiskeringLeft C (Karoubi C) D).obj (toKaroubi C)) :=
  IsEquivalence.cancelCompRight _
    ((whiskeringRight C _ _).obj (toKaroubi D) ⋙ (whiskeringRight C _ _).obj (toKaroubi D).inv)
    (IsEquivalence.ofEquivalence
      (@Equivalence.congrRight _ _ _ _ C _
        ((toKaroubi D).asEquivalence.trans (toKaroubi D).asEquivalence.symm)))
    (by change is_equivalence (karoubi_universal C D).inverse; infer_instance)

variable {C D}

/- warning: category_theory.idempotents.whiskering_left_obj_preimage_app -> CategoryTheory.Idempotents.whiskeringLeft_obj_preimage_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.whiskering_left_obj_preimage_app CategoryTheory.Idempotents.whiskeringLeft_obj_preimage_appₓ'. -/
theorem whiskeringLeft_obj_preimage_app {F G : Karoubi C ⥤ D}
    (τ : toKaroubi _ ⋙ F ⟶ toKaroubi _ ⋙ G) (P : Karoubi C) :
    (((whiskeringLeft _ _ _).obj (toKaroubi _)).preimage τ).app P =
      F.map P.decompId_i ≫ τ.app P.pt ≫ G.map P.decompId_p :=
  by
  rw [nat_trans_eq]
  congr 2
  exact congr_app (((whiskering_left _ _ _).obj (to_karoubi _)).image_preimage τ) P.X
#align category_theory.idempotents.whiskering_left_obj_preimage_app CategoryTheory.Idempotents.whiskeringLeft_obj_preimage_app

end IsIdempotentComplete

end Idempotents

end CategoryTheory

