/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module category_theory.idempotents.functor_categories
! leanprover-community/mathlib commit 19cb3751e5e9b3d97adb51023949c50c13b5fdfd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Idempotents.Karoubi

/-!
# Idempotent completeness and functor categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define an instance `functor_category_is_idempotent_complete` expressing
that a functor category `J ⥤ C` is idempotent complete when the target category `C` is.

We also provide a fully faithful functor
`karoubi_functor_category_embedding : karoubi (J ⥤ C)) : J ⥤ karoubi C` for all categories
`J` and `C`.

-/


open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Idempotents.Karoubi

open CategoryTheory.Limits

namespace CategoryTheory

namespace Idempotents

variable {J C : Type _} [Category J] [Category C] (P Q : Karoubi (J ⥤ C)) (f : P ⟶ Q) (X : J)

/- warning: category_theory.idempotents.app_idem -> CategoryTheory.Idempotents.app_idem is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} J] [_inst_2 : CategoryTheory.Category.{u4, u2} C] (P : CategoryTheory.Idempotents.Karoubi.{max u3 u4 u1 u2, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2)) (X : J), Eq.{succ u4} (Quiver.Hom.{succ u4, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} C (CategoryTheory.Category.toCategoryStruct.{u4, u2} C _inst_2)) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} J _inst_1 C _inst_2 (CategoryTheory.Idempotents.Karoubi.x.{max u3 u4 u1 u2, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2) P) X) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} J _inst_1 C _inst_2 (CategoryTheory.Idempotents.Karoubi.x.{max u3 u4 u1 u2, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2) P) X)) (CategoryTheory.CategoryStruct.comp.{u4, u2} C (CategoryTheory.Category.toCategoryStruct.{u4, u2} C _inst_2) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} J _inst_1 C _inst_2 (CategoryTheory.Idempotents.Karoubi.x.{max u3 u4 u1 u2, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2) P) X) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} J _inst_1 C _inst_2 (CategoryTheory.Idempotents.Karoubi.x.{max u3 u4 u1 u2, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2) P) X) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} J _inst_1 C _inst_2 (CategoryTheory.Idempotents.Karoubi.x.{max u3 u4 u1 u2, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2) P) X) (CategoryTheory.NatTrans.app.{u3, u4, u1, u2} J _inst_1 C _inst_2 (CategoryTheory.Idempotents.Karoubi.x.{max u3 u4 u1 u2, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2) P) (CategoryTheory.Idempotents.Karoubi.x.{max u3 u4 u1 u2, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2) P) (CategoryTheory.Idempotents.Karoubi.p.{max u3 u4 u1 u2, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2) P) X) (CategoryTheory.NatTrans.app.{u3, u4, u1, u2} J _inst_1 C _inst_2 (CategoryTheory.Idempotents.Karoubi.x.{max u3 u4 u1 u2, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2) P) (CategoryTheory.Idempotents.Karoubi.x.{max u3 u4 u1 u2, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2) P) (CategoryTheory.Idempotents.Karoubi.p.{max u3 u4 u1 u2, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2) P) X)) (CategoryTheory.NatTrans.app.{u3, u4, u1, u2} J _inst_1 C _inst_2 (CategoryTheory.Idempotents.Karoubi.x.{max u3 u4 u1 u2, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2) P) (CategoryTheory.Idempotents.Karoubi.x.{max u3 u4 u1 u2, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2) P) (CategoryTheory.Idempotents.Karoubi.p.{max u3 u4 u1 u2, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2) P) X)
but is expected to have type
  forall {J : Type.{u1}} {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u1} J] [_inst_2 : CategoryTheory.Category.{u4, u3} C] (P : CategoryTheory.Idempotents.Karoubi.{max (max (max u3 u1) u4) u2, max u1 u4} (CategoryTheory.Functor.{u2, u4, u1, u3} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u2, u4, u1, u3} J _inst_1 C _inst_2)) (X : J), Eq.{succ u4} (Quiver.Hom.{succ u4, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} C (CategoryTheory.Category.toCategoryStruct.{u4, u3} C _inst_2)) (Prefunctor.obj.{succ u2, succ u4, u1, u3} J (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} J (CategoryTheory.Category.toCategoryStruct.{u2, u1} J _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} C (CategoryTheory.Category.toCategoryStruct.{u4, u3} C _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u4, u1, u3} J _inst_1 C _inst_2 (CategoryTheory.Idempotents.Karoubi.X.{max (max (max u1 u3) u2) u4, max u1 u4} (CategoryTheory.Functor.{u2, u4, u1, u3} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u2, u4, u1, u3} J _inst_1 C _inst_2) P)) X) (Prefunctor.obj.{succ u2, succ u4, u1, u3} J (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} J (CategoryTheory.Category.toCategoryStruct.{u2, u1} J _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} C (CategoryTheory.Category.toCategoryStruct.{u4, u3} C _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u4, u1, u3} J _inst_1 C _inst_2 (CategoryTheory.Idempotents.Karoubi.X.{max (max (max u1 u3) u2) u4, max u1 u4} (CategoryTheory.Functor.{u2, u4, u1, u3} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u2, u4, u1, u3} J _inst_1 C _inst_2) P)) X)) (CategoryTheory.CategoryStruct.comp.{u4, u3} C (CategoryTheory.Category.toCategoryStruct.{u4, u3} C _inst_2) (Prefunctor.obj.{succ u2, succ u4, u1, u3} J (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} J (CategoryTheory.Category.toCategoryStruct.{u2, u1} J _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} C (CategoryTheory.Category.toCategoryStruct.{u4, u3} C _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u4, u1, u3} J _inst_1 C _inst_2 (CategoryTheory.Idempotents.Karoubi.X.{max (max (max u1 u3) u2) u4, max u1 u4} (CategoryTheory.Functor.{u2, u4, u1, u3} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u2, u4, u1, u3} J _inst_1 C _inst_2) P)) X) (Prefunctor.obj.{succ u2, succ u4, u1, u3} J (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} J (CategoryTheory.Category.toCategoryStruct.{u2, u1} J _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} C (CategoryTheory.Category.toCategoryStruct.{u4, u3} C _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u4, u1, u3} J _inst_1 C _inst_2 (CategoryTheory.Idempotents.Karoubi.X.{max (max (max u1 u3) u2) u4, max u1 u4} (CategoryTheory.Functor.{u2, u4, u1, u3} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u2, u4, u1, u3} J _inst_1 C _inst_2) P)) X) (Prefunctor.obj.{succ u2, succ u4, u1, u3} J (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} J (CategoryTheory.Category.toCategoryStruct.{u2, u1} J _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} C (CategoryTheory.Category.toCategoryStruct.{u4, u3} C _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u4, u1, u3} J _inst_1 C _inst_2 (CategoryTheory.Idempotents.Karoubi.X.{max (max (max u1 u3) u2) u4, max u1 u4} (CategoryTheory.Functor.{u2, u4, u1, u3} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u2, u4, u1, u3} J _inst_1 C _inst_2) P)) X) (CategoryTheory.NatTrans.app.{u2, u4, u1, u3} J _inst_1 C _inst_2 (CategoryTheory.Idempotents.Karoubi.X.{max (max (max u1 u3) u2) u4, max u1 u4} (CategoryTheory.Functor.{u2, u4, u1, u3} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u2, u4, u1, u3} J _inst_1 C _inst_2) P) (CategoryTheory.Idempotents.Karoubi.X.{max (max (max u1 u3) u2) u4, max u1 u4} (CategoryTheory.Functor.{u2, u4, u1, u3} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u2, u4, u1, u3} J _inst_1 C _inst_2) P) (CategoryTheory.Idempotents.Karoubi.p.{max (max (max u1 u3) u2) u4, max u1 u4} (CategoryTheory.Functor.{u2, u4, u1, u3} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u2, u4, u1, u3} J _inst_1 C _inst_2) P) X) (CategoryTheory.NatTrans.app.{u2, u4, u1, u3} J _inst_1 C _inst_2 (CategoryTheory.Idempotents.Karoubi.X.{max (max (max u1 u3) u2) u4, max u1 u4} (CategoryTheory.Functor.{u2, u4, u1, u3} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u2, u4, u1, u3} J _inst_1 C _inst_2) P) (CategoryTheory.Idempotents.Karoubi.X.{max (max (max u1 u3) u2) u4, max u1 u4} (CategoryTheory.Functor.{u2, u4, u1, u3} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u2, u4, u1, u3} J _inst_1 C _inst_2) P) (CategoryTheory.Idempotents.Karoubi.p.{max (max (max u1 u3) u2) u4, max u1 u4} (CategoryTheory.Functor.{u2, u4, u1, u3} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u2, u4, u1, u3} J _inst_1 C _inst_2) P) X)) (CategoryTheory.NatTrans.app.{u2, u4, u1, u3} J _inst_1 C _inst_2 (CategoryTheory.Idempotents.Karoubi.X.{max (max (max u1 u3) u2) u4, max u1 u4} (CategoryTheory.Functor.{u2, u4, u1, u3} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u2, u4, u1, u3} J _inst_1 C _inst_2) P) (CategoryTheory.Idempotents.Karoubi.X.{max (max (max u1 u3) u2) u4, max u1 u4} (CategoryTheory.Functor.{u2, u4, u1, u3} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u2, u4, u1, u3} J _inst_1 C _inst_2) P) (CategoryTheory.Idempotents.Karoubi.p.{max (max (max u1 u3) u2) u4, max u1 u4} (CategoryTheory.Functor.{u2, u4, u1, u3} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u2, u4, u1, u3} J _inst_1 C _inst_2) P) X)
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.app_idem CategoryTheory.Idempotents.app_idemₓ'. -/
@[simp, reassoc]
theorem app_idem : P.p.app X ≫ P.p.app X = P.p.app X :=
  congr_app P.idem X
#align category_theory.idempotents.app_idem CategoryTheory.Idempotents.app_idem

variable {P Q}

/- warning: category_theory.idempotents.app_p_comp -> CategoryTheory.Idempotents.app_p_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.app_p_comp CategoryTheory.Idempotents.app_p_compₓ'. -/
@[simp, reassoc]
theorem app_p_comp : P.p.app X ≫ f.f.app X = f.f.app X :=
  congr_app (p_comp f) X
#align category_theory.idempotents.app_p_comp CategoryTheory.Idempotents.app_p_comp

/- warning: category_theory.idempotents.app_comp_p -> CategoryTheory.Idempotents.app_comp_p is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.app_comp_p CategoryTheory.Idempotents.app_comp_pₓ'. -/
@[simp, reassoc]
theorem app_comp_p : f.f.app X ≫ Q.p.app X = f.f.app X :=
  congr_app (comp_p f) X
#align category_theory.idempotents.app_comp_p CategoryTheory.Idempotents.app_comp_p

/- warning: category_theory.idempotents.app_p_comm -> CategoryTheory.Idempotents.app_p_comm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.app_p_comm CategoryTheory.Idempotents.app_p_commₓ'. -/
@[reassoc]
theorem app_p_comm : P.p.app X ≫ f.f.app X = f.f.app X ≫ Q.p.app X :=
  congr_app (p_comm f) X
#align category_theory.idempotents.app_p_comm CategoryTheory.Idempotents.app_p_comm

variable (J C)

#print CategoryTheory.Idempotents.functor_category_isIdempotentComplete /-
instance functor_category_isIdempotentComplete [IsIdempotentComplete C] :
    IsIdempotentComplete (J ⥤ C) := by
  refine' ⟨_⟩
  intro F p hp
  have hC := (is_idempotent_complete_iff_has_equalizer_of_id_and_idempotent C).mp inferInstance
  haveI : ∀ j : J, has_equalizer (𝟙 _) (p.app j) := fun j => hC _ _ (congr_app hp j)
  /- We construct the direct factor `Y` associated to `p : F ⟶ F` by computing
      the equalizer of the identity and `p.app j` on each object `(j : J)`.  -/
  let Y : J ⥤ C :=
    { obj := fun j => limits.equalizer (𝟙 _) (p.app j)
      map := fun j j' φ =>
        equalizer.lift (limits.equalizer.ι (𝟙 _) (p.app j) ≫ F.map φ)
          (by rw [comp_id, assoc, p.naturality φ, ← assoc, ← limits.equalizer.condition, comp_id])
      map_id' := fun j => by ext; simp only [comp_id, Functor.map_id, equalizer.lift_ι, id_comp]
      map_comp' := fun j j' j'' φ φ' => by
        ext
        simp only [assoc, functor.map_comp, equalizer.lift_ι, equalizer.lift_ι_assoc] }
  let i : Y ⟶ F :=
    { app := fun j => equalizer.ι _ _
      naturality' := fun j j' φ => by rw [equalizer.lift_ι] }
  let e : F ⟶ Y :=
    { app := fun j => equalizer.lift (p.app j) (by rw [comp_id]; exact (congr_app hp j).symm)
      naturality' := fun j j' φ => by
        ext
        simp only [assoc, equalizer.lift_ι, nat_trans.naturality, equalizer.lift_ι_assoc] }
  use Y, i, e
  constructor <;> ext j
  ·
    simp only [nat_trans.comp_app, assoc, equalizer.lift_ι, nat_trans.id_app, id_comp, ←
      equalizer.condition, comp_id]
  · simp only [nat_trans.comp_app, equalizer.lift_ι]
#align category_theory.idempotents.functor_category_is_idempotent_complete CategoryTheory.Idempotents.functor_category_isIdempotentComplete
-/

namespace KaroubiFunctorCategoryEmbedding

variable {J C}

/- warning: category_theory.idempotents.karoubi_functor_category_embedding.obj -> CategoryTheory.Idempotents.KaroubiFunctorCategoryEmbedding.obj is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} J] [_inst_2 : CategoryTheory.Category.{u4, u2} C], (CategoryTheory.Idempotents.Karoubi.{max u3 u4 u1 u2, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2)) -> (CategoryTheory.Functor.{u3, u4, u1, max u2 u4} J _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} C _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} C _inst_2))
but is expected to have type
  forall {J : Type.{u1}} {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} J] [_inst_2 : CategoryTheory.Category.{u4, u2} C], (CategoryTheory.Idempotents.Karoubi.{max (max (max u2 u1) u4) u3, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2)) -> (CategoryTheory.Functor.{u3, u4, u1, max u4 u2} J _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} C _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u2, u4} C _inst_2))
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.karoubi_functor_category_embedding.obj CategoryTheory.Idempotents.KaroubiFunctorCategoryEmbedding.objₓ'. -/
/-- On objects, the functor which sends a formal direct factor `P` of a
functor `F : J ⥤ C` to the functor `J ⥤ karoubi C` which sends `(j : J)` to
the corresponding direct factor of `F.obj j`. -/
@[simps]
def obj (P : Karoubi (J ⥤ C)) : J ⥤ Karoubi C
    where
  obj j := ⟨P.pt.obj j, P.p.app j, congr_app P.idem j⟩
  map j j' φ :=
    { f := P.p.app j ≫ P.pt.map φ
      comm := by
        simp only [nat_trans.naturality, assoc]
        have h := congr_app P.idem j
        rw [nat_trans.comp_app] at h
        slice_rhs 1 3 => erw [h, h] }
#align category_theory.idempotents.karoubi_functor_category_embedding.obj CategoryTheory.Idempotents.KaroubiFunctorCategoryEmbedding.obj

/- warning: category_theory.idempotents.karoubi_functor_category_embedding.map -> CategoryTheory.Idempotents.KaroubiFunctorCategoryEmbedding.map is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} J] [_inst_2 : CategoryTheory.Category.{u4, u2} C] {P : CategoryTheory.Idempotents.Karoubi.{max u3 u4 u1 u2, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2)} {Q : CategoryTheory.Idempotents.Karoubi.{max u3 u4 u1 u2, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2)}, (Quiver.Hom.{succ (max u1 u4), max (max u3 u4 u1 u2) u1 u4} (CategoryTheory.Idempotents.Karoubi.{max u3 u4 u1 u2, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2)) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u4, max (max u3 u4 u1 u2) u1 u4} (CategoryTheory.Idempotents.Karoubi.{max u3 u4 u1 u2, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2)) (CategoryTheory.Category.toCategoryStruct.{max u1 u4, max (max u3 u4 u1 u2) u1 u4} (CategoryTheory.Idempotents.Karoubi.{max u3 u4 u1 u2, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2)) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{max u3 u4 u1 u2, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2)))) P Q) -> (Quiver.Hom.{succ (max u1 u4), max u3 u4 u1 u2 u4} (CategoryTheory.Functor.{u3, u4, u1, max u2 u4} J _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} C _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} C _inst_2)) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u4, max u3 u4 u1 u2 u4} (CategoryTheory.Functor.{u3, u4, u1, max u2 u4} J _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} C _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} C _inst_2)) (CategoryTheory.Category.toCategoryStruct.{max u1 u4, max u3 u4 u1 u2 u4} (CategoryTheory.Functor.{u3, u4, u1, max u2 u4} J _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} C _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} C _inst_2)) (CategoryTheory.Functor.category.{u3, u4, u1, max u2 u4} J _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} C _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} C _inst_2)))) (CategoryTheory.Idempotents.KaroubiFunctorCategoryEmbedding.obj.{u1, u2, u3, u4} J C _inst_1 _inst_2 P) (CategoryTheory.Idempotents.KaroubiFunctorCategoryEmbedding.obj.{u1, u2, u3, u4} J C _inst_1 _inst_2 Q))
but is expected to have type
  forall {J : Type.{u1}} {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} J] [_inst_2 : CategoryTheory.Category.{u4, u2} C] {P : CategoryTheory.Idempotents.Karoubi.{max (max (max u2 u1) u4) u3, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2)} {Q : CategoryTheory.Idempotents.Karoubi.{max (max (max u2 u1) u4) u3, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2)}, (Quiver.Hom.{max (succ u1) (succ u4), max (max (max u1 u2) u3) u4} (CategoryTheory.Idempotents.Karoubi.{max (max (max u2 u1) u4) u3, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2)) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u4, max (max (max u1 u2) u3) u4} (CategoryTheory.Idempotents.Karoubi.{max (max (max u2 u1) u4) u3, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2)) (CategoryTheory.Category.toCategoryStruct.{max u1 u4, max (max (max u1 u2) u3) u4} (CategoryTheory.Idempotents.Karoubi.{max (max (max u2 u1) u4) u3, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2)) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{max (max (max u1 u2) u3) u4, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2)))) P Q) -> (Quiver.Hom.{max (succ u1) (succ u4), max (max (max u4 u3) u2) u1} (CategoryTheory.Functor.{u3, u4, u1, max u4 u2} J _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} C _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u2, u4} C _inst_2)) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u4, max (max (max u1 u2) u3) u4} (CategoryTheory.Functor.{u3, u4, u1, max u4 u2} J _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} C _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u2, u4} C _inst_2)) (CategoryTheory.Category.toCategoryStruct.{max u1 u4, max (max (max u1 u2) u3) u4} (CategoryTheory.Functor.{u3, u4, u1, max u4 u2} J _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} C _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u2, u4} C _inst_2)) (CategoryTheory.Functor.category.{u3, u4, u1, max u2 u4} J _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} C _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u2, u4} C _inst_2)))) (CategoryTheory.Idempotents.KaroubiFunctorCategoryEmbedding.obj.{u1, u2, u3, u4} J C _inst_1 _inst_2 P) (CategoryTheory.Idempotents.KaroubiFunctorCategoryEmbedding.obj.{u1, u2, u3, u4} J C _inst_1 _inst_2 Q))
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.karoubi_functor_category_embedding.map CategoryTheory.Idempotents.KaroubiFunctorCategoryEmbedding.mapₓ'. -/
/-- Tautological action on maps of the functor `karoubi (J ⥤ C) ⥤ (J ⥤ karoubi C)`. -/
@[simps]
def map {P Q : Karoubi (J ⥤ C)} (f : P ⟶ Q) : obj P ⟶ obj Q
    where app j := ⟨f.f.app j, congr_app f.comm j⟩
#align category_theory.idempotents.karoubi_functor_category_embedding.map CategoryTheory.Idempotents.KaroubiFunctorCategoryEmbedding.map

end KaroubiFunctorCategoryEmbedding

variable (J C)

/- warning: category_theory.idempotents.karoubi_functor_category_embedding -> CategoryTheory.Idempotents.karoubiFunctorCategoryEmbedding is a dubious translation:
lean 3 declaration is
  forall (J : Type.{u1}) (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u3, u1} J] [_inst_2 : CategoryTheory.Category.{u4, u2} C], CategoryTheory.Functor.{max u1 u4, max u1 u4, max (max u3 u4 u1 u2) u1 u4, max u3 u4 u1 u2 u4} (CategoryTheory.Idempotents.Karoubi.{max u3 u4 u1 u2, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2)) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{max u3 u4 u1 u2, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2)) (CategoryTheory.Functor.{u3, u4, u1, max u2 u4} J _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} C _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} C _inst_2)) (CategoryTheory.Functor.category.{u3, u4, u1, max u2 u4} J _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} C _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u2, u4} C _inst_2))
but is expected to have type
  forall (J : Type.{u1}) (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u3, u1} J] [_inst_2 : CategoryTheory.Category.{u4, u2} C], CategoryTheory.Functor.{max u1 u4, max u1 u4, max (max u1 u4) (max (max u2 u1) u4) u3, max (max (max (max u4 u2) u1) u4) u3} (CategoryTheory.Idempotents.Karoubi.{max (max (max u2 u1) u4) u3, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2)) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{max (max (max u1 u2) u3) u4, max u1 u4} (CategoryTheory.Functor.{u3, u4, u1, u2} J _inst_1 C _inst_2) (CategoryTheory.Functor.category.{u3, u4, u1, u2} J _inst_1 C _inst_2)) (CategoryTheory.Functor.{u3, u4, u1, max u4 u2} J _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} C _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u2, u4} C _inst_2)) (CategoryTheory.Functor.category.{u3, u4, u1, max u2 u4} J _inst_1 (CategoryTheory.Idempotents.Karoubi.{u2, u4} C _inst_2) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u2, u4} C _inst_2))
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.karoubi_functor_category_embedding CategoryTheory.Idempotents.karoubiFunctorCategoryEmbeddingₓ'. -/
/-- The tautological fully faithful functor `karoubi (J ⥤ C) ⥤ (J ⥤ karoubi C)`. -/
@[simps]
def karoubiFunctorCategoryEmbedding : Karoubi (J ⥤ C) ⥤ J ⥤ Karoubi C
    where
  obj := KaroubiFunctorCategoryEmbedding.obj
  map P Q := KaroubiFunctorCategoryEmbedding.map
#align category_theory.idempotents.karoubi_functor_category_embedding CategoryTheory.Idempotents.karoubiFunctorCategoryEmbedding

instance : Full (karoubiFunctorCategoryEmbedding J C)
    where
  preimage P Q f :=
    { f :=
        { app := fun j => (f.app j).f
          naturality' := fun j j' φ => by
            rw [← karoubi.comp_p_assoc]
            have h := hom_ext.mp (f.naturality φ)
            simp only [comp_f] at h
            dsimp [karoubi_functor_category_embedding] at h
            erw [← h, assoc, ← P.p.naturality_assoc φ, p_comp (f.app j')] }
      comm := by ext j; exact (f.app j).comm }
  witness' P Q f := by ext j; rfl

instance : Faithful (karoubiFunctorCategoryEmbedding J C)
    where map_injective' P Q f f' h := by ext j; exact hom_ext.mp (congr_app h j)

/- warning: category_theory.idempotents.to_karoubi_comp_karoubi_functor_category_embedding -> CategoryTheory.Idempotents.toKaroubi_comp_karoubiFunctorCategoryEmbedding is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.to_karoubi_comp_karoubi_functor_category_embedding CategoryTheory.Idempotents.toKaroubi_comp_karoubiFunctorCategoryEmbeddingₓ'. -/
/-- The composition of `(J ⥤ C) ⥤ karoubi (J ⥤ C)` and `karoubi (J ⥤ C) ⥤ (J ⥤ karoubi C)`
equals the functor `(J ⥤ C) ⥤ (J ⥤ karoubi C)` given by the composition with
`to_karoubi C : C ⥤ karoubi C`. -/
theorem toKaroubi_comp_karoubiFunctorCategoryEmbedding :
    toKaroubi _ ⋙ karoubiFunctorCategoryEmbedding J C = (whiskeringRight J _ _).obj (toKaroubi C) :=
  by
  apply Functor.ext
  · intro X Y f
    ext j
    dsimp [to_karoubi]
    simp only [eq_to_hom_app, eq_to_hom_refl, id_comp]
    erw [comp_id]
  · intro X
    apply Functor.ext
    · intro j j' φ
      ext
      dsimp
      simpa only [comp_id, id_comp]
    · intro j
      rfl
#align category_theory.idempotents.to_karoubi_comp_karoubi_functor_category_embedding CategoryTheory.Idempotents.toKaroubi_comp_karoubiFunctorCategoryEmbedding

end Idempotents

end CategoryTheory

