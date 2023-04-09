/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module category_theory.idempotents.karoubi_karoubi
! leanprover-community/mathlib commit 19cb3751e5e9b3d97adb51023949c50c13b5fdfd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Idempotents.Karoubi

/-!
# Idempotence of the Karoubi envelope

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we construct the equivalence of categories
`karoubi_karoubi.equivalence C : karoubi C ≌ karoubi (karoubi C)` for any category `C`.

-/


open CategoryTheory.Category

open CategoryTheory.Idempotents.Karoubi

namespace CategoryTheory

namespace Idempotents

namespace KaroubiKaroubi

variable (C : Type _) [Category C]

/- warning: category_theory.idempotents.karoubi_karoubi.inverse -> CategoryTheory.Idempotents.KaroubiKaroubi.inverse is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u1}) [_inst_1 : CategoryTheory.Category.{u2, u1} C], CategoryTheory.Functor.{u2, u2, max u1 u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1)
but is expected to have type
  forall (C : Type.{u1}) [_inst_1 : CategoryTheory.Category.{u2, u1} C], CategoryTheory.Functor.{u2, u2, max u2 u1, max u2 u1} (CategoryTheory.Idempotents.Karoubi.{max u2 u1, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1)
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.karoubi_karoubi.inverse CategoryTheory.Idempotents.KaroubiKaroubi.inverseₓ'. -/
/-- The canonical functor `karoubi (karoubi C) ⥤ karoubi C` -/
@[simps]
def inverse : Karoubi (Karoubi C) ⥤ Karoubi C
    where
  obj P := ⟨P.pt.pt, P.p.f, by simpa only [hom_ext] using P.idem⟩
  map P Q f := ⟨f.f.f, by simpa only [hom_ext] using f.comm⟩
#align category_theory.idempotents.karoubi_karoubi.inverse CategoryTheory.Idempotents.KaroubiKaroubi.inverse

instance [Preadditive C] : Functor.Additive (inverse C) where

/- warning: category_theory.idempotents.karoubi_karoubi.unit_iso -> CategoryTheory.Idempotents.KaroubiKaroubi.unitIso is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u1}) [_inst_1 : CategoryTheory.Category.{u2, u1} C], CategoryTheory.Iso.{max u1 u2, max u1 u2} (CategoryTheory.Functor.{u2, u2, max u1 u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1)) (CategoryTheory.Functor.category.{u2, u2, max u1 u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1)) (CategoryTheory.Functor.id.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1)) (CategoryTheory.Functor.comp.{u2, u2, u2, max u1 u2, max u1 u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.toKaroubi.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.KaroubiKaroubi.inverse.{u1, u2} C _inst_1))
but is expected to have type
  forall (C : Type.{u1}) [_inst_1 : CategoryTheory.Category.{u2, u1} C], CategoryTheory.Iso.{max u1 u2, max u1 u2} (CategoryTheory.Functor.{u2, u2, max u2 u1, max u2 u1} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1)) (CategoryTheory.Functor.category.{u2, u2, max u1 u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1)) (CategoryTheory.Functor.id.{u2, max u2 u1} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1)) (CategoryTheory.Functor.comp.{u2, u2, u2, max u1 u2, max u1 u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{max u2 u1, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{max u2 u1, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.toKaroubi.{max u2 u1, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.KaroubiKaroubi.inverse.{u1, u2} C _inst_1))
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.karoubi_karoubi.unit_iso CategoryTheory.Idempotents.KaroubiKaroubi.unitIsoₓ'. -/
/-- The unit isomorphism of the equivalence -/
@[simps]
def unitIso : 𝟭 (Karoubi C) ≅ toKaroubi (Karoubi C) ⋙ inverse C :=
  eqToIso (Functor.ext (by tidy) (by tidy))
#align category_theory.idempotents.karoubi_karoubi.unit_iso CategoryTheory.Idempotents.KaroubiKaroubi.unitIso

/- warning: category_theory.idempotents.karoubi_karoubi.counit_iso -> CategoryTheory.Idempotents.KaroubiKaroubi.counitIso is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u1}) [_inst_1 : CategoryTheory.Category.{u2, u1} C], CategoryTheory.Iso.{max u1 u2, max u1 u2} (CategoryTheory.Functor.{u2, u2, max u1 u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1))) (CategoryTheory.Functor.category.{u2, u2, max u1 u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1))) (CategoryTheory.Functor.comp.{u2, u2, u2, max u1 u2, max u1 u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.KaroubiKaroubi.inverse.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.toKaroubi.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1))) (CategoryTheory.Functor.id.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1)))
but is expected to have type
  forall (C : Type.{u1}) [_inst_1 : CategoryTheory.Category.{u2, u1} C], CategoryTheory.Iso.{max u1 u2, max u1 u2} (CategoryTheory.Functor.{u2, u2, max u1 u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{max u2 u1, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.{max u2 u1, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{max u2 u1, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1))) (CategoryTheory.Functor.category.{u2, u2, max u1 u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{max u2 u1, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.{max u2 u1, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{max u2 u1, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1))) (CategoryTheory.Functor.comp.{u2, u2, u2, max u1 u2, max u1 u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{max u2 u1, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{max u2 u1, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{max u2 u1, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.KaroubiKaroubi.inverse.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.toKaroubi.{max u2 u1, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1))) (CategoryTheory.Functor.id.{u2, max u2 u1} (CategoryTheory.Idempotents.Karoubi.{max u2 u1, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1)))
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.karoubi_karoubi.counit_iso CategoryTheory.Idempotents.KaroubiKaroubi.counitIsoₓ'. -/
/-- The counit isomorphism of the equivalence -/
@[simps]
def counitIso : inverse C ⋙ toKaroubi (Karoubi C) ≅ 𝟭 (Karoubi (Karoubi C))
    where
  Hom :=
    { app := fun P =>
        { f :=
            { f := P.p.1
              comm := by
                have h := P.idem
                simp only [hom_ext, comp_f] at h
                erw [← assoc, h, comp_p] }
          comm := by
            have h := P.idem
            simp only [hom_ext, comp_f] at h⊢
            erw [h, h] }
      naturality' := fun P Q f => by simpa only [hom_ext] using (p_comm f).symm }
  inv :=
    { app := fun P =>
        { f :=
            { f := P.p.1
              comm := by
                have h := P.idem
                simp only [hom_ext, comp_f] at h
                erw [h, p_comp] }
          comm := by
            have h := P.idem
            simp only [hom_ext, comp_f] at h⊢
            erw [h, h] }
      naturality' := fun P Q f => by simpa only [hom_ext] using (p_comm f).symm }
  hom_inv_id' := by
    ext P
    simpa only [hom_ext, id_eq] using P.idem
  inv_hom_id' := by
    ext P
    simpa only [hom_ext, id_eq] using P.idem
#align category_theory.idempotents.karoubi_karoubi.counit_iso CategoryTheory.Idempotents.KaroubiKaroubi.counitIso

/- warning: category_theory.idempotents.karoubi_karoubi.equivalence -> CategoryTheory.Idempotents.KaroubiKaroubi.equivalence is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u1}) [_inst_1 : CategoryTheory.Category.{u2, u1} C], CategoryTheory.Equivalence.{u2, u2, max u1 u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1))
but is expected to have type
  forall (C : Type.{u1}) [_inst_1 : CategoryTheory.Category.{u2, u1} C], CategoryTheory.Equivalence.{u2, u2, max u2 u1, max u2 u1} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{max u2 u1, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1))
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.karoubi_karoubi.equivalence CategoryTheory.Idempotents.KaroubiKaroubi.equivalenceₓ'. -/
/-- The equivalence `karoubi C ≌ karoubi (karoubi C)` -/
@[simps]
def equivalence : Karoubi C ≌ Karoubi (Karoubi C)
    where
  Functor := toKaroubi (Karoubi C)
  inverse := KaroubiKaroubi.inverse C
  unitIso := KaroubiKaroubi.unitIso C
  counitIso := KaroubiKaroubi.counitIso C
#align category_theory.idempotents.karoubi_karoubi.equivalence CategoryTheory.Idempotents.KaroubiKaroubi.equivalence

/- warning: category_theory.idempotents.karoubi_karoubi.equivalence.additive_functor -> CategoryTheory.Idempotents.KaroubiKaroubi.equivalence.additive_functor is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u1}) [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.Preadditive.{u2, u1} C _inst_1], CategoryTheory.Functor.Additive.{max u1 u2, max u1 u2, u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.preadditive.{u1, u2} C _inst_1 _inst_2) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.preadditive.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.preadditive.{u1, u2} C _inst_1 _inst_2)) (CategoryTheory.Equivalence.functor.{u2, u2, max u1 u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.KaroubiKaroubi.equivalence.{u1, u2} C _inst_1))
but is expected to have type
  forall (C : Type.{u1}) [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.Preadditive.{u2, u1} C _inst_1], CategoryTheory.Functor.Additive.{max u1 u2, max u1 u2, u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{max u2 u1, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.instPreadditiveKaroubiInstCategoryKaroubi.{u1, u2} C _inst_1 _inst_2) (CategoryTheory.Idempotents.instPreadditiveKaroubiInstCategoryKaroubi.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.instPreadditiveKaroubiInstCategoryKaroubi.{u1, u2} C _inst_1 _inst_2)) (CategoryTheory.Equivalence.functor.{u2, u2, max u1 u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{max u2 u1, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.KaroubiKaroubi.equivalence.{u1, u2} C _inst_1))
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.karoubi_karoubi.equivalence.additive_functor CategoryTheory.Idempotents.KaroubiKaroubi.equivalence.additive_functorₓ'. -/
instance equivalence.additive_functor [Preadditive C] : Functor.Additive (equivalence C).Functor :=
  by
  dsimp
  infer_instance
#align category_theory.idempotents.karoubi_karoubi.equivalence.additive_functor CategoryTheory.Idempotents.KaroubiKaroubi.equivalence.additive_functor

/- warning: category_theory.idempotents.karoubi_karoubi.equivalence.additive_inverse -> CategoryTheory.Idempotents.KaroubiKaroubi.equivalence.additive_inverse is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u1}) [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.Preadditive.{u2, u1} C _inst_1], CategoryTheory.Functor.Additive.{max u1 u2, max u1 u2, u2, u2} (CategoryTheory.Idempotents.Karoubi.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.preadditive.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.preadditive.{u1, u2} C _inst_1 _inst_2)) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.preadditive.{u1, u2} C _inst_1 _inst_2) (CategoryTheory.Equivalence.inverse.{u2, u2, max u1 u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.KaroubiKaroubi.equivalence.{u1, u2} C _inst_1))
but is expected to have type
  forall (C : Type.{u1}) [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.Preadditive.{u2, u1} C _inst_1], CategoryTheory.Functor.Additive.{max u1 u2, max u1 u2, u2, u2} (CategoryTheory.Idempotents.Karoubi.{max u2 u1, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.instPreadditiveKaroubiInstCategoryKaroubi.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.instPreadditiveKaroubiInstCategoryKaroubi.{u1, u2} C _inst_1 _inst_2)) (CategoryTheory.Idempotents.instPreadditiveKaroubiInstCategoryKaroubi.{u1, u2} C _inst_1 _inst_2) (CategoryTheory.Equivalence.inverse.{u2, u2, max u1 u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{max u2 u1, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{max u1 u2, u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1)) (CategoryTheory.Idempotents.KaroubiKaroubi.equivalence.{u1, u2} C _inst_1))
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.karoubi_karoubi.equivalence.additive_inverse CategoryTheory.Idempotents.KaroubiKaroubi.equivalence.additive_inverseₓ'. -/
instance equivalence.additive_inverse [Preadditive C] : Functor.Additive (equivalence C).inverse :=
  by
  dsimp
  infer_instance
#align category_theory.idempotents.karoubi_karoubi.equivalence.additive_inverse CategoryTheory.Idempotents.KaroubiKaroubi.equivalence.additive_inverse

end KaroubiKaroubi

end Idempotents

end CategoryTheory

