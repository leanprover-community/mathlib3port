/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module category_theory.idempotents.homological_complex
! leanprover-community/mathlib commit 86d1873c01a723aba6788f0b9051ae3d23b4c1c3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Homology.Additive
import Mathbin.CategoryTheory.Idempotents.Karoubi

/-!
# Idempotent completeness and homological complexes

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains simplifications lemmas for categories
`karoubi (homological_complex C c)` and the construction of an equivalence
of categories `karoubi (homological_complex C c) ≌ homological_complex (karoubi C) c`.

When the category `C` is idempotent complete, it is shown that
`homological_complex (karoubi C) c` is also idempotent complete.

-/


namespace CategoryTheory

open Category

variable {C : Type _} [Category C] [Preadditive C] {ι : Type _} {c : ComplexShape ι}

namespace Idempotents

namespace Karoubi

namespace HomologicalComplex

variable {P Q : Karoubi (HomologicalComplex C c)} (f : P ⟶ Q) (n : ι)

/- warning: category_theory.idempotents.karoubi.homological_complex.p_comp_d -> CategoryTheory.Idempotents.Karoubi.HomologicalComplex.p_comp_d is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.karoubi.homological_complex.p_comp_d CategoryTheory.Idempotents.Karoubi.HomologicalComplex.p_comp_dₓ'. -/
@[simp, reassoc]
theorem p_comp_d : P.p.f n ≫ f.f.f n = f.f.f n :=
  HomologicalComplex.congr_hom (p_comp f) n
#align category_theory.idempotents.karoubi.homological_complex.p_comp_d CategoryTheory.Idempotents.Karoubi.HomologicalComplex.p_comp_d

/- warning: category_theory.idempotents.karoubi.homological_complex.comp_p_d -> CategoryTheory.Idempotents.Karoubi.HomologicalComplex.comp_p_d is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.karoubi.homological_complex.comp_p_d CategoryTheory.Idempotents.Karoubi.HomologicalComplex.comp_p_dₓ'. -/
@[simp, reassoc]
theorem comp_p_d : f.f.f n ≫ Q.p.f n = f.f.f n :=
  HomologicalComplex.congr_hom (comp_p f) n
#align category_theory.idempotents.karoubi.homological_complex.comp_p_d CategoryTheory.Idempotents.Karoubi.HomologicalComplex.comp_p_d

/- warning: category_theory.idempotents.karoubi.homological_complex.p_comm_f -> CategoryTheory.Idempotents.Karoubi.HomologicalComplex.p_comm_f is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.karoubi.homological_complex.p_comm_f CategoryTheory.Idempotents.Karoubi.HomologicalComplex.p_comm_fₓ'. -/
@[reassoc]
theorem p_comm_f : P.p.f n ≫ f.f.f n = f.f.f n ≫ Q.p.f n :=
  HomologicalComplex.congr_hom (p_comm f) n
#align category_theory.idempotents.karoubi.homological_complex.p_comm_f CategoryTheory.Idempotents.Karoubi.HomologicalComplex.p_comm_f

variable (P)

/- warning: category_theory.idempotents.karoubi.homological_complex.p_idem -> CategoryTheory.Idempotents.Karoubi.HomologicalComplex.p_idem is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.karoubi.homological_complex.p_idem CategoryTheory.Idempotents.Karoubi.HomologicalComplex.p_idemₓ'. -/
@[simp, reassoc]
theorem p_idem : P.p.f n ≫ P.p.f n = P.p.f n :=
  HomologicalComplex.congr_hom P.idem n
#align category_theory.idempotents.karoubi.homological_complex.p_idem CategoryTheory.Idempotents.Karoubi.HomologicalComplex.p_idem

end HomologicalComplex

end Karoubi

open Karoubi

namespace KaroubiHomologicalComplexEquivalence

namespace Functor

/- warning: category_theory.idempotents.karoubi_homological_complex_equivalence.functor.obj -> CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.Functor.obj is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.Preadditive.{u2, u1} C _inst_1] {ι : Type.{u3}} {c : ComplexShape.{u3} ι}, (CategoryTheory.Idempotents.Karoubi.{max u1 u3 u2, max u3 u2} (HomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c) (HomologicalComplex.CategoryTheory.category.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c)) -> (HomologicalComplex.{u2, max u1 u2, u3} ι (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.preadditive.{u1, u2} C _inst_1 _inst_2)) c)
but is expected to have type
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.Preadditive.{u2, u1} C _inst_1] {ι : Type.{u3}} {c : ComplexShape.{u3} ι}, (CategoryTheory.Idempotents.Karoubi.{max (max u3 u1) u2, max u2 u3} (HomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c)) -> (HomologicalComplex.{u2, max u2 u1, u3} ι (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.instPreadditiveKaroubiInstCategoryKaroubi.{u1, u2} C _inst_1 _inst_2)) c)
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.karoubi_homological_complex_equivalence.functor.obj CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.Functor.objₓ'. -/
/-- The functor `karoubi (homological_complex C c) ⥤ homological_complex (karoubi C) c`,
on objects. -/
@[simps]
def obj (P : Karoubi (HomologicalComplex C c)) : HomologicalComplex (Karoubi C) c
    where
  pt n :=
    ⟨P.pt.pt n, P.p.f n, by
      simpa only [HomologicalComplex.comp_f] using HomologicalComplex.congr_hom P.idem n⟩
  d i j :=
    { f := P.p.f i ≫ P.pt.d i j
      comm := by tidy }
  shape' i j hij := by simp only [hom_eq_zero_iff, P.X.shape i j hij, limits.comp_zero]
#align category_theory.idempotents.karoubi_homological_complex_equivalence.functor.obj CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.Functor.obj

/- warning: category_theory.idempotents.karoubi_homological_complex_equivalence.functor.map -> CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.Functor.map is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.Preadditive.{u2, u1} C _inst_1] {ι : Type.{u3}} {c : ComplexShape.{u3} ι} {P : CategoryTheory.Idempotents.Karoubi.{max u1 u3 u2, max u3 u2} (HomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c) (HomologicalComplex.CategoryTheory.category.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c)} {Q : CategoryTheory.Idempotents.Karoubi.{max u1 u3 u2, max u3 u2} (HomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c) (HomologicalComplex.CategoryTheory.category.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c)}, (Quiver.Hom.{succ (max u3 u2), max u1 u3 u2} (CategoryTheory.Idempotents.Karoubi.{max u1 u3 u2, max u3 u2} (HomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c) (HomologicalComplex.CategoryTheory.category.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c)) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u2, max u1 u3 u2} (CategoryTheory.Idempotents.Karoubi.{max u1 u3 u2, max u3 u2} (HomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c) (HomologicalComplex.CategoryTheory.category.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c)) (CategoryTheory.Category.toCategoryStruct.{max u3 u2, max u1 u3 u2} (CategoryTheory.Idempotents.Karoubi.{max u1 u3 u2, max u3 u2} (HomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c) (HomologicalComplex.CategoryTheory.category.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c)) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{max u1 u3 u2, max u3 u2} (HomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c) (HomologicalComplex.CategoryTheory.category.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c)))) P Q) -> (Quiver.Hom.{succ (max u3 u2), max (max u1 u2) u3 u2} (HomologicalComplex.{u2, max u1 u2, u3} ι (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.preadditive.{u1, u2} C _inst_1 _inst_2)) c) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u2, max (max u1 u2) u3 u2} (HomologicalComplex.{u2, max u1 u2, u3} ι (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.preadditive.{u1, u2} C _inst_1 _inst_2)) c) (CategoryTheory.Category.toCategoryStruct.{max u3 u2, max (max u1 u2) u3 u2} (HomologicalComplex.{u2, max u1 u2, u3} ι (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.preadditive.{u1, u2} C _inst_1 _inst_2)) c) (HomologicalComplex.CategoryTheory.category.{u2, max u1 u2, u3} ι (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.preadditive.{u1, u2} C _inst_1 _inst_2)) c))) (CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.Functor.obj.{u1, u2, u3} C _inst_1 _inst_2 ι c P) (CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.Functor.obj.{u1, u2, u3} C _inst_1 _inst_2 ι c Q))
but is expected to have type
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.Preadditive.{u2, u1} C _inst_1] {ι : Type.{u3}} {c : ComplexShape.{u3} ι} {P : CategoryTheory.Idempotents.Karoubi.{max (max u3 u1) u2, max u2 u3} (HomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c)} {Q : CategoryTheory.Idempotents.Karoubi.{max (max u3 u1) u2, max u2 u3} (HomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c)}, (Quiver.Hom.{max (succ u2) (succ u3), max (max u1 u2) u3} (CategoryTheory.Idempotents.Karoubi.{max (max u3 u1) u2, max u2 u3} (HomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c)) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u3, max (max u1 u2) u3} (CategoryTheory.Idempotents.Karoubi.{max (max u3 u1) u2, max u2 u3} (HomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c)) (CategoryTheory.Category.toCategoryStruct.{max u2 u3, max (max u1 u2) u3} (CategoryTheory.Idempotents.Karoubi.{max (max u3 u1) u2, max u2 u3} (HomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c)) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{max (max u1 u2) u3, max u2 u3} (HomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c)))) P Q) -> (Quiver.Hom.{max (succ u2) (succ u3), max (max u3 u2) u1} (HomologicalComplex.{u2, max u2 u1, u3} ι (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.instPreadditiveKaroubiInstCategoryKaroubi.{u1, u2} C _inst_1 _inst_2)) c) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u3, max (max u1 u2) u3} (HomologicalComplex.{u2, max u2 u1, u3} ι (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.instPreadditiveKaroubiInstCategoryKaroubi.{u1, u2} C _inst_1 _inst_2)) c) (CategoryTheory.Category.toCategoryStruct.{max u2 u3, max (max u1 u2) u3} (HomologicalComplex.{u2, max u2 u1, u3} ι (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.instPreadditiveKaroubiInstCategoryKaroubi.{u1, u2} C _inst_1 _inst_2)) c) (HomologicalComplex.instCategoryHomologicalComplex.{u2, max u1 u2, u3} ι (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.instPreadditiveKaroubiInstCategoryKaroubi.{u1, u2} C _inst_1 _inst_2)) c))) (CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.Functor.obj.{u1, u2, u3} C _inst_1 _inst_2 ι c P) (CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.Functor.obj.{u1, u2, u3} C _inst_1 _inst_2 ι c Q))
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.karoubi_homological_complex_equivalence.functor.map CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.Functor.mapₓ'. -/
/-- The functor `karoubi (homological_complex C c) ⥤ homological_complex (karoubi C) c`,
on morphisms. -/
@[simps]
def map {P Q : Karoubi (HomologicalComplex C c)} (f : P ⟶ Q) : obj P ⟶ obj Q
    where f n :=
    { f := f.f.f n
      comm := by simp }
#align category_theory.idempotents.karoubi_homological_complex_equivalence.functor.map CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.Functor.map

end Functor

/- warning: category_theory.idempotents.karoubi_homological_complex_equivalence.functor -> CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.functor is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.Preadditive.{u2, u1} C _inst_1] {ι : Type.{u3}} {c : ComplexShape.{u3} ι}, CategoryTheory.Functor.{max u3 u2, max u3 u2, max u1 u3 u2, max (max u1 u2) u3 u2} (CategoryTheory.Idempotents.Karoubi.{max u1 u3 u2, max u3 u2} (HomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c) (HomologicalComplex.CategoryTheory.category.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c)) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{max u1 u3 u2, max u3 u2} (HomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c) (HomologicalComplex.CategoryTheory.category.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c)) (HomologicalComplex.{u2, max u1 u2, u3} ι (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.preadditive.{u1, u2} C _inst_1 _inst_2)) c) (HomologicalComplex.CategoryTheory.category.{u2, max u1 u2, u3} ι (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.preadditive.{u1, u2} C _inst_1 _inst_2)) c)
but is expected to have type
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.Preadditive.{u2, u1} C _inst_1] {ι : Type.{u3}} {c : ComplexShape.{u3} ι}, CategoryTheory.Functor.{max u2 u3, max u2 u3, max (max u2 u3) (max u3 u1) u2, max (max u3 u2 u1) u2} (CategoryTheory.Idempotents.Karoubi.{max (max u3 u1) u2, max u2 u3} (HomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c)) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{max (max u1 u2) u3, max u2 u3} (HomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c)) (HomologicalComplex.{u2, max u2 u1, u3} ι (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.instPreadditiveKaroubiInstCategoryKaroubi.{u1, u2} C _inst_1 _inst_2)) c) (HomologicalComplex.instCategoryHomologicalComplex.{u2, max u1 u2, u3} ι (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.instPreadditiveKaroubiInstCategoryKaroubi.{u1, u2} C _inst_1 _inst_2)) c)
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.karoubi_homological_complex_equivalence.functor CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.functorₓ'. -/
/-- The functor `karoubi (homological_complex C c) ⥤ homological_complex (karoubi C) c`. -/
@[simps]
def functor : Karoubi (HomologicalComplex C c) ⥤ HomologicalComplex (Karoubi C) c
    where
  obj := Functor.obj
  map P Q f := Functor.map f
#align category_theory.idempotents.karoubi_homological_complex_equivalence.functor CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.functor

namespace Inverse

/- warning: category_theory.idempotents.karoubi_homological_complex_equivalence.inverse.obj -> CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.Inverse.obj is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.Preadditive.{u2, u1} C _inst_1] {ι : Type.{u3}} {c : ComplexShape.{u3} ι}, (HomologicalComplex.{u2, max u1 u2, u3} ι (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.preadditive.{u1, u2} C _inst_1 _inst_2)) c) -> (CategoryTheory.Idempotents.Karoubi.{max u1 u3 u2, max u3 u2} (HomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c) (HomologicalComplex.CategoryTheory.category.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c))
but is expected to have type
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.Preadditive.{u2, u1} C _inst_1] {ι : Type.{u3}} {c : ComplexShape.{u3} ι}, (HomologicalComplex.{u2, max u2 u1, u3} ι (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.instPreadditiveKaroubiInstCategoryKaroubi.{u1, u2} C _inst_1 _inst_2)) c) -> (CategoryTheory.Idempotents.Karoubi.{max (max u3 u1) u2, max u2 u3} (HomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c))
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.karoubi_homological_complex_equivalence.inverse.obj CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.Inverse.objₓ'. -/
/-- The functor `homological_complex (karoubi C) c ⥤ karoubi (homological_complex C c)`,
on objects -/
@[simps]
def obj (K : HomologicalComplex (Karoubi C) c) : Karoubi (HomologicalComplex C c)
    where
  pt :=
    { pt := fun n => (K.pt n).pt
      d := fun i j => (K.d i j).f
      shape' := fun i j hij => hom_eq_zero_iff.mp (K.shape i j hij)
      d_comp_d' := fun i j k hij hjk => by
        simpa only [comp_f] using hom_eq_zero_iff.mp (K.d_comp_d i j k) }
  p :=
    { f := fun n => (K.pt n).p
      comm' := by simp }
  idem := by tidy
#align category_theory.idempotents.karoubi_homological_complex_equivalence.inverse.obj CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.Inverse.obj

/- warning: category_theory.idempotents.karoubi_homological_complex_equivalence.inverse.map -> CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.Inverse.map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.karoubi_homological_complex_equivalence.inverse.map CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.Inverse.mapₓ'. -/
/-- The functor `homological_complex (karoubi C) c ⥤ karoubi (homological_complex C c)`,
on morphisms -/
@[simps]
def map {K L : HomologicalComplex (Karoubi C) c} (f : K ⟶ L) : obj K ⟶ obj L
    where
  f :=
    { f := fun n => (f.f n).f
      comm' := fun i j hij => by simpa only [comp_f] using hom_ext.mp (f.comm' i j hij) }
  comm := by tidy
#align category_theory.idempotents.karoubi_homological_complex_equivalence.inverse.map CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.Inverse.map

end Inverse

/- warning: category_theory.idempotents.karoubi_homological_complex_equivalence.inverse -> CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.inverse is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.Preadditive.{u2, u1} C _inst_1] {ι : Type.{u3}} {c : ComplexShape.{u3} ι}, CategoryTheory.Functor.{max u3 u2, max u3 u2, max (max u1 u2) u3 u2, max u1 u3 u2} (HomologicalComplex.{u2, max u1 u2, u3} ι (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.preadditive.{u1, u2} C _inst_1 _inst_2)) c) (HomologicalComplex.CategoryTheory.category.{u2, max u1 u2, u3} ι (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.preadditive.{u1, u2} C _inst_1 _inst_2)) c) (CategoryTheory.Idempotents.Karoubi.{max u1 u3 u2, max u3 u2} (HomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c) (HomologicalComplex.CategoryTheory.category.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c)) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{max u1 u3 u2, max u3 u2} (HomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c) (HomologicalComplex.CategoryTheory.category.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c))
but is expected to have type
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.Preadditive.{u2, u1} C _inst_1] {ι : Type.{u3}} {c : ComplexShape.{u3} ι}, CategoryTheory.Functor.{max u2 u3, max u2 u3, max (max u3 u2 u1) u2, max (max u2 u3) (max u3 u1) u2} (HomologicalComplex.{u2, max u2 u1, u3} ι (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.instPreadditiveKaroubiInstCategoryKaroubi.{u1, u2} C _inst_1 _inst_2)) c) (HomologicalComplex.instCategoryHomologicalComplex.{u2, max u1 u2, u3} ι (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.instPreadditiveKaroubiInstCategoryKaroubi.{u1, u2} C _inst_1 _inst_2)) c) (CategoryTheory.Idempotents.Karoubi.{max (max u3 u1) u2, max u2 u3} (HomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c)) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{max (max u1 u2) u3, max u2 u3} (HomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c))
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.karoubi_homological_complex_equivalence.inverse CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.inverseₓ'. -/
/-- The functor `homological_complex (karoubi C) c ⥤ karoubi (homological_complex C c)`. -/
@[simps]
def inverse : HomologicalComplex (Karoubi C) c ⥤ Karoubi (HomologicalComplex C c)
    where
  obj := Inverse.obj
  map K L f := Inverse.map f
#align category_theory.idempotents.karoubi_homological_complex_equivalence.inverse CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.inverse

/- warning: category_theory.idempotents.karoubi_homological_complex_equivalence.counit_iso -> CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.counitIso is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.karoubi_homological_complex_equivalence.counit_iso CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.counitIsoₓ'. -/
/-- The counit isomorphism of the equivalence
`karoubi (homological_complex C c) ≌ homological_complex (karoubi C) c`. -/
@[simps]
def counitIso : inverse ⋙ functor ≅ 𝟭 (HomologicalComplex (Karoubi C) c) :=
  eqToIso (Functor.ext (fun P => HomologicalComplex.ext (by tidy) (by tidy)) (by tidy))
#align category_theory.idempotents.karoubi_homological_complex_equivalence.counit_iso CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.counitIso

/- warning: category_theory.idempotents.karoubi_homological_complex_equivalence.unit_iso -> CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.unitIso is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.karoubi_homological_complex_equivalence.unit_iso CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.unitIsoₓ'. -/
/-- The unit isomorphism of the equivalence
`karoubi (homological_complex C c) ≌ homological_complex (karoubi C) c`. -/
@[simps]
def unitIso : 𝟭 (Karoubi (HomologicalComplex C c)) ≅ functor ⋙ inverse
    where
  Hom :=
    { app := fun P =>
        { f :=
            { f := fun n => P.p.f n
              comm' := fun i j hij => by
                dsimp
                simp only [HomologicalComplex.Hom.comm, HomologicalComplex.Hom.comm_assoc,
                  homological_complex.p_idem] }
          comm := by ext n; dsimp; simp only [homological_complex.p_idem] }
      naturality' := fun P Q φ => by
        ext
        dsimp
        simp only [comp_f, HomologicalComplex.comp_f, homological_complex.comp_p_d, inverse.map_f_f,
          functor.map_f_f, homological_complex.p_comp_d] }
  inv :=
    { app := fun P =>
        { f :=
            { f := fun n => P.p.f n
              comm' := fun i j hij => by
                dsimp
                simp only [HomologicalComplex.Hom.comm, assoc, homological_complex.p_idem] }
          comm := by ext n; dsimp; simp only [homological_complex.p_idem] }
      naturality' := fun P Q φ => by
        ext
        dsimp
        simp only [comp_f, HomologicalComplex.comp_f, inverse.map_f_f, functor.map_f_f,
          homological_complex.comp_p_d, homological_complex.p_comp_d] }
  hom_inv_id' := by
    ext
    dsimp
    simp only [homological_complex.p_idem, comp_f, HomologicalComplex.comp_f, id_eq]
  inv_hom_id' := by
    ext
    dsimp
    simp only [homological_complex.p_idem, comp_f, HomologicalComplex.comp_f, id_eq,
      inverse.obj_p_f, functor.obj_X_p]
#align category_theory.idempotents.karoubi_homological_complex_equivalence.unit_iso CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.unitIso

end KaroubiHomologicalComplexEquivalence

variable (C) (c)

/- warning: category_theory.idempotents.karoubi_homological_complex_equivalence -> CategoryTheory.Idempotents.karoubiHomologicalComplexEquivalence is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u1}) [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.Preadditive.{u2, u1} C _inst_1] {ι : Type.{u3}} (c : ComplexShape.{u3} ι), CategoryTheory.Equivalence.{max u3 u2, max u3 u2, max u1 u3 u2, max (max u1 u2) u3 u2} (CategoryTheory.Idempotents.Karoubi.{max u1 u3 u2, max u3 u2} (HomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c) (HomologicalComplex.CategoryTheory.category.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c)) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{max u1 u3 u2, max u3 u2} (HomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c) (HomologicalComplex.CategoryTheory.category.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c)) (HomologicalComplex.{u2, max u1 u2, u3} ι (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.preadditive.{u1, u2} C _inst_1 _inst_2)) c) (HomologicalComplex.CategoryTheory.category.{u2, max u1 u2, u3} ι (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.preadditive.{u1, u2} C _inst_1 _inst_2)) c)
but is expected to have type
  forall (C : Type.{u1}) [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.Preadditive.{u2, u1} C _inst_1] {ι : Type.{u3}} (c : ComplexShape.{u3} ι), CategoryTheory.Equivalence.{max u2 u3, max u2 u3, max (max u2 u3) (max u3 u1) u2, max (max u3 u2 u1) u2} (CategoryTheory.Idempotents.Karoubi.{max (max u3 u1) u2, max u2 u3} (HomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c)) (HomologicalComplex.{u2, max u2 u1, u3} ι (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.instPreadditiveKaroubiInstCategoryKaroubi.{u1, u2} C _inst_1 _inst_2)) c) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{max (max u1 u2) u3, max u2 u3} (HomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u2, u1, u3} ι C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) c)) (HomologicalComplex.instCategoryHomologicalComplex.{u2, max u1 u2, u3} ι (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.instPreadditiveKaroubiInstCategoryKaroubi.{u1, u2} C _inst_1 _inst_2)) c)
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.karoubi_homological_complex_equivalence CategoryTheory.Idempotents.karoubiHomologicalComplexEquivalenceₓ'. -/
/-- The equivalence `karoubi (homological_complex C c) ≌ homological_complex (karoubi C) c`. -/
@[simps]
def karoubiHomologicalComplexEquivalence :
    Karoubi (HomologicalComplex C c) ≌ HomologicalComplex (Karoubi C) c
    where
  Functor := KaroubiHomologicalComplexEquivalence.functor
  inverse := KaroubiHomologicalComplexEquivalence.inverse
  unitIso := KaroubiHomologicalComplexEquivalence.unitIso
  counitIso := KaroubiHomologicalComplexEquivalence.counitIso
#align category_theory.idempotents.karoubi_homological_complex_equivalence CategoryTheory.Idempotents.karoubiHomologicalComplexEquivalence

variable (α : Type _) [AddRightCancelSemigroup α] [One α]

/- warning: category_theory.idempotents.karoubi_chain_complex_equivalence -> CategoryTheory.Idempotents.karoubiChainComplexEquivalence is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u1}) [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.Preadditive.{u2, u1} C _inst_1] (α : Type.{u3}) [_inst_3 : AddRightCancelSemigroup.{u3} α] [_inst_4 : One.{u3} α], CategoryTheory.Equivalence.{max u3 u2, max u3 u2, max u1 u3 u2, max (max u1 u2) u3 u2} (CategoryTheory.Idempotents.Karoubi.{max u1 u3 u2, max u3 u2} (ChainComplex.{u2, u1, u3} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) α _inst_3 _inst_4) (HomologicalComplex.CategoryTheory.category.{u2, u1, u3} α C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) (ComplexShape.down.{u3} α _inst_3 _inst_4))) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{max u1 u3 u2, max u3 u2} (ChainComplex.{u2, u1, u3} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) α _inst_3 _inst_4) (HomologicalComplex.CategoryTheory.category.{u2, u1, u3} α C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) (ComplexShape.down.{u3} α _inst_3 _inst_4))) (ChainComplex.{u2, max u1 u2, u3} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.preadditive.{u1, u2} C _inst_1 _inst_2)) α _inst_3 _inst_4) (HomologicalComplex.CategoryTheory.category.{u2, max u1 u2, u3} α (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.preadditive.{u1, u2} C _inst_1 _inst_2)) (ComplexShape.down.{u3} α _inst_3 _inst_4))
but is expected to have type
  forall (C : Type.{u1}) [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.Preadditive.{u2, u1} C _inst_1] (α : Type.{u3}) [_inst_3 : AddRightCancelSemigroup.{u3} α] [_inst_4 : One.{u3} α], CategoryTheory.Equivalence.{max u2 u3, max u2 u3, max (max u2 u3) (max u3 u1) u2, max (max u3 u2 u1) u2} (CategoryTheory.Idempotents.Karoubi.{max (max u3 u1) u2, max u2 u3} (ChainComplex.{u2, u1, u3} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) α _inst_3 _inst_4) (HomologicalComplex.instCategoryHomologicalComplex.{u2, u1, u3} α C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) (ComplexShape.down.{u3} α _inst_3 _inst_4))) (ChainComplex.{u2, max u2 u1, u3} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.instPreadditiveKaroubiInstCategoryKaroubi.{u1, u2} C _inst_1 _inst_2)) α _inst_3 _inst_4) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{max (max u1 u2) u3, max u2 u3} (ChainComplex.{u2, u1, u3} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) α _inst_3 _inst_4) (HomologicalComplex.instCategoryHomologicalComplex.{u2, u1, u3} α C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) (ComplexShape.down.{u3} α _inst_3 _inst_4))) (HomologicalComplex.instCategoryHomologicalComplex.{u2, max u1 u2, u3} α (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.instPreadditiveKaroubiInstCategoryKaroubi.{u1, u2} C _inst_1 _inst_2)) (ComplexShape.down.{u3} α _inst_3 _inst_4))
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.karoubi_chain_complex_equivalence CategoryTheory.Idempotents.karoubiChainComplexEquivalenceₓ'. -/
/-- The equivalence `karoubi (chain_complex C α) ≌ chain_complex (karoubi C) α`. -/
@[simps]
def karoubiChainComplexEquivalence : Karoubi (ChainComplex C α) ≌ ChainComplex (Karoubi C) α :=
  karoubiHomologicalComplexEquivalence C (ComplexShape.down α)
#align category_theory.idempotents.karoubi_chain_complex_equivalence CategoryTheory.Idempotents.karoubiChainComplexEquivalence

/- warning: category_theory.idempotents.karoubi_cochain_complex_equivalence -> CategoryTheory.Idempotents.karoubiCochainComplexEquivalence is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u1}) [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.Preadditive.{u2, u1} C _inst_1] (α : Type.{u3}) [_inst_3 : AddRightCancelSemigroup.{u3} α] [_inst_4 : One.{u3} α], CategoryTheory.Equivalence.{max u3 u2, max u3 u2, max u1 u3 u2, max (max u1 u2) u3 u2} (CategoryTheory.Idempotents.Karoubi.{max u1 u3 u2, max u3 u2} (CochainComplex.{u2, u1, u3} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) α _inst_3 _inst_4) (HomologicalComplex.CategoryTheory.category.{u2, u1, u3} α C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) (ComplexShape.up.{u3} α _inst_3 _inst_4))) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{max u1 u3 u2, max u3 u2} (CochainComplex.{u2, u1, u3} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) α _inst_3 _inst_4) (HomologicalComplex.CategoryTheory.category.{u2, u1, u3} α C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) (ComplexShape.up.{u3} α _inst_3 _inst_4))) (CochainComplex.{u2, max u1 u2, u3} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.preadditive.{u1, u2} C _inst_1 _inst_2)) α _inst_3 _inst_4) (HomologicalComplex.CategoryTheory.category.{u2, max u1 u2, u3} α (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.preadditive.{u1, u2} C _inst_1 _inst_2)) (ComplexShape.up.{u3} α _inst_3 _inst_4))
but is expected to have type
  forall (C : Type.{u1}) [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.Preadditive.{u2, u1} C _inst_1] (α : Type.{u3}) [_inst_3 : AddRightCancelSemigroup.{u3} α] [_inst_4 : One.{u3} α], CategoryTheory.Equivalence.{max u2 u3, max u2 u3, max (max u2 u3) (max u3 u1) u2, max (max u3 u2 u1) u2} (CategoryTheory.Idempotents.Karoubi.{max (max u3 u1) u2, max u2 u3} (CochainComplex.{u2, u1, u3} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) α _inst_3 _inst_4) (HomologicalComplex.instCategoryHomologicalComplex.{u2, u1, u3} α C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) (ComplexShape.up.{u3} α _inst_3 _inst_4))) (CochainComplex.{u2, max u2 u1, u3} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.instPreadditiveKaroubiInstCategoryKaroubi.{u1, u2} C _inst_1 _inst_2)) α _inst_3 _inst_4) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{max (max u1 u2) u3, max u2 u3} (CochainComplex.{u2, u1, u3} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) α _inst_3 _inst_4) (HomologicalComplex.instCategoryHomologicalComplex.{u2, u1, u3} α C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) (ComplexShape.up.{u3} α _inst_3 _inst_4))) (HomologicalComplex.instCategoryHomologicalComplex.{u2, max u1 u2, u3} α (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, max u1 u2} (CategoryTheory.Idempotents.Karoubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{u1, u2} C _inst_1) (CategoryTheory.Idempotents.instPreadditiveKaroubiInstCategoryKaroubi.{u1, u2} C _inst_1 _inst_2)) (ComplexShape.up.{u3} α _inst_3 _inst_4))
Case conversion may be inaccurate. Consider using '#align category_theory.idempotents.karoubi_cochain_complex_equivalence CategoryTheory.Idempotents.karoubiCochainComplexEquivalenceₓ'. -/
/-- The equivalence `karoubi (cochain_complex C α) ≌ cochain_complex (karoubi C) α`. -/
@[simps]
def karoubiCochainComplexEquivalence :
    Karoubi (CochainComplex C α) ≌ CochainComplex (Karoubi C) α :=
  karoubiHomologicalComplexEquivalence C (ComplexShape.up α)
#align category_theory.idempotents.karoubi_cochain_complex_equivalence CategoryTheory.Idempotents.karoubiCochainComplexEquivalence

instance [IsIdempotentComplete C] : IsIdempotentComplete (HomologicalComplex C c) :=
  by
  rw [is_idempotent_complete_iff_of_equivalence
      ((to_karoubi_equivalence C).mapHomologicalComplex c),
    ← is_idempotent_complete_iff_of_equivalence (karoubi_homological_complex_equivalence C c)]
  infer_instance

end Idempotents

end CategoryTheory

