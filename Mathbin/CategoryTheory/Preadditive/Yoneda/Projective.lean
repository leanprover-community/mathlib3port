/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison

! This file was ported from Lean 3 source module category_theory.preadditive.yoneda.projective
! leanprover-community/mathlib commit bd15ff41b70f5e2cc210f26f25a8d5c53b20d3de
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Preadditive.Yoneda.Basic
import Mathbin.CategoryTheory.Preadditive.Projective
import Mathbin.Algebra.Category.Group.EpiMono
import Mathbin.Algebra.Category.Module.EpiMono

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

An object is projective iff the preadditive coyoneda functor on it preserves epimorphisms.
-/


universe v u

open Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

section Preadditive

variable [Preadditive C]

namespace Projective

/- warning: category_theory.projective.projective_iff_preserves_epimorphisms_preadditive_coyoneda_obj -> CategoryTheory.Projective.projective_iff_preservesEpimorphisms_preadditiveCoyoneda_obj is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (P : C), Iff (CategoryTheory.Projective.{u1, u2} C _inst_1 P) (CategoryTheory.Functor.PreservesEpimorphisms.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (CategoryTheory.preadditiveCoyoneda.{u1, u2} C _inst_1 _inst_2) (Opposite.op.{succ u2} C P)))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (P : C), Iff (CategoryTheory.Projective.{u1, u2} C _inst_1 P) (CategoryTheory.Functor.PreservesEpimorphisms.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u2, max u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1))) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.preadditiveCoyoneda.{u1, u2} C _inst_1 _inst_2)) (Opposite.op.{succ u2} C P)))
Case conversion may be inaccurate. Consider using '#align category_theory.projective.projective_iff_preserves_epimorphisms_preadditive_coyoneda_obj CategoryTheory.Projective.projective_iff_preservesEpimorphisms_preadditiveCoyoneda_objₓ'. -/
theorem projective_iff_preservesEpimorphisms_preadditiveCoyoneda_obj (P : C) :
    Projective P ↔ (preadditiveCoyoneda.obj (op P)).PreservesEpimorphisms :=
  by
  rw [projective_iff_preserves_epimorphisms_coyoneda_obj]
  refine' ⟨fun h : (preadditive_coyoneda.obj (op P) ⋙ forget _).PreservesEpimorphisms => _, _⟩
  ·
    exact
      functor.preserves_epimorphisms_of_preserves_of_reflects (preadditive_coyoneda.obj (op P))
        (forget _)
  · intro
    exact (inferInstance : (preadditive_coyoneda.obj (op P) ⋙ forget _).PreservesEpimorphisms)
#align category_theory.projective.projective_iff_preserves_epimorphisms_preadditive_coyoneda_obj CategoryTheory.Projective.projective_iff_preservesEpimorphisms_preadditiveCoyoneda_obj

/- warning: category_theory.projective.projective_iff_preserves_epimorphisms_preadditive_coyoneda_obj' -> CategoryTheory.Projective.projective_iff_preservesEpimorphisms_preadditiveCoyoneda_obj' is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (P : C), Iff (CategoryTheory.Projective.{u1, u2} C _inst_1 P) (CategoryTheory.Functor.PreservesEpimorphisms.{u1, u1, u2, succ u1} C _inst_1 (ModuleCat.{u1, u1} (CategoryTheory.End.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1)) (Opposite.op.{succ u2} C P)) (CategoryTheory.Preadditive.CategoryTheory.End.ring.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Opposite.preadditive.{u2, u1} C _inst_1 _inst_2) (Opposite.op.{succ u2} C P))) (ModuleCat.moduleCategory.{u1, u1} (CategoryTheory.End.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1)) (Opposite.op.{succ u2} C P)) (CategoryTheory.Preadditive.CategoryTheory.End.ring.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Opposite.preadditive.{u2, u1} C _inst_1 _inst_2) (Opposite.op.{succ u2} C P))) (CategoryTheory.preadditiveCoyonedaObj.{u1, u2} C _inst_1 _inst_2 (Opposite.op.{succ u2} C P)))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] (P : C), Iff (CategoryTheory.Projective.{u1, u2} C _inst_1 P) (CategoryTheory.Functor.PreservesEpimorphisms.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u2, max u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1))) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.preadditiveCoyoneda.{u1, u2} C _inst_1 _inst_2)) (Opposite.op.{succ u2} C P)))
Case conversion may be inaccurate. Consider using '#align category_theory.projective.projective_iff_preserves_epimorphisms_preadditive_coyoneda_obj' CategoryTheory.Projective.projective_iff_preservesEpimorphisms_preadditiveCoyoneda_obj'ₓ'. -/
theorem projective_iff_preservesEpimorphisms_preadditiveCoyoneda_obj' (P : C) :
    Projective P ↔ (preadditiveCoyonedaObj (op P)).PreservesEpimorphisms :=
  by
  rw [projective_iff_preserves_epimorphisms_coyoneda_obj]
  refine' ⟨fun h : (preadditive_coyoneda_obj (op P) ⋙ forget _).PreservesEpimorphisms => _, _⟩
  ·
    exact
      functor.preserves_epimorphisms_of_preserves_of_reflects (preadditive_coyoneda_obj (op P))
        (forget _)
  · intro
    exact (inferInstance : (preadditive_coyoneda_obj (op P) ⋙ forget _).PreservesEpimorphisms)
#align category_theory.projective.projective_iff_preserves_epimorphisms_preadditive_coyoneda_obj' CategoryTheory.Projective.projective_iff_preservesEpimorphisms_preadditiveCoyoneda_obj'

end Projective

end Preadditive

end CategoryTheory

