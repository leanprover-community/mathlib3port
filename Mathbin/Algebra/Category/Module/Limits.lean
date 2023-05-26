/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.category.Module.limits
! leanprover-community/mathlib commit a87d22575d946e1e156fc1edd1e1269600a8a282
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Module.Basic
import Mathbin.Algebra.Category.Group.Limits
import Mathbin.Algebra.DirectLimit

/-!
# The category of R-modules has all limits

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/


open CategoryTheory

open CategoryTheory.Limits

universe v w u

-- `u` is determined by the ring, so can come last
noncomputable section

namespace ModuleCat

variable {R : Type u} [Ring R]

variable {J : Type v} [SmallCategory J]

/- warning: Module.add_comm_group_obj -> ModuleCat.addCommGroupObj is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u3}} [_inst_1 : Ring.{u3} R] {J : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u1 u2, u1, max u3 (succ (max u1 u2))} J _inst_2 (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1)) (j : J), AddCommGroup.{max u1 u2} (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_2 Type.{max u1 u2} CategoryTheory.types.{max u1 u2} (CategoryTheory.Functor.comp.{u1, max u1 u2, max u1 u2, u1, max u3 (succ (max u1 u2)), succ (max u1 u2)} J _inst_2 (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) Type.{max u1 u2} CategoryTheory.types.{max u1 u2} F (CategoryTheory.forget.{max u3 (succ (max u1 u2)), max u1 u2, max u1 u2} (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleConcreteCategory.{max u1 u2, u3} R _inst_1))) j)
but is expected to have type
  forall {R : Type.{u3}} [_inst_1 : Ring.{u3} R] {J : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u1 u2, u1, max (max u3 (succ u1)) (succ u2)} J _inst_2 (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1)) (j : J), AddCommGroup.{max u1 u2} (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u1, max (succ u1) (succ u2)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) Type.{max u1 u2} (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, max (succ u1) (succ u2)} Type.{max u1 u2} (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max (succ u1) (succ u2)} Type.{max u1 u2} CategoryTheory.types.{max u1 u2})) (CategoryTheory.Functor.toPrefunctor.{u1, max u1 u2, u1, max (succ u1) (succ u2)} J _inst_2 Type.{max u1 u2} CategoryTheory.types.{max u1 u2} (CategoryTheory.Functor.comp.{u1, max u1 u2, max u1 u2, u1, max (max u3 (succ u1)) (succ u2), max (succ u1) (succ u2)} J _inst_2 (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) Type.{max u1 u2} CategoryTheory.types.{max u1 u2} F (CategoryTheory.forget.{max u3 (succ (max u1 u2)), max u1 u2, max u1 u2} (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleConcreteCategory.{max u1 u2, u3} R _inst_1)))) j)
Case conversion may be inaccurate. Consider using '#align Module.add_comm_group_obj ModuleCat.addCommGroupObjₓ'. -/
instance addCommGroupObj (F : J ⥤ ModuleCat.{max v w} R) (j) :
    AddCommGroup ((F ⋙ forget (ModuleCat R)).obj j) :=
  by
  change AddCommGroup (F.obj j)
  infer_instance
#align Module.add_comm_group_obj ModuleCat.addCommGroupObj

/- warning: Module.module_obj -> ModuleCat.moduleObj is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u3}} [_inst_1 : Ring.{u3} R] {J : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u1 u2, u1, max u3 (succ (max u1 u2))} J _inst_2 (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1)) (j : J), Module.{u3, max u1 u2} R (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_2 Type.{max u1 u2} CategoryTheory.types.{max u1 u2} (CategoryTheory.Functor.comp.{u1, max u1 u2, max u1 u2, u1, max u3 (succ (max u1 u2)), succ (max u1 u2)} J _inst_2 (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) Type.{max u1 u2} CategoryTheory.types.{max u1 u2} F (CategoryTheory.forget.{max u3 (succ (max u1 u2)), max u1 u2, max u1 u2} (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleConcreteCategory.{max u1 u2, u3} R _inst_1))) j) (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{max u1 u2} (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_2 Type.{max u1 u2} CategoryTheory.types.{max u1 u2} (CategoryTheory.Functor.comp.{u1, max u1 u2, max u1 u2, u1, max u3 (succ (max u1 u2)), succ (max u1 u2)} J _inst_2 (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) Type.{max u1 u2} CategoryTheory.types.{max u1 u2} F (CategoryTheory.forget.{max u3 (succ (max u1 u2)), max u1 u2, max u1 u2} (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleConcreteCategory.{max u1 u2, u3} R _inst_1))) j) (ModuleCat.addCommGroupObj.{u1, u2, u3} R _inst_1 J _inst_2 F j))
but is expected to have type
  forall {R : Type.{u3}} [_inst_1 : Ring.{u3} R] {J : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u1 u2, u1, max (max u3 (succ u1)) (succ u2)} J _inst_2 (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1)) (j : J), Module.{u3, max u1 u2} R (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u1, max (succ u1) (succ u2)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) Type.{max u1 u2} (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, max (succ u1) (succ u2)} Type.{max u1 u2} (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max (succ u1) (succ u2)} Type.{max u1 u2} CategoryTheory.types.{max u1 u2})) (CategoryTheory.Functor.toPrefunctor.{u1, max u1 u2, u1, max (succ u1) (succ u2)} J _inst_2 Type.{max u1 u2} CategoryTheory.types.{max u1 u2} (CategoryTheory.Functor.comp.{u1, max u1 u2, max u1 u2, u1, max (max u3 (succ u1)) (succ u2), max (succ u1) (succ u2)} J _inst_2 (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) Type.{max u1 u2} CategoryTheory.types.{max u1 u2} F (CategoryTheory.forget.{max u3 (succ (max u1 u2)), max u1 u2, max u1 u2} (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleConcreteCategory.{max u1 u2, u3} R _inst_1)))) j) (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{max u1 u2} (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u1, max (succ u1) (succ u2)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) Type.{max u1 u2} (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, max (succ u1) (succ u2)} Type.{max u1 u2} (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max (succ u1) (succ u2)} Type.{max u1 u2} CategoryTheory.types.{max u1 u2})) (CategoryTheory.Functor.toPrefunctor.{u1, max u1 u2, u1, max (succ u1) (succ u2)} J _inst_2 Type.{max u1 u2} CategoryTheory.types.{max u1 u2} (CategoryTheory.Functor.comp.{u1, max u1 u2, max u1 u2, u1, max (max u3 (succ u1)) (succ u2), max (succ u1) (succ u2)} J _inst_2 (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) Type.{max u1 u2} CategoryTheory.types.{max u1 u2} F (CategoryTheory.forget.{max u3 (succ (max u1 u2)), max u1 u2, max u1 u2} (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleConcreteCategory.{max u1 u2, u3} R _inst_1)))) j) (ModuleCat.addCommGroupObj.{u1, u2, u3} R _inst_1 J _inst_2 F j))
Case conversion may be inaccurate. Consider using '#align Module.module_obj ModuleCat.moduleObjₓ'. -/
instance moduleObj (F : J ⥤ ModuleCat.{max v w} R) (j) :
    Module R ((F ⋙ forget (ModuleCat R)).obj j) :=
  by
  change Module R (F.obj j)
  infer_instance
#align Module.module_obj ModuleCat.moduleObj

/- warning: Module.sections_submodule -> ModuleCat.sectionsSubmodule is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u3}} [_inst_1 : Ring.{u3} R] {J : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u1 u2, u1, max u3 (succ (max u1 u2))} J _inst_2 (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1)), Submodule.{u3, max u1 u2} R (forall (j : J), coeSort.{max (succ u3) (succ (succ (max u1 u2))), succ (succ (max u1 u2))} (ModuleCat.{max u1 u2, u3} R _inst_1) Type.{max u1 u2} (ModuleCat.hasCoeToSort.{max u1 u2, u3} R _inst_1) (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, max u3 (succ (max u1 u2))} J _inst_2 (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) F j)) (Ring.toSemiring.{u3} R _inst_1) (Pi.addCommMonoid.{u1, max u1 u2} J (fun (j : J) => coeSort.{max (succ u3) (succ (succ (max u1 u2))), succ (succ (max u1 u2))} (ModuleCat.{max u1 u2, u3} R _inst_1) Type.{max u1 u2} (ModuleCat.hasCoeToSort.{max u1 u2, u3} R _inst_1) (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, max u3 (succ (max u1 u2))} J _inst_2 (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) F j)) (fun (i : J) => AddCommGroup.toAddCommMonoid.{max u1 u2} (coeSort.{max (succ u3) (succ (succ (max u1 u2))), succ (succ (max u1 u2))} (ModuleCat.{max u1 u2, u3} R _inst_1) Type.{max u1 u2} (ModuleCat.hasCoeToSort.{max u1 u2, u3} R _inst_1) (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, max u3 (succ (max u1 u2))} J _inst_2 (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) F i)) (ModuleCat.isAddCommGroup.{max u1 u2, u3} R _inst_1 (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, max u3 (succ (max u1 u2))} J _inst_2 (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) F i)))) (Pi.module.{u1, max u1 u2, u3} J (fun (j : J) => coeSort.{max (succ u3) (succ (succ (max u1 u2))), succ (succ (max u1 u2))} (ModuleCat.{max u1 u2, u3} R _inst_1) Type.{max u1 u2} (ModuleCat.hasCoeToSort.{max u1 u2, u3} R _inst_1) (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, max u3 (succ (max u1 u2))} J _inst_2 (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) F j)) R (Ring.toSemiring.{u3} R _inst_1) (fun (i : J) => AddCommGroup.toAddCommMonoid.{max u1 u2} (coeSort.{max (succ u3) (succ (succ (max u1 u2))), succ (succ (max u1 u2))} (ModuleCat.{max u1 u2, u3} R _inst_1) Type.{max u1 u2} (ModuleCat.hasCoeToSort.{max u1 u2, u3} R _inst_1) (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, max u3 (succ (max u1 u2))} J _inst_2 (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) F i)) (ModuleCat.isAddCommGroup.{max u1 u2, u3} R _inst_1 (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, max u3 (succ (max u1 u2))} J _inst_2 (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) F i))) (fun (i : J) => ModuleCat.isModule.{max u1 u2, u3} R _inst_1 (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, max u3 (succ (max u1 u2))} J _inst_2 (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) F i)))
but is expected to have type
  forall {R : Type.{u3}} [_inst_1 : Ring.{u3} R] {J : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u1 u2, u1, max (max u3 (succ u1)) (succ u2)} J _inst_2 (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1)), Submodule.{u3, max u1 u2} R (forall (j : J), ModuleCat.carrier.{max u1 u2, u3} R _inst_1 (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u1, max (max u3 (succ u1)) (succ u2)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, max (max u3 (succ u1)) (succ u2)} (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max (max u3 (succ u1)) (succ u2)} (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, max u1 u2, u1, max (max u3 (succ u1)) (succ u2)} J _inst_2 (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) F) j)) (Ring.toSemiring.{u3} R _inst_1) (Pi.addCommMonoid.{u1, max u1 u2} J (fun (j : J) => ModuleCat.carrier.{max u1 u2, u3} R _inst_1 (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u1, max (max u3 (succ u1)) (succ u2)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, max (max u3 (succ u1)) (succ u2)} (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max (max u3 (succ u1)) (succ u2)} (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, max u1 u2, u1, max (max u3 (succ u1)) (succ u2)} J _inst_2 (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) F) j)) (fun (i : J) => AddCommGroup.toAddCommMonoid.{max u1 u2} (ModuleCat.carrier.{max u1 u2, u3} R _inst_1 (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u1, max (max u3 (succ u1)) (succ u2)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, max (max u3 (succ u1)) (succ u2)} (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max (max u3 (succ u1)) (succ u2)} (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, max u1 u2, u1, max (max u3 (succ u1)) (succ u2)} J _inst_2 (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) F) i)) (ModuleCat.isAddCommGroup.{max u1 u2, u3} R _inst_1 (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u1, max (max u3 (succ u1)) (succ u2)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, max (max u3 (succ u1)) (succ u2)} (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max (max u3 (succ u1)) (succ u2)} (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, max u1 u2, u1, max (max u3 (succ u1)) (succ u2)} J _inst_2 (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) F) i)))) (Pi.module.{u1, max u1 u2, u3} J (fun (j : J) => ModuleCat.carrier.{max u1 u2, u3} R _inst_1 (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u1, max (max u3 (succ u1)) (succ u2)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, max (max u3 (succ u1)) (succ u2)} (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max (max u3 (succ u1)) (succ u2)} (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, max u1 u2, u1, max (max u3 (succ u1)) (succ u2)} J _inst_2 (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) F) j)) R (Ring.toSemiring.{u3} R _inst_1) (fun (i : J) => AddCommGroup.toAddCommMonoid.{max u1 u2} (ModuleCat.carrier.{max u1 u2, u3} R _inst_1 (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u1, max (max u3 (succ u1)) (succ u2)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, max (max u3 (succ u1)) (succ u2)} (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max (max u3 (succ u1)) (succ u2)} (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, max u1 u2, u1, max (max u3 (succ u1)) (succ u2)} J _inst_2 (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) F) i)) (ModuleCat.isAddCommGroup.{max u1 u2, u3} R _inst_1 (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u1, max (max u3 (succ u1)) (succ u2)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, max (max u3 (succ u1)) (succ u2)} (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max (max u3 (succ u1)) (succ u2)} (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, max u1 u2, u1, max (max u3 (succ u1)) (succ u2)} J _inst_2 (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) F) i))) (fun (i : J) => ModuleCat.isModule.{max u1 u2, u3} R _inst_1 (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u1, max (max u3 (succ u1)) (succ u2)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, max (max u3 (succ u1)) (succ u2)} (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max (max u3 (succ u1)) (succ u2)} (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, max u1 u2, u1, max (max u3 (succ u1)) (succ u2)} J _inst_2 (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) F) i)))
Case conversion may be inaccurate. Consider using '#align Module.sections_submodule ModuleCat.sectionsSubmoduleₓ'. -/
/-- The flat sections of a functor into `Module R` form a submodule of all sections.
-/
def sectionsSubmodule (F : J ⥤ ModuleCat.{max v w} R) : Submodule R (∀ j, F.obj j) :=
  {
    AddGroupCat.sectionsAddSubgroup
      (F ⋙
        forget₂ (ModuleCat R) AddCommGroupCat.{max v w} ⋙
          forget₂ AddCommGroupCat
            AddGroupCat.{max v
                w}) with
    carrier := (F ⋙ forget (ModuleCat R)).sections
    smul_mem' := fun r s sh j j' f =>
      by
      simp only [forget_map_eq_coe, functor.comp_map, Pi.smul_apply, LinearMap.map_smul]
      dsimp [functor.sections] at sh
      rw [sh f] }
#align Module.sections_submodule ModuleCat.sectionsSubmodule

#print ModuleCat.limitAddCommMonoid /-
-- Adding the following instance speeds up `limit_module` noticeably,
-- by preventing a bad unfold of `limit_add_comm_group`.
instance limitAddCommMonoid (F : J ⥤ ModuleCat R) :
    AddCommMonoid (Types.limitCone (F ⋙ forget (ModuleCat.{max v w} R))).pt :=
  show AddCommMonoid (sectionsSubmodule F) by infer_instance
#align Module.limit_add_comm_monoid ModuleCat.limitAddCommMonoid
-/

#print ModuleCat.limitAddCommGroup /-
instance limitAddCommGroup (F : J ⥤ ModuleCat R) :
    AddCommGroup (Types.limitCone (F ⋙ forget (ModuleCat.{max v w} R))).pt :=
  show AddCommGroup (sectionsSubmodule F) by infer_instance
#align Module.limit_add_comm_group ModuleCat.limitAddCommGroup
-/

#print ModuleCat.limitModule /-
instance limitModule (F : J ⥤ ModuleCat R) :
    Module R (Types.limitCone (F ⋙ forget (ModuleCat.{max v w} R))).pt :=
  show Module R (sectionsSubmodule F) by infer_instance
#align Module.limit_module ModuleCat.limitModule
-/

/- warning: Module.limit_π_linear_map -> ModuleCat.limitπLinearMap is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u3}} [_inst_1 : Ring.{u3} R] {J : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u1 u2, u1, max u3 (succ (max u1 u2))} J _inst_2 (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1)) (j : J), LinearMap.{u3, u3, max u1 u2, max u1 u2} R R (Ring.toSemiring.{u3} R _inst_1) (Ring.toSemiring.{u3} R _inst_1) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R (Ring.toSemiring.{u3} R _inst_1))) (CategoryTheory.Limits.Cone.pt.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_2 Type.{max u1 u2} CategoryTheory.types.{max u1 u2} (CategoryTheory.Functor.comp.{u1, max u1 u2, max u1 u2, u1, max u3 (succ (max u1 u2)), succ (max u1 u2)} J _inst_2 (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) Type.{max u1 u2} CategoryTheory.types.{max u1 u2} F (CategoryTheory.forget.{max u3 (succ (max u1 u2)), max u1 u2, max u1 u2} (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleConcreteCategory.{max u1 u2, u3} R _inst_1))) (CategoryTheory.Limits.Types.limitCone.{u1, u2} J _inst_2 (CategoryTheory.Functor.comp.{u1, max u1 u2, max u1 u2, u1, max u3 (succ (max u1 u2)), succ (max u1 u2)} J _inst_2 (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) Type.{max u1 u2} CategoryTheory.types.{max u1 u2} F (CategoryTheory.forget.{max u3 (succ (max u1 u2)), max u1 u2, max u1 u2} (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleConcreteCategory.{max u1 u2, u3} R _inst_1))))) (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_2 Type.{max u1 u2} CategoryTheory.types.{max u1 u2} (CategoryTheory.Functor.comp.{u1, max u1 u2, max u1 u2, u1, max u3 (succ (max u1 u2)), succ (max u1 u2)} J _inst_2 (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) Type.{max u1 u2} CategoryTheory.types.{max u1 u2} F (CategoryTheory.forget.{max u3 (succ (max u1 u2)), max u1 u2, max u1 u2} (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleConcreteCategory.{max u1 u2, u3} R _inst_1))) j) (ModuleCat.limitAddCommMonoid.{u1, u2, u3} R _inst_1 J _inst_2 F) (AddCommGroup.toAddCommMonoid.{max u1 u2} (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_2 Type.{max u1 u2} CategoryTheory.types.{max u1 u2} (CategoryTheory.Functor.comp.{u1, max u1 u2, max u1 u2, u1, max u3 (succ (max u1 u2)), succ (max u1 u2)} J _inst_2 (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) Type.{max u1 u2} CategoryTheory.types.{max u1 u2} F (CategoryTheory.forget.{max u3 (succ (max u1 u2)), max u1 u2, max u1 u2} (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleConcreteCategory.{max u1 u2, u3} R _inst_1))) j) (ModuleCat.addCommGroupObj.{u1, u2, u3} R _inst_1 J _inst_2 F j)) (ModuleCat.limitModule.{u1, u2, u3} R _inst_1 J _inst_2 F) (ModuleCat.moduleObj.{u1, u2, u3} R _inst_1 J _inst_2 F j)
but is expected to have type
  forall {R : Type.{u3}} [_inst_1 : Ring.{u3} R] {J : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u1 u2, u1, max (max u3 (succ u1)) (succ u2)} J _inst_2 (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1)) (j : J), LinearMap.{u3, u3, max u1 u2, max u1 u2} R R (Ring.toSemiring.{u3} R _inst_1) (Ring.toSemiring.{u3} R _inst_1) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R (Ring.toSemiring.{u3} R _inst_1))) (CategoryTheory.Limits.Cone.pt.{u1, max u1 u2, u1, max (succ u1) (succ u2)} J _inst_2 TypeMax.{u1, u2} CategoryTheory.types.{max u2 u1} (CategoryTheory.Functor.comp.{u1, max u1 u2, max u2 u1, u1, max (max u3 (succ u1)) (succ u2), max (succ u2) (succ u1)} J _inst_2 (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) TypeMax.{u1, u2} CategoryTheory.types.{max u2 u1} F (CategoryTheory.forget.{max (max (succ u1) (succ u2)) u3, max u1 u2, max u1 u2} (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleConcreteCategory.{max u1 u2, u3} R _inst_1))) (CategoryTheory.Limits.Types.limitCone.{u1, u2} J _inst_2 (CategoryTheory.Functor.comp.{u1, max u1 u2, max u2 u1, u1, max (max u3 (succ u1)) (succ u2), max (succ u2) (succ u1)} J _inst_2 (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) TypeMax.{u1, u2} CategoryTheory.types.{max u2 u1} F (CategoryTheory.forget.{max (max (succ u1) (succ u2)) u3, max u1 u2, max u1 u2} (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleConcreteCategory.{max u1 u2, u3} R _inst_1))))) (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u1, max (succ u1) (succ u2)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) Type.{max u1 u2} (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, max (succ u1) (succ u2)} Type.{max u1 u2} (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max (succ u1) (succ u2)} Type.{max u1 u2} CategoryTheory.types.{max u1 u2})) (CategoryTheory.Functor.toPrefunctor.{u1, max u1 u2, u1, max (succ u1) (succ u2)} J _inst_2 Type.{max u1 u2} CategoryTheory.types.{max u1 u2} (CategoryTheory.Functor.comp.{u1, max u1 u2, max u1 u2, u1, max (max u3 (succ u1)) (succ u2), max (succ u1) (succ u2)} J _inst_2 (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) Type.{max u1 u2} CategoryTheory.types.{max u1 u2} F (CategoryTheory.forget.{max u3 (succ (max u1 u2)), max u1 u2, max u1 u2} (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleConcreteCategory.{max u1 u2, u3} R _inst_1)))) j) (ModuleCat.limitAddCommMonoid.{u1, u2, u3} R _inst_1 J _inst_2 F) (AddCommGroup.toAddCommMonoid.{max u1 u2} (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u1, max (succ u1) (succ u2)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_2)) Type.{max u1 u2} (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, max (succ u1) (succ u2)} Type.{max u1 u2} (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max (succ u1) (succ u2)} Type.{max u1 u2} CategoryTheory.types.{max u1 u2})) (CategoryTheory.Functor.toPrefunctor.{u1, max u1 u2, u1, max (succ u1) (succ u2)} J _inst_2 Type.{max u1 u2} CategoryTheory.types.{max u1 u2} (CategoryTheory.Functor.comp.{u1, max u1 u2, max u1 u2, u1, max (max u3 (succ u1)) (succ u2), max (succ u1) (succ u2)} J _inst_2 (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) Type.{max u1 u2} CategoryTheory.types.{max u1 u2} F (CategoryTheory.forget.{max u3 (succ (max u1 u2)), max u1 u2, max u1 u2} (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleConcreteCategory.{max u1 u2, u3} R _inst_1)))) j) (ModuleCat.addCommGroupObj.{u1, u2, u3} R _inst_1 J _inst_2 F j)) (ModuleCat.limitModule.{u1, u2, u3} R _inst_1 J _inst_2 F) (ModuleCat.moduleObj.{u1, u2, u3} R _inst_1 J _inst_2 F j)
Case conversion may be inaccurate. Consider using '#align Module.limit_π_linear_map ModuleCat.limitπLinearMapₓ'. -/
/-- `limit.π (F ⋙ forget Ring) j` as a `ring_hom`. -/
def limitπLinearMap (F : J ⥤ ModuleCat R) (j) :
    (Types.limitCone (F ⋙ forget (ModuleCat.{max v w} R))).pt →ₗ[R] (F ⋙ forget (ModuleCat R)).obj j
    where
  toFun := (Types.limitCone (F ⋙ forget (ModuleCat R))).π.app j
  map_smul' x y := rfl
  map_add' x y := rfl
#align Module.limit_π_linear_map ModuleCat.limitπLinearMap

namespace HasLimits

#print ModuleCat.HasLimits.limitCone /-
-- The next two definitions are used in the construction of `has_limits (Module R)`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.is_limit F`.
/-- Construction of a limit cone in `Module R`.
(Internal use only; use the limits API.)
-/
def limitCone (F : J ⥤ ModuleCat.{max v w} R) : Cone F
    where
  pt := ModuleCat.of R (Types.limitCone (F ⋙ forget _)).pt
  π :=
    { app := limitπLinearMap F
      naturality' := fun j j' f =>
        LinearMap.coe_injective ((Types.limitCone (F ⋙ forget _)).π.naturality f) }
#align Module.has_limits.limit_cone ModuleCat.HasLimits.limitCone
-/

#print ModuleCat.HasLimits.limitConeIsLimit /-
/-- Witness that the limit cone in `Module R` is a limit cone.
(Internal use only; use the limits API.)
-/
def limitConeIsLimit (F : J ⥤ ModuleCat.{max v w} R) : IsLimit (limitCone F) := by
  refine'
            is_limit.of_faithful (forget (ModuleCat R)) (types.limit_cone_is_limit _)
              (fun s => ⟨_, _, _⟩) fun s => rfl <;>
          intros <;>
        ext j <;>
      simp only [Subtype.coe_mk, functor.map_cone_π_app, forget_map_eq_coe, LinearMap.map_add,
        LinearMap.map_smul] <;>
    rfl
#align Module.has_limits.limit_cone_is_limit ModuleCat.HasLimits.limitConeIsLimit
-/

end HasLimits

open HasLimits

/- ./././Mathport/Syntax/Translate/Command.lean:322:38: unsupported irreducible non-definition -/
#print ModuleCat.hasLimitsOfSize /-
/-- The category of R-modules has all limits. -/
irreducible_def hasLimitsOfSize : HasLimitsOfSize.{v, v} (ModuleCat.{max v w} R) :=
  {
    HasLimitsOfShape := fun J 𝒥 =>
      {
        HasLimit := fun F =>
          has_limit.mk
            { Cone := limit_cone F
              IsLimit := limit_cone_is_limit F } } }
#align Module.has_limits_of_size ModuleCat.hasLimitsOfSize
-/

#print ModuleCat.hasLimits /-
instance hasLimits : HasLimits (ModuleCat.{w} R) :=
  ModuleCat.hasLimitsOfSize.{w, w, u}
#align Module.has_limits ModuleCat.hasLimits
-/

/- warning: Module.forget₂_AddCommGroup_preserves_limits_aux -> ModuleCat.forget₂AddCommGroupPreservesLimitsAux is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u3}} [_inst_1 : Ring.{u3} R] {J : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u1 u2, u1, max u3 (succ (max u1 u2))} J _inst_2 (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1)), CategoryTheory.Limits.IsLimit.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_2 AddCommGroupCat.{max u1 u2} AddCommGroupCat.largeCategory.{max u1 u2} (CategoryTheory.Functor.comp.{u1, max u1 u2, max u1 u2, u1, max u3 (succ (max u1 u2)), succ (max u1 u2)} J _inst_2 (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) AddCommGroupCat.{max u1 u2} AddCommGroupCat.largeCategory.{max u1 u2} F (CategoryTheory.forget₂.{max u3 (succ (max u1 u2)), succ (max u1 u2), max u1 u2, max u1 u2, max u1 u2} (ModuleCat.{max u1 u2, u3} R _inst_1) AddCommGroupCat.{max u1 u2} (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleConcreteCategory.{max u1 u2, u3} R _inst_1) AddCommGroupCat.largeCategory.{max u1 u2} AddCommGroupCat.concreteCategory.{max u1 u2} (ModuleCat.hasForgetToAddCommGroup.{u3, max u1 u2} R _inst_1))) (CategoryTheory.Functor.mapCone.{u1, max u1 u2, max u1 u2, u1, max u3 (succ (max u1 u2)), succ (max u1 u2)} J _inst_2 (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) AddCommGroupCat.{max u1 u2} AddCommGroupCat.largeCategory.{max u1 u2} F (CategoryTheory.forget₂.{max u3 (succ (max u1 u2)), succ (max u1 u2), max u1 u2, max u1 u2, max u1 u2} (ModuleCat.{max u1 u2, u3} R _inst_1) AddCommGroupCat.{max u1 u2} (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleConcreteCategory.{max u1 u2, u3} R _inst_1) AddCommGroupCat.largeCategory.{max u1 u2} AddCommGroupCat.concreteCategory.{max u1 u2} (ModuleCat.hasForgetToAddCommGroup.{u3, max u1 u2} R _inst_1)) (ModuleCat.HasLimits.limitCone.{u1, u2, u3} R _inst_1 J _inst_2 F))
but is expected to have type
  forall {R : Type.{u3}} [_inst_1 : Ring.{u3} R] {J : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u1 u2, u1, max (max u3 (succ u1)) (succ u2)} J _inst_2 (ModuleCat.ModuleCatMax.{u3, u1, u2} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1)), CategoryTheory.Limits.IsLimit.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_2 AddCommGroupCat.{max u1 u2} instAddCommGroupCatLargeCategory.{max u1 u2} (CategoryTheory.Functor.comp.{u1, max u1 u2, max u1 u2, u1, max u3 (succ (max u1 u2)), succ (max u1 u2)} J _inst_2 (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) AddCommGroupCat.{max u1 u2} instAddCommGroupCatLargeCategory.{max u1 u2} F (CategoryTheory.forget₂.{max u3 (succ (max u1 u2)), succ (max u1 u2), max u1 u2, max u1 u2, max u1 u2} (ModuleCat.{max u1 u2, u3} R _inst_1) AddCommGroupCat.{max u1 u2} (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleConcreteCategory.{max u1 u2, u3} R _inst_1) instAddCommGroupCatLargeCategory.{max u1 u2} AddCommGroupCat.concreteCategory.{max u1 u2} (ModuleCat.hasForgetToAddCommGroup.{u3, max u1 u2} R _inst_1))) (CategoryTheory.Functor.mapCone.{u1, max u1 u2, max u1 u2, u1, max u3 (succ (max u1 u2)), succ (max u1 u2)} J _inst_2 (ModuleCat.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) AddCommGroupCat.{max u1 u2} instAddCommGroupCatLargeCategory.{max u1 u2} (CategoryTheory.forget₂.{max u3 (succ (max u1 u2)), succ (max u1 u2), max u1 u2, max u1 u2, max u1 u2} (ModuleCat.{max u1 u2, u3} R _inst_1) AddCommGroupCat.{max u1 u2} (ModuleCat.moduleCategory.{max u1 u2, u3} R _inst_1) (ModuleCat.moduleConcreteCategory.{max u1 u2, u3} R _inst_1) instAddCommGroupCatLargeCategory.{max u1 u2} AddCommGroupCat.concreteCategory.{max u1 u2} (ModuleCat.hasForgetToAddCommGroup.{u3, max u1 u2} R _inst_1)) F (ModuleCat.HasLimits.limitCone.{u1, u2, u3} R _inst_1 J _inst_2 F))
Case conversion may be inaccurate. Consider using '#align Module.forget₂_AddCommGroup_preserves_limits_aux ModuleCat.forget₂AddCommGroupPreservesLimitsAuxₓ'. -/
/-- An auxiliary declaration to speed up typechecking.
-/
def forget₂AddCommGroupPreservesLimitsAux (F : J ⥤ ModuleCat.{max v w} R) :
    IsLimit ((forget₂ (ModuleCat R) AddCommGroupCat).mapCone (limitCone F)) :=
  AddCommGroupCat.limitConeIsLimit (F ⋙ forget₂ (ModuleCat R) AddCommGroupCat.{max v w})
#align Module.forget₂_AddCommGroup_preserves_limits_aux ModuleCat.forget₂AddCommGroupPreservesLimitsAux

#print ModuleCat.forget₂AddCommGroupPreservesLimitsOfSize /-
/-- The forgetful functor from R-modules to abelian groups preserves all limits.
-/
instance forget₂AddCommGroupPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ (ModuleCat R) AddCommGroupCat.{max v w})
    where PreservesLimitsOfShape J 𝒥 :=
    {
      PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
          (forget₂_AddCommGroup_preserves_limits_aux F) }
#align Module.forget₂_AddCommGroup_preserves_limits_of_size ModuleCat.forget₂AddCommGroupPreservesLimitsOfSize
-/

#print ModuleCat.forget₂AddCommGroupPreservesLimits /-
instance forget₂AddCommGroupPreservesLimits :
    PreservesLimits (forget₂ (ModuleCat R) AddCommGroupCat.{w}) :=
  ModuleCat.forget₂AddCommGroupPreservesLimitsOfSize.{w, w}
#align Module.forget₂_AddCommGroup_preserves_limits ModuleCat.forget₂AddCommGroupPreservesLimits
-/

#print ModuleCat.forgetPreservesLimitsOfSize /-
/-- The forgetful functor from R-modules to types preserves all limits.
-/
instance forgetPreservesLimitsOfSize : PreservesLimitsOfSize.{v, v} (forget (ModuleCat.{max v w} R))
    where PreservesLimitsOfShape J 𝒥 :=
    {
      PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
          (types.limit_cone_is_limit (F ⋙ forget _)) }
#align Module.forget_preserves_limits_of_size ModuleCat.forgetPreservesLimitsOfSize
-/

#print ModuleCat.forgetPreservesLimits /-
instance forgetPreservesLimits : PreservesLimits (forget (ModuleCat.{w} R)) :=
  ModuleCat.forgetPreservesLimitsOfSize.{w, w}
#align Module.forget_preserves_limits ModuleCat.forgetPreservesLimits
-/

section DirectLimit

open Module

variable {ι : Type v}

variable [dec_ι : DecidableEq ι] [Preorder ι]

variable (G : ι → Type v)

variable [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]

variable (f : ∀ i j, i ≤ j → G i →ₗ[R] G j) [DirectedSystem G fun i j h => f i j h]

/- warning: Module.direct_limit_diagram -> ModuleCat.directLimitDiagram is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u2}} [_inst_1 : Ring.{u2} R] {ι : Type.{u1}} [_inst_3 : Preorder.{u1} ι] (G : ι -> Type.{u1}) [_inst_4 : forall (i : ι), AddCommGroup.{u1} (G i)] [_inst_5 : forall (i : ι), Module.{u2, u1} R (G i) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} (G i) (_inst_4 i))] (f : forall (i : ι) (j : ι), (LE.le.{u1} ι (Preorder.toHasLe.{u1} ι _inst_3) i j) -> (LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (G i) (G j) (AddCommGroup.toAddCommMonoid.{u1} (G i) (_inst_4 i)) (AddCommGroup.toAddCommMonoid.{u1} (G j) (_inst_4 j)) (_inst_5 i) (_inst_5 j))) [_inst_6 : DirectedSystem.{u1, u1} ι _inst_3 G (fun (i : ι) (j : ι) (h : LE.le.{u1} ι (Preorder.toHasLe.{u1} ι _inst_3) i j) => coeFn.{succ u1, succ u1} (LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (G i) (G j) (AddCommGroup.toAddCommMonoid.{u1} (G i) (_inst_4 i)) (AddCommGroup.toAddCommMonoid.{u1} (G j) (_inst_4 j)) (_inst_5 i) (_inst_5 j)) (fun (_x : LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (G i) (G j) (AddCommGroup.toAddCommMonoid.{u1} (G i) (_inst_4 i)) (AddCommGroup.toAddCommMonoid.{u1} (G j) (_inst_4 j)) (_inst_5 i) (_inst_5 j)) => (G i) -> (G j)) (LinearMap.hasCoeToFun.{u2, u2, u1, u1} R R (G i) (G j) (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} (G i) (_inst_4 i)) (AddCommGroup.toAddCommMonoid.{u1} (G j) (_inst_4 j)) (_inst_5 i) (_inst_5 j) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) (f i j h))], CategoryTheory.Functor.{u1, u1, u1, max u2 (succ u1)} ι (Preorder.smallCategory.{u1} ι _inst_3) (ModuleCat.{u1, u2} R _inst_1) (ModuleCat.moduleCategory.{u1, u2} R _inst_1)
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : Ring.{u2} R] {ι : Type.{u1}} [_inst_3 : Preorder.{u1} ι] (G : ι -> Type.{u1}) [_inst_4 : forall (i : ι), AddCommGroup.{u1} (G i)] [_inst_5 : forall (i : ι), Module.{u2, u1} R (G i) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} (G i) (_inst_4 i))] (f : forall (i : ι) (j : ι), (LE.le.{u1} ι (Preorder.toLE.{u1} ι _inst_3) i j) -> (LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (G i) (G j) (AddCommGroup.toAddCommMonoid.{u1} (G i) (_inst_4 i)) (AddCommGroup.toAddCommMonoid.{u1} (G j) (_inst_4 j)) (_inst_5 i) (_inst_5 j))) [_inst_6 : DirectedSystem.{u1, u1} ι _inst_3 G (fun (i : ι) (j : ι) (h : LE.le.{u1} ι (Preorder.toLE.{u1} ι _inst_3) i j) => FunLike.coe.{succ u1, succ u1, succ u1} (LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (G i) (G j) (AddCommGroup.toAddCommMonoid.{u1} (G i) (_inst_4 i)) (AddCommGroup.toAddCommMonoid.{u1} (G j) (_inst_4 j)) (_inst_5 i) (_inst_5 j)) (G i) (fun (_x : G i) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : G i) => G j) _x) (LinearMap.instFunLikeLinearMap.{u2, u2, u1, u1} R R (G i) (G j) (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} (G i) (_inst_4 i)) (AddCommGroup.toAddCommMonoid.{u1} (G j) (_inst_4 j)) (_inst_5 i) (_inst_5 j) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) (f i j h))], CategoryTheory.Functor.{u1, u1, u1, max u2 (succ u1)} ι (Preorder.smallCategory.{u1} ι _inst_3) (ModuleCat.{u1, u2} R _inst_1) (ModuleCat.moduleCategory.{u1, u2} R _inst_1)
Case conversion may be inaccurate. Consider using '#align Module.direct_limit_diagram ModuleCat.directLimitDiagramₓ'. -/
/-- The diagram (in the sense of `category_theory`)
 of an unbundled `direct_limit` of modules. -/
@[simps]
def directLimitDiagram : ι ⥤ ModuleCat R
    where
  obj i := ModuleCat.of R (G i)
  map i j hij := f i j hij.le
  map_id' i := by
    apply LinearMap.ext
    intro x
    apply Module.DirectedSystem.map_self
  map_comp' i j k hij hjk := by
    apply LinearMap.ext
    intro x
    symm
    apply Module.DirectedSystem.map_map
#align Module.direct_limit_diagram ModuleCat.directLimitDiagram

variable [DecidableEq ι]

/- warning: Module.direct_limit_cocone -> ModuleCat.directLimitCocone is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u2}} [_inst_1 : Ring.{u2} R] {ι : Type.{u1}} [_inst_3 : Preorder.{u1} ι] (G : ι -> Type.{u1}) [_inst_4 : forall (i : ι), AddCommGroup.{u1} (G i)] [_inst_5 : forall (i : ι), Module.{u2, u1} R (G i) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} (G i) (_inst_4 i))] (f : forall (i : ι) (j : ι), (LE.le.{u1} ι (Preorder.toHasLe.{u1} ι _inst_3) i j) -> (LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (G i) (G j) (AddCommGroup.toAddCommMonoid.{u1} (G i) (_inst_4 i)) (AddCommGroup.toAddCommMonoid.{u1} (G j) (_inst_4 j)) (_inst_5 i) (_inst_5 j))) [_inst_6 : DirectedSystem.{u1, u1} ι _inst_3 G (fun (i : ι) (j : ι) (h : LE.le.{u1} ι (Preorder.toHasLe.{u1} ι _inst_3) i j) => coeFn.{succ u1, succ u1} (LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (G i) (G j) (AddCommGroup.toAddCommMonoid.{u1} (G i) (_inst_4 i)) (AddCommGroup.toAddCommMonoid.{u1} (G j) (_inst_4 j)) (_inst_5 i) (_inst_5 j)) (fun (_x : LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (G i) (G j) (AddCommGroup.toAddCommMonoid.{u1} (G i) (_inst_4 i)) (AddCommGroup.toAddCommMonoid.{u1} (G j) (_inst_4 j)) (_inst_5 i) (_inst_5 j)) => (G i) -> (G j)) (LinearMap.hasCoeToFun.{u2, u2, u1, u1} R R (G i) (G j) (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} (G i) (_inst_4 i)) (AddCommGroup.toAddCommMonoid.{u1} (G j) (_inst_4 j)) (_inst_5 i) (_inst_5 j) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) (f i j h))] [_inst_7 : DecidableEq.{succ u1} ι], CategoryTheory.Limits.Cocone.{u1, u1, u1, max u2 (succ u1)} ι (Preorder.smallCategory.{u1} ι _inst_3) (ModuleCat.{u1, u2} R _inst_1) (ModuleCat.moduleCategory.{u1, u2} R _inst_1) (ModuleCat.directLimitDiagram.{u1, u2} R _inst_1 ι _inst_3 G (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i) f _inst_6)
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : Ring.{u2} R] {ι : Type.{u1}} [_inst_3 : Preorder.{u1} ι] (G : ι -> Type.{u1}) [_inst_4 : forall (i : ι), AddCommGroup.{u1} (G i)] [_inst_5 : forall (i : ι), Module.{u2, u1} R (G i) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} (G i) (_inst_4 i))] (f : forall (i : ι) (j : ι), (LE.le.{u1} ι (Preorder.toLE.{u1} ι _inst_3) i j) -> (LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (G i) (G j) (AddCommGroup.toAddCommMonoid.{u1} (G i) (_inst_4 i)) (AddCommGroup.toAddCommMonoid.{u1} (G j) (_inst_4 j)) (_inst_5 i) (_inst_5 j))) [_inst_6 : DirectedSystem.{u1, u1} ι _inst_3 G (fun (i : ι) (j : ι) (h : LE.le.{u1} ι (Preorder.toLE.{u1} ι _inst_3) i j) => FunLike.coe.{succ u1, succ u1, succ u1} (LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (G i) (G j) (AddCommGroup.toAddCommMonoid.{u1} (G i) (_inst_4 i)) (AddCommGroup.toAddCommMonoid.{u1} (G j) (_inst_4 j)) (_inst_5 i) (_inst_5 j)) (G i) (fun (_x : G i) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : G i) => G j) _x) (LinearMap.instFunLikeLinearMap.{u2, u2, u1, u1} R R (G i) (G j) (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} (G i) (_inst_4 i)) (AddCommGroup.toAddCommMonoid.{u1} (G j) (_inst_4 j)) (_inst_5 i) (_inst_5 j) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) (f i j h))] [_inst_7 : DecidableEq.{succ u1} ι], CategoryTheory.Limits.Cocone.{u1, u1, u1, max u2 (succ u1)} ι (Preorder.smallCategory.{u1} ι _inst_3) (ModuleCat.{u1, u2} R _inst_1) (ModuleCat.moduleCategory.{u1, u2} R _inst_1) (ModuleCat.directLimitDiagram.{u1, u2} R _inst_1 ι _inst_3 G (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i) f _inst_6)
Case conversion may be inaccurate. Consider using '#align Module.direct_limit_cocone ModuleCat.directLimitCoconeₓ'. -/
/-- The `cocone` on `direct_limit_diagram` corresponding to
the unbundled `direct_limit` of modules.

In `direct_limit_is_colimit` we show that it is a colimit cocone. -/
@[simps]
def directLimitCocone : Cocone (directLimitDiagram G f)
    where
  pt := ModuleCat.of R <| DirectLimit G f
  ι :=
    { app := Module.DirectLimit.of R ι G f
      naturality' := fun i j hij => by
        apply LinearMap.ext
        intro x
        exact direct_limit.of_f }
#align Module.direct_limit_cocone ModuleCat.directLimitCocone

/- warning: Module.direct_limit_is_colimit -> ModuleCat.directLimitIsColimit is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u2}} [_inst_1 : Ring.{u2} R] {ι : Type.{u1}} [_inst_3 : Preorder.{u1} ι] (G : ι -> Type.{u1}) [_inst_4 : forall (i : ι), AddCommGroup.{u1} (G i)] [_inst_5 : forall (i : ι), Module.{u2, u1} R (G i) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} (G i) (_inst_4 i))] (f : forall (i : ι) (j : ι), (LE.le.{u1} ι (Preorder.toHasLe.{u1} ι _inst_3) i j) -> (LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (G i) (G j) (AddCommGroup.toAddCommMonoid.{u1} (G i) (_inst_4 i)) (AddCommGroup.toAddCommMonoid.{u1} (G j) (_inst_4 j)) (_inst_5 i) (_inst_5 j))) [_inst_6 : DirectedSystem.{u1, u1} ι _inst_3 G (fun (i : ι) (j : ι) (h : LE.le.{u1} ι (Preorder.toHasLe.{u1} ι _inst_3) i j) => coeFn.{succ u1, succ u1} (LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (G i) (G j) (AddCommGroup.toAddCommMonoid.{u1} (G i) (_inst_4 i)) (AddCommGroup.toAddCommMonoid.{u1} (G j) (_inst_4 j)) (_inst_5 i) (_inst_5 j)) (fun (_x : LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (G i) (G j) (AddCommGroup.toAddCommMonoid.{u1} (G i) (_inst_4 i)) (AddCommGroup.toAddCommMonoid.{u1} (G j) (_inst_4 j)) (_inst_5 i) (_inst_5 j)) => (G i) -> (G j)) (LinearMap.hasCoeToFun.{u2, u2, u1, u1} R R (G i) (G j) (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} (G i) (_inst_4 i)) (AddCommGroup.toAddCommMonoid.{u1} (G j) (_inst_4 j)) (_inst_5 i) (_inst_5 j) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) (f i j h))] [_inst_7 : DecidableEq.{succ u1} ι] [_inst_8 : Nonempty.{succ u1} ι] [_inst_9 : IsDirected.{u1} ι (LE.le.{u1} ι (Preorder.toHasLe.{u1} ι _inst_3))], CategoryTheory.Limits.IsColimit.{u1, u1, u1, max u2 (succ u1)} ι (Preorder.smallCategory.{u1} ι _inst_3) (ModuleCat.{u1, u2} R _inst_1) (ModuleCat.moduleCategory.{u1, u2} R _inst_1) (ModuleCat.directLimitDiagram.{u1, u2} R _inst_1 ι _inst_3 G (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i) f _inst_6) (ModuleCat.directLimitCocone.{u1, u2} R _inst_1 ι _inst_3 G (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i) f _inst_6 (fun (a : ι) (b : ι) => _inst_7 a b))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : Ring.{u2} R] {ι : Type.{u1}} [_inst_3 : Preorder.{u1} ι] (G : ι -> Type.{u1}) [_inst_4 : forall (i : ι), AddCommGroup.{u1} (G i)] [_inst_5 : forall (i : ι), Module.{u2, u1} R (G i) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} (G i) (_inst_4 i))] (f : forall (i : ι) (j : ι), (LE.le.{u1} ι (Preorder.toLE.{u1} ι _inst_3) i j) -> (LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (G i) (G j) (AddCommGroup.toAddCommMonoid.{u1} (G i) (_inst_4 i)) (AddCommGroup.toAddCommMonoid.{u1} (G j) (_inst_4 j)) (_inst_5 i) (_inst_5 j))) [_inst_6 : DirectedSystem.{u1, u1} ι _inst_3 G (fun (i : ι) (j : ι) (h : LE.le.{u1} ι (Preorder.toLE.{u1} ι _inst_3) i j) => FunLike.coe.{succ u1, succ u1, succ u1} (LinearMap.{u2, u2, u1, u1} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (G i) (G j) (AddCommGroup.toAddCommMonoid.{u1} (G i) (_inst_4 i)) (AddCommGroup.toAddCommMonoid.{u1} (G j) (_inst_4 j)) (_inst_5 i) (_inst_5 j)) (G i) (fun (_x : G i) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : G i) => G j) _x) (LinearMap.instFunLikeLinearMap.{u2, u2, u1, u1} R R (G i) (G j) (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} (G i) (_inst_4 i)) (AddCommGroup.toAddCommMonoid.{u1} (G j) (_inst_4 j)) (_inst_5 i) (_inst_5 j) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) (f i j h))] [_inst_7 : DecidableEq.{succ u1} ι] [_inst_8 : Nonempty.{succ u1} ι] [_inst_9 : IsDirected.{u1} ι (fun (x._@.Mathlib.Algebra.Category.ModuleCat.Limits._hyg.1595 : ι) (x._@.Mathlib.Algebra.Category.ModuleCat.Limits._hyg.1597 : ι) => LE.le.{u1} ι (Preorder.toLE.{u1} ι _inst_3) x._@.Mathlib.Algebra.Category.ModuleCat.Limits._hyg.1595 x._@.Mathlib.Algebra.Category.ModuleCat.Limits._hyg.1597)], CategoryTheory.Limits.IsColimit.{u1, u1, u1, max u2 (succ u1)} ι (Preorder.smallCategory.{u1} ι _inst_3) (ModuleCat.{u1, u2} R _inst_1) (ModuleCat.moduleCategory.{u1, u2} R _inst_1) (ModuleCat.directLimitDiagram.{u1, u2} R _inst_1 ι _inst_3 G (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i) f _inst_6) (ModuleCat.directLimitCocone.{u1, u2} R _inst_1 ι _inst_3 G (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i) f _inst_6 (fun (a : ι) (b : ι) => _inst_7 a b))
Case conversion may be inaccurate. Consider using '#align Module.direct_limit_is_colimit ModuleCat.directLimitIsColimitₓ'. -/
/-- The unbundled `direct_limit` of modules is a colimit
in the sense of `category_theory`. -/
@[simps]
def directLimitIsColimit [Nonempty ι] [IsDirected ι (· ≤ ·)] : IsColimit (directLimitCocone G f)
    where
  desc s :=
    DirectLimit.lift R ι G f s.ι.app fun i j h x =>
      by
      rw [← s.w (hom_of_le h)]
      rfl
  fac s i := by
    apply LinearMap.ext
    intro x
    dsimp
    exact direct_limit.lift_of s.ι.app _ x
  uniq s m h :=
    by
    have :
      s.ι.app = fun i =>
        LinearMap.comp m (direct_limit.of R ι (fun i => G i) (fun i j H => f i j H) i) :=
      by
      funext i
      rw [← h]
      rfl
    apply LinearMap.ext
    intro x
    simp only [this]
    apply Module.DirectLimit.lift_unique
#align Module.direct_limit_is_colimit ModuleCat.directLimitIsColimit

end DirectLimit

end ModuleCat

