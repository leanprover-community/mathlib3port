/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.category.Ring.limits
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Ring.Pi
import Mathbin.Algebra.Category.Ring.Basic
import Mathbin.Algebra.Category.Group.Limits
import Mathbin.RingTheory.Subring.Basic

/-!
# The category of (commutative) rings has all limits

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/


-- We use the following trick a lot of times in this file.
library_note "change elaboration strategy with `by apply`"/--
Some definitions may be extremely slow to elaborate, when the target type to be constructed
is complicated and when the type of the term given in the definition is also complicated and does
not obviously match the target type. In this case, instead of just giving the term, prefixing it
with `by apply` may speed up things considerably as the types are not elaborated in the same order.
-/


open CategoryTheory

open CategoryTheory.Limits

universe v u

noncomputable section

namespace SemiRingCat

variable {J : Type v} [SmallCategory J]

/- warning: SemiRing.semiring_obj -> SemiRingCat.semiringObj is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 SemiRingCat.{max u1 u2} SemiRingCat.largeCategory.{max u1 u2}) (j : J), Semiring.{max u1 u2} (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 Type.{max u1 u2} CategoryTheory.types.{max u1 u2} (CategoryTheory.Functor.comp.{u1, max u1 u2, max u1 u2, u1, succ (max u1 u2), succ (max u1 u2)} J _inst_1 SemiRingCat.{max u1 u2} SemiRingCat.largeCategory.{max u1 u2} Type.{max u1 u2} CategoryTheory.types.{max u1 u2} F (CategoryTheory.forget.{succ (max u1 u2), max u1 u2, max u1 u2} SemiRingCat.{max u1 u2} SemiRingCat.largeCategory.{max u1 u2} SemiRingCat.concreteCategory.{max u1 u2})) j)
but is expected to have type
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 SemiRingCatMax.{u1, u2} instSemiRingCatLargeCategory.{max u2 u1}) (j : J), Semiring.{max u2 u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) Type.{max u2 u1} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} Type.{max u2 u1} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} Type.{max u2 u1} CategoryTheory.types.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 Type.{max u2 u1} CategoryTheory.types.{max u2 u1} (CategoryTheory.Functor.comp.{u1, max u2 u1, max u2 u1, u1, max (succ u2) (succ u1), max (succ u2) (succ u1)} J _inst_1 SemiRingCatMax.{u1, u2} instSemiRingCatLargeCategory.{max u2 u1} Type.{max u2 u1} CategoryTheory.types.{max u2 u1} F (CategoryTheory.forget.{succ (max u2 u1), max u2 u1, max u2 u1} SemiRingCat.{max u2 u1} instSemiRingCatLargeCategory.{max u2 u1} SemiRingCat.instConcreteCategorySemiRingCatInstSemiRingCatLargeCategory.{max u2 u1}))) j)
Case conversion may be inaccurate. Consider using '#align SemiRing.semiring_obj SemiRingCat.semiringObjₓ'. -/
instance semiringObj (F : J ⥤ SemiRingCat.{max v u}) (j) :
    Semiring ((F ⋙ forget SemiRingCat).obj j) := by change Semiring (F.obj j); infer_instance
#align SemiRing.semiring_obj SemiRingCat.semiringObj

/- warning: SemiRing.sections_subsemiring -> SemiRingCat.sectionsSubsemiring is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 SemiRingCat.{max u1 u2} SemiRingCat.largeCategory.{max u1 u2}), Subsemiring.{max u1 u2} (forall (j : J), coeSort.{succ (succ (max u1 u2)), succ (succ (max u1 u2))} SemiRingCat.{max u1 u2} Type.{max u1 u2} SemiRingCat.hasCoeToSort.{max u1 u2} (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 SemiRingCat.{max u1 u2} SemiRingCat.largeCategory.{max u1 u2} F j)) (Pi.nonAssocSemiring.{u1, max u1 u2} J (fun (j : J) => coeSort.{succ (succ (max u1 u2)), succ (succ (max u1 u2))} SemiRingCat.{max u1 u2} Type.{max u1 u2} SemiRingCat.hasCoeToSort.{max u1 u2} (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 SemiRingCat.{max u1 u2} SemiRingCat.largeCategory.{max u1 u2} F j)) (fun (i : J) => Semiring.toNonAssocSemiring.{max u1 u2} (coeSort.{succ (succ (max u1 u2)), succ (succ (max u1 u2))} SemiRingCat.{max u1 u2} Type.{max u1 u2} SemiRingCat.hasCoeToSort.{max u1 u2} (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 SemiRingCat.{max u1 u2} SemiRingCat.largeCategory.{max u1 u2} F i)) (SemiRingCat.semiring.{max u1 u2} (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 SemiRingCat.{max u1 u2} SemiRingCat.largeCategory.{max u1 u2} F i))))
but is expected to have type
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 SemiRingCatMax.{u1, u2} instSemiRingCatLargeCategory.{max u2 u1}), Subsemiring.{max u1 u2} (forall (j : J), CategoryTheory.Bundled.α.{max u2 u1, max u2 u1} Semiring.{max u2 u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) SemiRingCatMax.{u1, u2} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} SemiRingCatMax.{u1, u2} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} SemiRingCatMax.{u1, u2} instSemiRingCatLargeCategory.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 SemiRingCatMax.{u1, u2} instSemiRingCatLargeCategory.{max u2 u1} F) j)) (Pi.nonAssocSemiring.{u1, max u2 u1} J (fun (j : J) => CategoryTheory.Bundled.α.{max u2 u1, max u2 u1} Semiring.{max u2 u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) SemiRingCatMax.{u1, u2} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} SemiRingCatMax.{u1, u2} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} SemiRingCatMax.{u1, u2} instSemiRingCatLargeCategory.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 SemiRingCatMax.{u1, u2} instSemiRingCatLargeCategory.{max u2 u1} F) j)) (fun (i : J) => Semiring.toNonAssocSemiring.{max u2 u1} (CategoryTheory.Bundled.α.{max u2 u1, max u2 u1} Semiring.{max u2 u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) SemiRingCatMax.{u1, u2} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} SemiRingCatMax.{u1, u2} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} SemiRingCatMax.{u1, u2} instSemiRingCatLargeCategory.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 SemiRingCatMax.{u1, u2} instSemiRingCatLargeCategory.{max u2 u1} F) i)) (SemiRingCat.instSemiringα.{max u2 u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) SemiRingCatMax.{u1, u2} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} SemiRingCatMax.{u1, u2} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} SemiRingCatMax.{u1, u2} instSemiRingCatLargeCategory.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 SemiRingCatMax.{u1, u2} instSemiRingCatLargeCategory.{max u2 u1} F) i))))
Case conversion may be inaccurate. Consider using '#align SemiRing.sections_subsemiring SemiRingCat.sectionsSubsemiringₓ'. -/
/-- The flat sections of a functor into `SemiRing` form a subsemiring of all sections.
-/
def sectionsSubsemiring (F : J ⥤ SemiRingCat.{max v u}) : Subsemiring (∀ j, F.obj j) :=
  {
    AddMonCat.sectionsAddSubmonoid
      (F ⋙ forget₂ SemiRingCat AddCommMonCat.{max v u} ⋙ forget₂ AddCommMonCat AddMonCat.{max v u}),
    MonCat.sectionsSubmonoid (F ⋙ forget₂ SemiRingCat MonCat.{max v u}) with
    carrier := (F ⋙ forget SemiRingCat).sections }
#align SemiRing.sections_subsemiring SemiRingCat.sectionsSubsemiring

#print SemiRingCat.limitSemiring /-
instance limitSemiring (F : J ⥤ SemiRingCat.{max v u}) :
    Semiring (Types.limitCone (F ⋙ forget SemiRingCat.{max v u})).pt :=
  (sectionsSubsemiring F).toSemiring
#align SemiRing.limit_semiring SemiRingCat.limitSemiring
-/

/- warning: SemiRing.limit_π_ring_hom -> SemiRingCat.limitπRingHom is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 SemiRingCat.{max u1 u2} SemiRingCat.largeCategory.{max u1 u2}) (j : J), RingHom.{max u1 u2, max u1 u2} (CategoryTheory.Limits.Cone.pt.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 Type.{max u1 u2} CategoryTheory.types.{max u1 u2} (CategoryTheory.Functor.comp.{u1, max u1 u2, max u1 u2, u1, succ (max u1 u2), succ (max u1 u2)} J _inst_1 SemiRingCat.{max u1 u2} SemiRingCat.largeCategory.{max u1 u2} Type.{max u1 u2} CategoryTheory.types.{max u1 u2} F (CategoryTheory.forget.{succ (max u1 u2), max u1 u2, max u1 u2} SemiRingCat.{max u1 u2} SemiRingCat.largeCategory.{max u1 u2} SemiRingCat.concreteCategory.{max u1 u2})) (CategoryTheory.Limits.Types.limitCone.{u1, u2} J _inst_1 (CategoryTheory.Functor.comp.{u1, max u1 u2, max u1 u2, u1, succ (max u1 u2), succ (max u1 u2)} J _inst_1 SemiRingCat.{max u1 u2} SemiRingCat.largeCategory.{max u1 u2} Type.{max u1 u2} CategoryTheory.types.{max u1 u2} F (CategoryTheory.forget.{succ (max u1 u2), max u1 u2, max u1 u2} SemiRingCat.{max u1 u2} SemiRingCat.largeCategory.{max u1 u2} SemiRingCat.concreteCategory.{max u1 u2})))) (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 Type.{max u1 u2} CategoryTheory.types.{max u1 u2} (CategoryTheory.Functor.comp.{u1, max u1 u2, max u1 u2, u1, succ (max u1 u2), succ (max u1 u2)} J _inst_1 SemiRingCat.{max u1 u2} SemiRingCat.largeCategory.{max u1 u2} Type.{max u1 u2} CategoryTheory.types.{max u1 u2} F (CategoryTheory.forget.{succ (max u1 u2), max u1 u2, max u1 u2} SemiRingCat.{max u1 u2} SemiRingCat.largeCategory.{max u1 u2} SemiRingCat.concreteCategory.{max u1 u2})) j) (Semiring.toNonAssocSemiring.{max u1 u2} (CategoryTheory.Limits.Cone.pt.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 Type.{max u1 u2} CategoryTheory.types.{max u1 u2} (CategoryTheory.Functor.comp.{u1, max u1 u2, max u1 u2, u1, succ (max u1 u2), succ (max u1 u2)} J _inst_1 SemiRingCat.{max u1 u2} SemiRingCat.largeCategory.{max u1 u2} Type.{max u1 u2} CategoryTheory.types.{max u1 u2} F (CategoryTheory.forget.{succ (max u1 u2), max u1 u2, max u1 u2} SemiRingCat.{max u1 u2} SemiRingCat.largeCategory.{max u1 u2} SemiRingCat.concreteCategory.{max u1 u2})) (CategoryTheory.Limits.Types.limitCone.{u1, u2} J _inst_1 (CategoryTheory.Functor.comp.{u1, max u1 u2, max u1 u2, u1, succ (max u1 u2), succ (max u1 u2)} J _inst_1 SemiRingCat.{max u1 u2} SemiRingCat.largeCategory.{max u1 u2} Type.{max u1 u2} CategoryTheory.types.{max u1 u2} F (CategoryTheory.forget.{succ (max u1 u2), max u1 u2, max u1 u2} SemiRingCat.{max u1 u2} SemiRingCat.largeCategory.{max u1 u2} SemiRingCat.concreteCategory.{max u1 u2})))) (SemiRingCat.limitSemiring.{u1, u2} J _inst_1 F)) (Semiring.toNonAssocSemiring.{max u1 u2} (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 Type.{max u1 u2} CategoryTheory.types.{max u1 u2} (CategoryTheory.Functor.comp.{u1, max u1 u2, max u1 u2, u1, succ (max u1 u2), succ (max u1 u2)} J _inst_1 SemiRingCat.{max u1 u2} SemiRingCat.largeCategory.{max u1 u2} Type.{max u1 u2} CategoryTheory.types.{max u1 u2} F (CategoryTheory.forget.{succ (max u1 u2), max u1 u2, max u1 u2} SemiRingCat.{max u1 u2} SemiRingCat.largeCategory.{max u1 u2} SemiRingCat.concreteCategory.{max u1 u2})) j) (SemiRingCat.semiringObj.{u1, u2} J _inst_1 F j))
but is expected to have type
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 SemiRingCatMax.{u1, u2} instSemiRingCatLargeCategory.{max u2 u1}) (j : J), RingHom.{max u2 u1, max u2 u1} (CategoryTheory.Limits.Cone.pt.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 TypeMax.{u1, u2} CategoryTheory.types.{max u2 u1} (CategoryTheory.Functor.comp.{u1, max u2 u1, max u2 u1, u1, max (succ u2) (succ u1), max (succ u2) (succ u1)} J _inst_1 SemiRingCatMax.{u1, u2} instSemiRingCatLargeCategory.{max u2 u1} TypeMax.{u1, u2} CategoryTheory.types.{max u2 u1} F (CategoryTheory.forget.{succ (max u2 u1), max u2 u1, max u2 u1} SemiRingCat.{max u2 u1} instSemiRingCatLargeCategory.{max u2 u1} SemiRingCat.instConcreteCategorySemiRingCatInstSemiRingCatLargeCategory.{max u2 u1})) (CategoryTheory.Limits.Types.limitCone.{u1, u2} J _inst_1 (CategoryTheory.Functor.comp.{u1, max u2 u1, max u2 u1, u1, max (succ u2) (succ u1), max (succ u2) (succ u1)} J _inst_1 SemiRingCatMax.{u1, u2} instSemiRingCatLargeCategory.{max u2 u1} TypeMax.{u1, u2} CategoryTheory.types.{max u2 u1} F (CategoryTheory.forget.{succ (max u2 u1), max u2 u1, max u2 u1} SemiRingCat.{max u2 u1} instSemiRingCatLargeCategory.{max u2 u1} SemiRingCat.instConcreteCategorySemiRingCatInstSemiRingCatLargeCategory.{max u2 u1})))) (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) Type.{max u2 u1} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} Type.{max u2 u1} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} Type.{max u2 u1} CategoryTheory.types.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 Type.{max u2 u1} CategoryTheory.types.{max u2 u1} (CategoryTheory.Functor.comp.{u1, max u2 u1, max u2 u1, u1, max (succ u2) (succ u1), max (succ u2) (succ u1)} J _inst_1 SemiRingCatMax.{u1, u2} instSemiRingCatLargeCategory.{max u2 u1} Type.{max u2 u1} CategoryTheory.types.{max u2 u1} F (CategoryTheory.forget.{succ (max u2 u1), max u2 u1, max u2 u1} SemiRingCat.{max u2 u1} instSemiRingCatLargeCategory.{max u2 u1} SemiRingCat.instConcreteCategorySemiRingCatInstSemiRingCatLargeCategory.{max u2 u1}))) j) (Semiring.toNonAssocSemiring.{max u2 u1} (CategoryTheory.Limits.Cone.pt.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 TypeMax.{u1, u2} CategoryTheory.types.{max u2 u1} (CategoryTheory.Functor.comp.{u1, max u2 u1, max u2 u1, u1, max (succ u2) (succ u1), max (succ u2) (succ u1)} J _inst_1 SemiRingCatMax.{u1, u2} instSemiRingCatLargeCategory.{max u2 u1} TypeMax.{u1, u2} CategoryTheory.types.{max u2 u1} F (CategoryTheory.forget.{succ (max u2 u1), max u2 u1, max u2 u1} SemiRingCat.{max u2 u1} instSemiRingCatLargeCategory.{max u2 u1} SemiRingCat.instConcreteCategorySemiRingCatInstSemiRingCatLargeCategory.{max u2 u1})) (CategoryTheory.Limits.Types.limitCone.{u1, u2} J _inst_1 (CategoryTheory.Functor.comp.{u1, max u2 u1, max u2 u1, u1, max (succ u2) (succ u1), max (succ u2) (succ u1)} J _inst_1 SemiRingCatMax.{u1, u2} instSemiRingCatLargeCategory.{max u2 u1} TypeMax.{u1, u2} CategoryTheory.types.{max u2 u1} F (CategoryTheory.forget.{succ (max u2 u1), max u2 u1, max u2 u1} SemiRingCat.{max u2 u1} instSemiRingCatLargeCategory.{max u2 u1} SemiRingCat.instConcreteCategorySemiRingCatInstSemiRingCatLargeCategory.{max u2 u1})))) (SemiRingCat.limitSemiring.{u1, u2} J _inst_1 F)) (Semiring.toNonAssocSemiring.{max u2 u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) Type.{max u2 u1} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} Type.{max u2 u1} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} Type.{max u2 u1} CategoryTheory.types.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 Type.{max u2 u1} CategoryTheory.types.{max u2 u1} (CategoryTheory.Functor.comp.{u1, max u2 u1, max u2 u1, u1, max (succ u2) (succ u1), max (succ u2) (succ u1)} J _inst_1 SemiRingCatMax.{u1, u2} instSemiRingCatLargeCategory.{max u2 u1} Type.{max u2 u1} CategoryTheory.types.{max u2 u1} F (CategoryTheory.forget.{succ (max u2 u1), max u2 u1, max u2 u1} SemiRingCat.{max u2 u1} instSemiRingCatLargeCategory.{max u2 u1} SemiRingCat.instConcreteCategorySemiRingCatInstSemiRingCatLargeCategory.{max u2 u1}))) j) (SemiRingCat.semiringObj.{u1, u2} J _inst_1 F j))
Case conversion may be inaccurate. Consider using '#align SemiRing.limit_π_ring_hom SemiRingCat.limitπRingHomₓ'. -/
/-- `limit.π (F ⋙ forget SemiRing) j` as a `ring_hom`. -/
def limitπRingHom (F : J ⥤ SemiRingCat.{max v u}) (j) :
    (Types.limitCone (F ⋙ forget SemiRingCat)).pt →+* (F ⋙ forget SemiRingCat).obj j :=
  {
    AddMonCat.limitπAddMonoidHom
      (F ⋙ forget₂ SemiRingCat AddCommMonCat.{max v u} ⋙ forget₂ AddCommMonCat AddMonCat.{max v u})
      j,
    MonCat.limitπMonoidHom (F ⋙ forget₂ SemiRingCat MonCat.{max v u}) j with
    toFun := (Types.limitCone (F ⋙ forget SemiRingCat)).π.app j }
#align SemiRing.limit_π_ring_hom SemiRingCat.limitπRingHom

namespace HasLimits

#print SemiRingCat.HasLimits.limitCone /-
-- The next two definitions are used in the construction of `has_limits SemiRing`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.is_limit F`.
/-- Construction of a limit cone in `SemiRing`.
(Internal use only; use the limits API.)
-/
def limitCone (F : J ⥤ SemiRingCat.{max v u}) : Cone F
    where
  pt := SemiRingCat.of (Types.limitCone (F ⋙ forget _)).pt
  π :=
    { app := limitπRingHom F
      naturality' := fun j j' f =>
        RingHom.coe_inj ((Types.limitCone (F ⋙ forget _)).π.naturality f) }
#align SemiRing.has_limits.limit_cone SemiRingCat.HasLimits.limitCone
-/

#print SemiRingCat.HasLimits.limitConeIsLimit /-
/-- Witness that the limit cone in `SemiRing` is a limit cone.
(Internal use only; use the limits API.)
-/
def limitConeIsLimit (F : J ⥤ SemiRingCat.{max v u}) : IsLimit (limitCone F) := by
  refine'
      is_limit.of_faithful (forget SemiRingCat) (types.limit_cone_is_limit _)
        (fun s => ⟨_, _, _, _, _⟩) fun s => rfl <;>
    tidy
#align SemiRing.has_limits.limit_cone_is_limit SemiRingCat.HasLimits.limitConeIsLimit
-/

end HasLimits

open HasLimits

/- ./././Mathport/Syntax/Translate/Command.lean:322:38: unsupported irreducible non-definition -/
#print SemiRingCat.hasLimitsOfSize /-
/-- The category of rings has all limits. -/
irreducible_def hasLimitsOfSize : HasLimitsOfSize.{v} SemiRingCat.{max v u} :=
  {
    HasLimitsOfShape := fun J 𝒥 =>
      {
        HasLimit := fun F =>
          has_limit.mk
            { Cone := limit_cone F
              IsLimit := limit_cone_is_limit F } } }
#align SemiRing.has_limits_of_size SemiRingCat.hasLimitsOfSize
-/

#print SemiRingCat.hasLimits /-
instance hasLimits : HasLimits SemiRingCat.{u} :=
  SemiRingCat.hasLimitsOfSize.{u, u}
#align SemiRing.has_limits SemiRingCat.hasLimits
-/

/- warning: SemiRing.forget₂_AddCommMon_preserves_limits_aux -> SemiRingCat.forget₂AddCommMonPreservesLimitsAux is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 SemiRingCat.{max u1 u2} SemiRingCat.largeCategory.{max u1 u2}), CategoryTheory.Limits.IsLimit.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 AddCommMonCat.{max u1 u2} AddCommMonCat.largeCategory.{max u1 u2} (CategoryTheory.Functor.comp.{u1, max u1 u2, max u1 u2, u1, succ (max u1 u2), succ (max u1 u2)} J _inst_1 SemiRingCat.{max u1 u2} SemiRingCat.largeCategory.{max u1 u2} AddCommMonCat.{max u1 u2} AddCommMonCat.largeCategory.{max u1 u2} F (CategoryTheory.forget₂.{succ (max u1 u2), succ (max u1 u2), max u1 u2, max u1 u2, max u1 u2} SemiRingCat.{max u1 u2} AddCommMonCat.{max u1 u2} SemiRingCat.largeCategory.{max u1 u2} SemiRingCat.concreteCategory.{max u1 u2} AddCommMonCat.largeCategory.{max u1 u2} AddCommMonCat.concreteCategory.{max u1 u2} SemiRingCat.hasForgetToAddCommMonCat.{max u1 u2})) (CategoryTheory.Functor.mapCone.{u1, max u1 u2, max u1 u2, u1, succ (max u1 u2), succ (max u1 u2)} J _inst_1 SemiRingCat.{max u1 u2} SemiRingCat.largeCategory.{max u1 u2} AddCommMonCat.{max u1 u2} AddCommMonCat.largeCategory.{max u1 u2} F (CategoryTheory.forget₂.{succ (max u1 u2), succ (max u1 u2), max u1 u2, max u1 u2, max u1 u2} SemiRingCat.{max u1 u2} AddCommMonCat.{max u1 u2} SemiRingCat.largeCategory.{max u1 u2} SemiRingCat.concreteCategory.{max u1 u2} AddCommMonCat.largeCategory.{max u1 u2} AddCommMonCat.concreteCategory.{max u1 u2} SemiRingCat.hasForgetToAddCommMonCat.{max u1 u2}) (SemiRingCat.HasLimits.limitCone.{u1, u2} J _inst_1 F))
but is expected to have type
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 SemiRingCatMax.{u1, u2} instSemiRingCatLargeCategory.{max u2 u1}), CategoryTheory.Limits.IsLimit.{u1, max u2 u1, u1, succ (max u2 u1)} J _inst_1 AddCommMonCat.{max u2 u1} instAddCommMonCatLargeCategory.{max u2 u1} (CategoryTheory.Functor.comp.{u1, max u2 u1, max u2 u1, u1, succ (max u2 u1), succ (max u2 u1)} J _inst_1 SemiRingCat.{max u2 u1} instSemiRingCatLargeCategory.{max u2 u1} AddCommMonCat.{max u2 u1} instAddCommMonCatLargeCategory.{max u2 u1} F (CategoryTheory.forget₂.{succ (max u2 u1), succ (max u2 u1), max u2 u1, max u2 u1, max u2 u1} SemiRingCat.{max u2 u1} AddCommMonCat.{max u2 u1} instSemiRingCatLargeCategory.{max u2 u1} SemiRingCat.instConcreteCategorySemiRingCatInstSemiRingCatLargeCategory.{max u2 u1} instAddCommMonCatLargeCategory.{max u2 u1} AddCommMonCat.concreteCategory.{max u2 u1} SemiRingCat.hasForgetToAddCommMonCat.{max u2 u1})) (CategoryTheory.Functor.mapCone.{u1, max u2 u1, max u2 u1, u1, succ (max u2 u1), succ (max u2 u1)} J _inst_1 SemiRingCat.{max u2 u1} instSemiRingCatLargeCategory.{max u2 u1} AddCommMonCat.{max u2 u1} instAddCommMonCatLargeCategory.{max u2 u1} (CategoryTheory.forget₂.{succ (max u2 u1), succ (max u2 u1), max u2 u1, max u2 u1, max u2 u1} SemiRingCat.{max u2 u1} AddCommMonCat.{max u2 u1} instSemiRingCatLargeCategory.{max u2 u1} SemiRingCat.instConcreteCategorySemiRingCatInstSemiRingCatLargeCategory.{max u2 u1} instAddCommMonCatLargeCategory.{max u2 u1} AddCommMonCat.concreteCategory.{max u2 u1} SemiRingCat.hasForgetToAddCommMonCat.{max u2 u1}) F (SemiRingCat.HasLimits.limitCone.{u1, u2} J _inst_1 F))
Case conversion may be inaccurate. Consider using '#align SemiRing.forget₂_AddCommMon_preserves_limits_aux SemiRingCat.forget₂AddCommMonPreservesLimitsAuxₓ'. -/
/-- An auxiliary declaration to speed up typechecking.
-/
def forget₂AddCommMonPreservesLimitsAux (F : J ⥤ SemiRingCat.{max v u}) :
    IsLimit ((forget₂ SemiRingCat AddCommMonCat).mapCone (limitCone F)) := by
  apply AddCommMonCat.limitConeIsLimit (F ⋙ forget₂ SemiRingCat AddCommMonCat.{max v u})
#align SemiRing.forget₂_AddCommMon_preserves_limits_aux SemiRingCat.forget₂AddCommMonPreservesLimitsAux

#print SemiRingCat.forget₂AddCommMonPreservesLimitsOfSize /-
/-- The forgetful functor from semirings to additive commutative monoids preserves all limits.
-/
instance forget₂AddCommMonPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ SemiRingCat AddCommMonCat.{max v u})
    where PreservesLimitsOfShape J 𝒥 :=
    {
      PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
          (forget₂_AddCommMon_preserves_limits_aux F) }
#align SemiRing.forget₂_AddCommMon_preserves_limits_of_size SemiRingCat.forget₂AddCommMonPreservesLimitsOfSize
-/

#print SemiRingCat.forget₂AddCommMonPreservesLimits /-
instance forget₂AddCommMonPreservesLimits :
    PreservesLimits (forget₂ SemiRingCat AddCommMonCat.{u}) :=
  SemiRingCat.forget₂AddCommMonPreservesLimitsOfSize.{u, u}
#align SemiRing.forget₂_AddCommMon_preserves_limits SemiRingCat.forget₂AddCommMonPreservesLimits
-/

/- warning: SemiRing.forget₂_Mon_preserves_limits_aux -> SemiRingCat.forget₂MonPreservesLimitsAux is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 SemiRingCat.{max u1 u2} SemiRingCat.largeCategory.{max u1 u2}), CategoryTheory.Limits.IsLimit.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2} (CategoryTheory.Functor.comp.{u1, max u1 u2, max u1 u2, u1, succ (max u1 u2), succ (max u1 u2)} J _inst_1 SemiRingCat.{max u1 u2} SemiRingCat.largeCategory.{max u1 u2} MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2} F (CategoryTheory.forget₂.{succ (max u1 u2), succ (max u1 u2), max u1 u2, max u1 u2, max u1 u2} SemiRingCat.{max u1 u2} MonCat.{max u1 u2} SemiRingCat.largeCategory.{max u1 u2} SemiRingCat.concreteCategory.{max u1 u2} MonCat.largeCategory.{max u1 u2} MonCat.concreteCategory.{max u1 u2} SemiRingCat.hasForgetToMonCat.{max u1 u2})) (CategoryTheory.Functor.mapCone.{u1, max u1 u2, max u1 u2, u1, succ (max u1 u2), succ (max u1 u2)} J _inst_1 SemiRingCat.{max u1 u2} SemiRingCat.largeCategory.{max u1 u2} MonCat.{max u1 u2} MonCat.largeCategory.{max u1 u2} F (CategoryTheory.forget₂.{succ (max u1 u2), succ (max u1 u2), max u1 u2, max u1 u2, max u1 u2} SemiRingCat.{max u1 u2} MonCat.{max u1 u2} SemiRingCat.largeCategory.{max u1 u2} SemiRingCat.concreteCategory.{max u1 u2} MonCat.largeCategory.{max u1 u2} MonCat.concreteCategory.{max u1 u2} SemiRingCat.hasForgetToMonCat.{max u1 u2}) (SemiRingCat.HasLimits.limitCone.{u1, u2} J _inst_1 F))
but is expected to have type
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 SemiRingCatMax.{u1, u2} instSemiRingCatLargeCategory.{max u2 u1}), CategoryTheory.Limits.IsLimit.{u1, max u2 u1, u1, succ (max u2 u1)} J _inst_1 MonCat.{max u2 u1} instMonCatLargeCategory.{max u2 u1} (CategoryTheory.Functor.comp.{u1, max u2 u1, max u2 u1, u1, succ (max u2 u1), succ (max u2 u1)} J _inst_1 SemiRingCat.{max u2 u1} instSemiRingCatLargeCategory.{max u2 u1} MonCat.{max u2 u1} instMonCatLargeCategory.{max u2 u1} F (CategoryTheory.forget₂.{succ (max u2 u1), succ (max u2 u1), max u2 u1, max u2 u1, max u2 u1} SemiRingCat.{max u2 u1} MonCat.{max u2 u1} instSemiRingCatLargeCategory.{max u2 u1} SemiRingCat.instConcreteCategorySemiRingCatInstSemiRingCatLargeCategory.{max u2 u1} instMonCatLargeCategory.{max u2 u1} MonCat.concreteCategory.{max u2 u1} SemiRingCat.hasForgetToMonCat.{max u2 u1})) (CategoryTheory.Functor.mapCone.{u1, max u2 u1, max u2 u1, u1, succ (max u2 u1), succ (max u2 u1)} J _inst_1 SemiRingCat.{max u2 u1} instSemiRingCatLargeCategory.{max u2 u1} MonCat.{max u2 u1} instMonCatLargeCategory.{max u2 u1} (CategoryTheory.forget₂.{succ (max u2 u1), succ (max u2 u1), max u2 u1, max u2 u1, max u2 u1} SemiRingCat.{max u2 u1} MonCat.{max u2 u1} instSemiRingCatLargeCategory.{max u2 u1} SemiRingCat.instConcreteCategorySemiRingCatInstSemiRingCatLargeCategory.{max u2 u1} instMonCatLargeCategory.{max u2 u1} MonCat.concreteCategory.{max u2 u1} SemiRingCat.hasForgetToMonCat.{max u2 u1}) F (SemiRingCat.HasLimits.limitCone.{u1, u2} J _inst_1 F))
Case conversion may be inaccurate. Consider using '#align SemiRing.forget₂_Mon_preserves_limits_aux SemiRingCat.forget₂MonPreservesLimitsAuxₓ'. -/
/-- An auxiliary declaration to speed up typechecking.
-/
def forget₂MonPreservesLimitsAux (F : J ⥤ SemiRingCat.{max v u}) :
    IsLimit ((forget₂ SemiRingCat MonCat).mapCone (limitCone F)) := by
  apply MonCat.HasLimits.limitConeIsLimit (F ⋙ forget₂ SemiRingCat MonCat.{max v u})
#align SemiRing.forget₂_Mon_preserves_limits_aux SemiRingCat.forget₂MonPreservesLimitsAux

#print SemiRingCat.forget₂MonPreservesLimitsOfSize /-
/-- The forgetful functor from semirings to monoids preserves all limits.
-/
instance forget₂MonPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ SemiRingCat MonCat.{max v u})
    where PreservesLimitsOfShape J 𝒥 :=
    {
      PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
          (forget₂_Mon_preserves_limits_aux F) }
#align SemiRing.forget₂_Mon_preserves_limits_of_size SemiRingCat.forget₂MonPreservesLimitsOfSize
-/

#print SemiRingCat.forget₂MonPreservesLimits /-
instance forget₂MonPreservesLimits : PreservesLimits (forget₂ SemiRingCat MonCat.{u}) :=
  SemiRingCat.forget₂MonPreservesLimitsOfSize.{u, u}
#align SemiRing.forget₂_Mon_preserves_limits SemiRingCat.forget₂MonPreservesLimits
-/

#print SemiRingCat.forgetPreservesLimitsOfSize /-
/-- The forgetful functor from semirings to types preserves all limits.
-/
instance forgetPreservesLimitsOfSize : PreservesLimitsOfSize.{v, v} (forget SemiRingCat.{max v u})
    where PreservesLimitsOfShape J 𝒥 :=
    {
      PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
          (types.limit_cone_is_limit (F ⋙ forget _)) }
#align SemiRing.forget_preserves_limits_of_size SemiRingCat.forgetPreservesLimitsOfSize
-/

#print SemiRingCat.forgetPreservesLimits /-
instance forgetPreservesLimits : PreservesLimits (forget SemiRingCat.{u}) :=
  SemiRingCat.forgetPreservesLimitsOfSize.{u, u}
#align SemiRing.forget_preserves_limits SemiRingCat.forgetPreservesLimits
-/

end SemiRingCat

namespace CommSemiRingCat

variable {J : Type v} [SmallCategory J]

/- warning: CommSemiRing.comm_semiring_obj -> CommSemiRingCat.commSemiringObj is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 CommSemiRingCat.{max u1 u2} CommSemiRingCat.largeCategory.{max u1 u2}) (j : J), CommSemiring.{max u1 u2} (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 Type.{max u1 u2} CategoryTheory.types.{max u1 u2} (CategoryTheory.Functor.comp.{u1, max u1 u2, max u1 u2, u1, succ (max u1 u2), succ (max u1 u2)} J _inst_1 CommSemiRingCat.{max u1 u2} CommSemiRingCat.largeCategory.{max u1 u2} Type.{max u1 u2} CategoryTheory.types.{max u1 u2} F (CategoryTheory.forget.{succ (max u1 u2), max u1 u2, max u1 u2} CommSemiRingCat.{max u1 u2} CommSemiRingCat.largeCategory.{max u1 u2} CommSemiRingCat.concreteCategory.{max u1 u2})) j)
but is expected to have type
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 CommSemiRingCatMax.{u1, u2} instCommSemiRingCatLargeCategory.{max u2 u1}) (j : J), CommSemiring.{max u2 u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) Type.{max u2 u1} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} Type.{max u2 u1} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} Type.{max u2 u1} CategoryTheory.types.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 Type.{max u2 u1} CategoryTheory.types.{max u2 u1} (CategoryTheory.Functor.comp.{u1, max u2 u1, max u2 u1, u1, max (succ u2) (succ u1), max (succ u2) (succ u1)} J _inst_1 CommSemiRingCatMax.{u1, u2} instCommSemiRingCatLargeCategory.{max u2 u1} Type.{max u2 u1} CategoryTheory.types.{max u2 u1} F (CategoryTheory.forget.{succ (max u2 u1), max u2 u1, max u2 u1} CommSemiRingCat.{max u2 u1} instCommSemiRingCatLargeCategory.{max u2 u1} CommSemiRing.instConcreteCategoryCommSemiRingCatInstCommSemiRingCatLargeCategory.{max u2 u1}))) j)
Case conversion may be inaccurate. Consider using '#align CommSemiRing.comm_semiring_obj CommSemiRingCat.commSemiringObjₓ'. -/
instance commSemiringObj (F : J ⥤ CommSemiRingCat.{max v u}) (j) :
    CommSemiring ((F ⋙ forget CommSemiRingCat).obj j) := by change CommSemiring (F.obj j);
  infer_instance
#align CommSemiRing.comm_semiring_obj CommSemiRingCat.commSemiringObj

#print CommSemiRingCat.limitCommSemiring /-
instance limitCommSemiring (F : J ⥤ CommSemiRingCat.{max v u}) :
    CommSemiring (Types.limitCone (F ⋙ forget CommSemiRingCat.{max v u})).pt :=
  @Subsemiring.toCommSemiring (∀ j, F.obj j) _
    (SemiRingCat.sectionsSubsemiring (F ⋙ forget₂ CommSemiRingCat SemiRingCat.{max v u}))
#align CommSemiRing.limit_comm_semiring CommSemiRingCat.limitCommSemiring
-/

/-- We show that the forgetful functor `CommSemiRing ⥤ SemiRing` creates limits.

All we need to do is notice that the limit point has a `comm_semiring` instance available,
and then reuse the existing limit.
-/
instance (F : J ⥤ CommSemiRingCat.{max v u}) :
    CreatesLimit F (forget₂ CommSemiRingCat SemiRingCat.{max v u}) :=
  createsLimitOfReflectsIso fun c' t =>
    { liftedCone :=
        { pt := CommSemiRing.of (Types.limitCone (F ⋙ forget _)).pt
          π :=
            { app := by
                apply SemiRingCat.limitπRingHom (F ⋙ forget₂ CommSemiRingCat SemiRingCat.{max v u})
              naturality' :=
                (SemiRingCat.HasLimits.limitCone
                      (F ⋙ forget₂ CommSemiRingCat SemiRingCat.{max v u})).π.naturality } }
      validLift := by apply is_limit.unique_up_to_iso (SemiRingCat.HasLimits.limitConeIsLimit _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ CommSemiRingCat SemiRingCat.{max v u})
          (by apply SemiRingCat.HasLimits.limitConeIsLimit _)
          (fun s =>
            (SemiRingCat.HasLimits.limitConeIsLimit _).lift ((forget₂ _ SemiRingCat).mapCone s))
          fun s => rfl }

#print CommSemiRingCat.limitCone /-
/-- A choice of limit cone for a functor into `CommSemiRing`.
(Generally, you'll just want to use `limit F`.)
-/
def limitCone (F : J ⥤ CommSemiRingCat.{max v u}) : Cone F :=
  liftLimit (limit.isLimit (F ⋙ forget₂ CommSemiRingCat SemiRingCat.{max v u}))
#align CommSemiRing.limit_cone CommSemiRingCat.limitCone
-/

#print CommSemiRingCat.limitConeIsLimit /-
/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
def limitConeIsLimit (F : J ⥤ CommSemiRingCat.{max v u}) : IsLimit (limitCone F) :=
  liftedLimitIsLimit _
#align CommSemiRing.limit_cone_is_limit CommSemiRingCat.limitConeIsLimit
-/

/- ./././Mathport/Syntax/Translate/Command.lean:322:38: unsupported irreducible non-definition -/
#print CommSemiRingCat.hasLimitsOfSize /-
/-- The category of rings has all limits. -/
irreducible_def hasLimitsOfSize : HasLimitsOfSize.{v, v} CommSemiRingCat.{max v u} :=
  {
    HasLimitsOfShape := fun J 𝒥 =>
      {
        HasLimit := fun F =>
          has_limit_of_created F (forget₂ CommSemiRingCat SemiRingCat.{max v u}) } }
#align CommSemiRing.has_limits_of_size CommSemiRingCat.hasLimitsOfSize
-/

#print CommSemiRingCat.hasLimits /-
instance hasLimits : HasLimits CommSemiRingCat.{u} :=
  CommSemiRingCat.hasLimitsOfSize.{u, u}
#align CommSemiRing.has_limits CommSemiRingCat.hasLimits
-/

#print CommSemiRingCat.forget₂SemiRingPreservesLimitsOfSize /-
/-- The forgetful functor from rings to semirings preserves all limits.
-/
instance forget₂SemiRingPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ CommSemiRingCat SemiRingCat.{max v u})
    where PreservesLimitsOfShape J 𝒥 := { PreservesLimit := fun F => by infer_instance }
#align CommSemiRing.forget₂_SemiRing_preserves_limits_of_size CommSemiRingCat.forget₂SemiRingPreservesLimitsOfSize
-/

#print CommSemiRingCat.forget₂SemiRingPreservesLimits /-
instance forget₂SemiRingPreservesLimits :
    PreservesLimits (forget₂ CommSemiRingCat SemiRingCat.{u}) :=
  CommSemiRingCat.forget₂SemiRingPreservesLimitsOfSize.{u, u}
#align CommSemiRing.forget₂_SemiRing_preserves_limits CommSemiRingCat.forget₂SemiRingPreservesLimits
-/

#print CommSemiRingCat.forgetPreservesLimitsOfSize /-
/-- The forgetful functor from rings to types preserves all limits. (That is, the underlying
types could have been computed instead as limits in the category of types.)
-/
instance forgetPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget CommSemiRingCat.{max v u})
    where PreservesLimitsOfShape J 𝒥 :=
    {
      PreservesLimit := fun F =>
        limits.comp_preserves_limit (forget₂ CommSemiRingCat SemiRingCat) (forget SemiRingCat) }
#align CommSemiRing.forget_preserves_limits_of_size CommSemiRingCat.forgetPreservesLimitsOfSize
-/

#print CommSemiRingCat.forgetPreservesLimits /-
instance forgetPreservesLimits : PreservesLimits (forget CommSemiRingCat.{u}) :=
  CommSemiRingCat.forgetPreservesLimitsOfSize.{u, u}
#align CommSemiRing.forget_preserves_limits CommSemiRingCat.forgetPreservesLimits
-/

end CommSemiRingCat

namespace RingCat

variable {J : Type v} [SmallCategory J]

/- warning: Ring.ring_obj -> RingCat.ringObj is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 RingCat.{max u1 u2} RingCat.largeCategory.{max u1 u2}) (j : J), Ring.{max u1 u2} (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 Type.{max u1 u2} CategoryTheory.types.{max u1 u2} (CategoryTheory.Functor.comp.{u1, max u1 u2, max u1 u2, u1, succ (max u1 u2), succ (max u1 u2)} J _inst_1 RingCat.{max u1 u2} RingCat.largeCategory.{max u1 u2} Type.{max u1 u2} CategoryTheory.types.{max u1 u2} F (CategoryTheory.forget.{succ (max u1 u2), max u1 u2, max u1 u2} RingCat.{max u1 u2} RingCat.largeCategory.{max u1 u2} RingCat.concreteCategory.{max u1 u2})) j)
but is expected to have type
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 RingCatMax.{u1, u2} instRingCatLargeCategory.{max u2 u1}) (j : J), Ring.{max u2 u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) Type.{max u2 u1} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} Type.{max u2 u1} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} Type.{max u2 u1} CategoryTheory.types.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 Type.{max u2 u1} CategoryTheory.types.{max u2 u1} (CategoryTheory.Functor.comp.{u1, max u2 u1, max u2 u1, u1, max (succ u2) (succ u1), max (succ u2) (succ u1)} J _inst_1 RingCatMax.{u1, u2} instRingCatLargeCategory.{max u2 u1} Type.{max u2 u1} CategoryTheory.types.{max u2 u1} F (CategoryTheory.forget.{succ (max u2 u1), max u2 u1, max u2 u1} RingCat.{max u2 u1} instRingCatLargeCategory.{max u2 u1} RingCat.instConcreteCategoryRingCatInstRingCatLargeCategory.{max u2 u1}))) j)
Case conversion may be inaccurate. Consider using '#align Ring.ring_obj RingCat.ringObjₓ'. -/
instance ringObj (F : J ⥤ RingCat.{max v u}) (j) : Ring ((F ⋙ forget RingCat).obj j) := by
  change Ring (F.obj j); infer_instance
#align Ring.ring_obj RingCat.ringObj

/- warning: Ring.sections_subring -> RingCat.sectionsSubring is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 RingCat.{max u1 u2} RingCat.largeCategory.{max u1 u2}), Subring.{max u1 u2} (forall (j : J), coeSort.{succ (succ (max u1 u2)), succ (succ (max u1 u2))} RingCat.{max u1 u2} Type.{max u1 u2} RingCat.hasCoeToSort.{max u1 u2} (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 RingCat.{max u1 u2} RingCat.largeCategory.{max u1 u2} F j)) (Pi.ring.{u1, max u1 u2} J (fun (j : J) => coeSort.{succ (succ (max u1 u2)), succ (succ (max u1 u2))} RingCat.{max u1 u2} Type.{max u1 u2} RingCat.hasCoeToSort.{max u1 u2} (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 RingCat.{max u1 u2} RingCat.largeCategory.{max u1 u2} F j)) (fun (i : J) => RingCat.ring.{max u1 u2} (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 RingCat.{max u1 u2} RingCat.largeCategory.{max u1 u2} F i)))
but is expected to have type
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 RingCatMax.{u1, u2} instRingCatLargeCategory.{max u2 u1}), Subring.{max u1 u2} (forall (j : J), CategoryTheory.Bundled.α.{max u2 u1, max u2 u1} Ring.{max u2 u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) RingCatMax.{u1, u2} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} RingCatMax.{u1, u2} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} RingCatMax.{u1, u2} instRingCatLargeCategory.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 RingCatMax.{u1, u2} instRingCatLargeCategory.{max u2 u1} F) j)) (Pi.ring.{u1, max u2 u1} J (fun (j : J) => CategoryTheory.Bundled.α.{max u2 u1, max u2 u1} Ring.{max u2 u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) RingCatMax.{u1, u2} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} RingCatMax.{u1, u2} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} RingCatMax.{u1, u2} instRingCatLargeCategory.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 RingCatMax.{u1, u2} instRingCatLargeCategory.{max u2 u1} F) j)) (fun (i : J) => RingCat.instRingα_1.{max u2 u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) RingCatMax.{u1, u2} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} RingCatMax.{u1, u2} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} RingCatMax.{u1, u2} instRingCatLargeCategory.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 RingCatMax.{u1, u2} instRingCatLargeCategory.{max u2 u1} F) i)))
Case conversion may be inaccurate. Consider using '#align Ring.sections_subring RingCat.sectionsSubringₓ'. -/
/-- The flat sections of a functor into `Ring` form a subring of all sections.
-/
def sectionsSubring (F : J ⥤ RingCat.{max v u}) : Subring (∀ j, F.obj j) :=
  {
    AddGroupCat.sectionsAddSubgroup
      (F ⋙
        forget₂ RingCat AddCommGroupCat.{max v u} ⋙ forget₂ AddCommGroupCat AddGroupCat.{max v u}),
    SemiRingCat.sectionsSubsemiring (F ⋙ forget₂ RingCat SemiRingCat.{max v u}) with
    carrier := (F ⋙ forget RingCat).sections }
#align Ring.sections_subring RingCat.sectionsSubring

#print RingCat.limitRing /-
instance limitRing (F : J ⥤ RingCat.{max v u}) :
    Ring (Types.limitCone (F ⋙ forget RingCat.{max v u})).pt :=
  (sectionsSubring F).toRing
#align Ring.limit_ring RingCat.limitRing
-/

/-- We show that the forgetful functor `CommRing ⥤ Ring` creates limits.

All we need to do is notice that the limit point has a `ring` instance available,
and then reuse the existing limit.
-/
instance (F : J ⥤ RingCat.{max v u}) : CreatesLimit F (forget₂ RingCat SemiRingCat.{max v u}) :=
  createsLimitOfReflectsIso fun c' t =>
    { liftedCone :=
        { pt := RingCat.of (Types.limitCone (F ⋙ forget _)).pt
          π :=
            { app := by apply SemiRingCat.limitπRingHom (F ⋙ forget₂ RingCat SemiRingCat.{max v u})
              naturality' :=
                (SemiRingCat.HasLimits.limitCone
                      (F ⋙ forget₂ RingCat SemiRingCat.{max v u})).π.naturality } }
      validLift := by apply is_limit.unique_up_to_iso (SemiRingCat.HasLimits.limitConeIsLimit _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ RingCat SemiRingCat.{max v u})
          (by apply SemiRingCat.HasLimits.limitConeIsLimit _) (fun s => _) fun s => rfl }

#print RingCat.limitCone /-
/-- A choice of limit cone for a functor into `Ring`.
(Generally, you'll just want to use `limit F`.)
-/
def limitCone (F : J ⥤ RingCat.{max v u}) : Cone F :=
  liftLimit (limit.isLimit (F ⋙ forget₂ RingCat SemiRingCat.{max v u}))
#align Ring.limit_cone RingCat.limitCone
-/

#print RingCat.limitConeIsLimit /-
/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
def limitConeIsLimit (F : J ⥤ RingCat.{max v u}) : IsLimit (limitCone F) :=
  liftedLimitIsLimit _
#align Ring.limit_cone_is_limit RingCat.limitConeIsLimit
-/

/- ./././Mathport/Syntax/Translate/Command.lean:322:38: unsupported irreducible non-definition -/
#print RingCat.hasLimitsOfSize /-
/-- The category of rings has all limits. -/
irreducible_def hasLimitsOfSize : HasLimitsOfSize.{v, v} RingCat.{max v u} :=
  {
    HasLimitsOfShape := fun J 𝒥 =>
      { HasLimit := fun F => has_limit_of_created F (forget₂ RingCat SemiRingCat.{max v u}) } }
#align Ring.has_limits_of_size RingCat.hasLimitsOfSize
-/

#print RingCat.hasLimits /-
instance hasLimits : HasLimits RingCat.{u} :=
  RingCat.hasLimitsOfSize.{u, u}
#align Ring.has_limits RingCat.hasLimits
-/

#print RingCat.forget₂SemiRingPreservesLimitsOfSize /-
/-- The forgetful functor from rings to semirings preserves all limits.
-/
instance forget₂SemiRingPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ RingCat SemiRingCat.{max v u})
    where PreservesLimitsOfShape J 𝒥 := { PreservesLimit := fun F => by infer_instance }
#align Ring.forget₂_SemiRing_preserves_limits_of_size RingCat.forget₂SemiRingPreservesLimitsOfSize
-/

#print RingCat.forget₂SemiRingPreservesLimits /-
instance forget₂SemiRingPreservesLimits : PreservesLimits (forget₂ RingCat SemiRingCat.{u}) :=
  RingCat.forget₂SemiRingPreservesLimitsOfSize.{u, u}
#align Ring.forget₂_SemiRing_preserves_limits RingCat.forget₂SemiRingPreservesLimits
-/

/- warning: Ring.forget₂_AddCommGroup_preserves_limits_aux -> RingCat.forget₂AddCommGroupPreservesLimitsAux is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 RingCat.{max u1 u2} RingCat.largeCategory.{max u1 u2}), CategoryTheory.Limits.IsLimit.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 AddCommGroupCat.{max u1 u2} AddCommGroupCat.largeCategory.{max u1 u2} (CategoryTheory.Functor.comp.{u1, max u1 u2, max u1 u2, u1, succ (max u1 u2), succ (max u1 u2)} J _inst_1 RingCat.{max u1 u2} RingCat.largeCategory.{max u1 u2} AddCommGroupCat.{max u1 u2} AddCommGroupCat.largeCategory.{max u1 u2} F (CategoryTheory.forget₂.{succ (max u1 u2), succ (max u1 u2), max u1 u2, max u1 u2, max u1 u2} RingCat.{max u1 u2} AddCommGroupCat.{max u1 u2} RingCat.largeCategory.{max u1 u2} RingCat.concreteCategory.{max u1 u2} AddCommGroupCat.largeCategory.{max u1 u2} AddCommGroupCat.concreteCategory.{max u1 u2} RingCat.hasForgetToAddCommGroupCat.{max u1 u2})) (CategoryTheory.Functor.mapCone.{u1, max u1 u2, max u1 u2, u1, succ (max u1 u2), succ (max u1 u2)} J _inst_1 RingCat.{max u1 u2} RingCat.largeCategory.{max u1 u2} AddCommGroupCat.{max u1 u2} AddCommGroupCat.largeCategory.{max u1 u2} F (CategoryTheory.forget₂.{succ (max u1 u2), succ (max u1 u2), max u1 u2, max u1 u2, max u1 u2} RingCat.{max u1 u2} AddCommGroupCat.{max u1 u2} RingCat.largeCategory.{max u1 u2} RingCat.concreteCategory.{max u1 u2} AddCommGroupCat.largeCategory.{max u1 u2} AddCommGroupCat.concreteCategory.{max u1 u2} RingCat.hasForgetToAddCommGroupCat.{max u1 u2}) (RingCat.limitCone.{u1, u2} J _inst_1 F))
but is expected to have type
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 RingCatMax.{u1, u2} instRingCatLargeCategory.{max u2 u1}), CategoryTheory.Limits.IsLimit.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 AddCommGroupCat.{max u2 u1} instAddCommGroupCatLargeCategory.{max u2 u1} (CategoryTheory.Functor.comp.{u1, max u2 u1, max u2 u1, u1, max (succ u2) (succ u1), max (succ u2) (succ u1)} J _inst_1 RingCatMax.{u1, u2} instRingCatLargeCategory.{max u2 u1} AddCommGroupCat.{max u2 u1} instAddCommGroupCatLargeCategory.{max u2 u1} F (CategoryTheory.forget₂.{max (succ u2) (succ u1), succ (max u2 u1), max u2 u1, max u2 u1, max u2 u1} RingCatMax.{u1, u2} AddCommGroupCat.{max u2 u1} instRingCatLargeCategory.{max u2 u1} RingCat.instConcreteCategoryRingCatInstRingCatLargeCategory.{max u2 u1} instAddCommGroupCatLargeCategory.{max u2 u1} AddCommGroupCat.concreteCategory.{max u2 u1} RingCat.hasForgetToAddCommGroupCat.{max u2 u1})) (CategoryTheory.Functor.mapCone.{u1, max u2 u1, max u2 u1, u1, max (succ u2) (succ u1), max (succ u2) (succ u1)} J _inst_1 RingCatMax.{u1, u2} instRingCatLargeCategory.{max u2 u1} AddCommGroupCat.{max u2 u1} instAddCommGroupCatLargeCategory.{max u2 u1} (CategoryTheory.forget₂.{max (succ u2) (succ u1), succ (max u2 u1), max u2 u1, max u2 u1, max u2 u1} RingCatMax.{u1, u2} AddCommGroupCat.{max u2 u1} instRingCatLargeCategory.{max u2 u1} RingCat.instConcreteCategoryRingCatInstRingCatLargeCategory.{max u2 u1} instAddCommGroupCatLargeCategory.{max u2 u1} AddCommGroupCat.concreteCategory.{max u2 u1} RingCat.hasForgetToAddCommGroupCat.{max u2 u1}) F (RingCat.limitCone.{u1, u2} J _inst_1 F))
Case conversion may be inaccurate. Consider using '#align Ring.forget₂_AddCommGroup_preserves_limits_aux RingCat.forget₂AddCommGroupPreservesLimitsAuxₓ'. -/
/-- An auxiliary declaration to speed up typechecking.
-/
def forget₂AddCommGroupPreservesLimitsAux (F : J ⥤ RingCat.{max v u}) :
    IsLimit ((forget₂ RingCat AddCommGroupCat).mapCone (limitCone F)) := by
  apply AddCommGroupCat.limitConeIsLimit (F ⋙ forget₂ RingCat AddCommGroupCat.{max v u})
#align Ring.forget₂_AddCommGroup_preserves_limits_aux RingCat.forget₂AddCommGroupPreservesLimitsAux

#print RingCat.forget₂AddCommGroupPreservesLimitsOfSize /-
/-- The forgetful functor from rings to additive commutative groups preserves all limits.
-/
instance forget₂AddCommGroupPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ RingCat AddCommGroupCat.{max v u})
    where PreservesLimitsOfShape J 𝒥 :=
    {
      PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
          (forget₂_AddCommGroup_preserves_limits_aux F) }
#align Ring.forget₂_AddCommGroup_preserves_limits_of_size RingCat.forget₂AddCommGroupPreservesLimitsOfSize
-/

#print RingCat.forget₂AddCommGroupPreservesLimits /-
instance forget₂AddCommGroupPreservesLimits :
    PreservesLimits (forget₂ RingCat AddCommGroupCat.{u}) :=
  RingCat.forget₂AddCommGroupPreservesLimitsOfSize.{u, u}
#align Ring.forget₂_AddCommGroup_preserves_limits RingCat.forget₂AddCommGroupPreservesLimits
-/

#print RingCat.forgetPreservesLimitsOfSize /-
/-- The forgetful functor from rings to types preserves all limits. (That is, the underlying
types could have been computed instead as limits in the category of types.)
-/
instance forgetPreservesLimitsOfSize : PreservesLimitsOfSize.{v, v} (forget RingCat.{max v u})
    where PreservesLimitsOfShape J 𝒥 :=
    {
      PreservesLimit := fun F =>
        limits.comp_preserves_limit (forget₂ RingCat SemiRingCat) (forget SemiRingCat.{max v u}) }
#align Ring.forget_preserves_limits_of_size RingCat.forgetPreservesLimitsOfSize
-/

#print RingCat.forgetPreservesLimits /-
instance forgetPreservesLimits : PreservesLimits (forget RingCat.{u}) :=
  RingCat.forgetPreservesLimitsOfSize.{u, u}
#align Ring.forget_preserves_limits RingCat.forgetPreservesLimits
-/

end RingCat

namespace CommRingCat

variable {J : Type v} [SmallCategory J]

/- warning: CommRing.comm_ring_obj -> CommRingCat.commRingObj is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 CommRingCat.{max u1 u2} CommRingCat.largeCategory.{max u1 u2}) (j : J), CommRing.{max u1 u2} (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 Type.{max u1 u2} CategoryTheory.types.{max u1 u2} (CategoryTheory.Functor.comp.{u1, max u1 u2, max u1 u2, u1, succ (max u1 u2), succ (max u1 u2)} J _inst_1 CommRingCat.{max u1 u2} CommRingCat.largeCategory.{max u1 u2} Type.{max u1 u2} CategoryTheory.types.{max u1 u2} F (CategoryTheory.forget.{succ (max u1 u2), max u1 u2, max u1 u2} CommRingCat.{max u1 u2} CommRingCat.largeCategory.{max u1 u2} CommRingCat.concreteCategory.{max u1 u2})) j)
but is expected to have type
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 CommRingCatMax.{u1, u2} instCommRingCatLargeCategory.{max u2 u1}) (j : J), CommRing.{max u2 u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u1, max (succ u2) (succ u1)} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) Type.{max u2 u1} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (succ u2) (succ u1)} Type.{max u2 u1} (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (succ u2) (succ u1)} Type.{max u2 u1} CategoryTheory.types.{max u2 u1})) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 Type.{max u2 u1} CategoryTheory.types.{max u2 u1} (CategoryTheory.Functor.comp.{u1, max u2 u1, max u2 u1, u1, max (succ u2) (succ u1), max (succ u2) (succ u1)} J _inst_1 CommRingCatMax.{u1, u2} instCommRingCatLargeCategory.{max u2 u1} Type.{max u2 u1} CategoryTheory.types.{max u2 u1} F (CategoryTheory.forget.{succ (max u2 u1), max u2 u1, max u2 u1} CommRingCat.{max u2 u1} instCommRingCatLargeCategory.{max u2 u1} CommRingCat.instConcreteCategoryCommRingCatInstCommRingCatLargeCategory.{max u2 u1}))) j)
Case conversion may be inaccurate. Consider using '#align CommRing.comm_ring_obj CommRingCat.commRingObjₓ'. -/
instance commRingObj (F : J ⥤ CommRingCat.{max v u}) (j) :
    CommRing ((F ⋙ forget CommRingCat).obj j) := by change CommRing (F.obj j); infer_instance
#align CommRing.comm_ring_obj CommRingCat.commRingObj

#print CommRingCat.limitCommRing /-
instance limitCommRing (F : J ⥤ CommRingCat.{max v u}) :
    CommRing (Types.limitCone (F ⋙ forget CommRingCat.{max v u})).pt :=
  @Subring.toCommRing (∀ j, F.obj j) _
    (RingCat.sectionsSubring (F ⋙ forget₂ CommRingCat RingCat.{max v u}))
#align CommRing.limit_comm_ring CommRingCat.limitCommRing
-/

/-- We show that the forgetful functor `CommRing ⥤ Ring` creates limits.

All we need to do is notice that the limit point has a `comm_ring` instance available,
and then reuse the existing limit.
-/
instance (F : J ⥤ CommRingCat.{max v u}) : CreatesLimit F (forget₂ CommRingCat RingCat.{max v u}) :=
  /-
    A terse solution here would be
    ```
    creates_limit_of_fully_faithful_of_iso (CommRing.of (limit (F ⋙ forget _))) (iso.refl _)
    ```
    but it seems this would introduce additional identity morphisms in `limit.π`.
    -/
    createsLimitOfReflectsIso
    fun c' t =>
    { liftedCone :=
        { pt := CommRingCat.of (Types.limitCone (F ⋙ forget _)).pt
          π :=
            { app := by
                apply
                  SemiRingCat.limitπRingHom
                    (F ⋙
                      forget₂ CommRingCat RingCat.{max v u} ⋙ forget₂ RingCat SemiRingCat.{max v u})
              naturality' :=
                (SemiRingCat.HasLimits.limitCone
                      (F ⋙
                        forget₂ _ RingCat.{max v u} ⋙
                          forget₂ _ SemiRingCat.{max v u})).π.naturality } }
      validLift := by apply is_limit.unique_up_to_iso (RingCat.limitConeIsLimit _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ _ RingCat.{max v u})
          (by apply RingCat.limitConeIsLimit (F ⋙ forget₂ CommRingCat RingCat.{max v u}))
          (fun s => (RingCat.limitConeIsLimit _).lift ((forget₂ _ RingCat.{max v u}).mapCone s))
          fun s => rfl }

#print CommRingCat.limitCone /-
/-- A choice of limit cone for a functor into `CommRing`.
(Generally, you'll just want to use `limit F`.)
-/
def limitCone (F : J ⥤ CommRingCat.{max v u}) : Cone F :=
  liftLimit (limit.isLimit (F ⋙ forget₂ CommRingCat RingCat.{max v u}))
#align CommRing.limit_cone CommRingCat.limitCone
-/

#print CommRingCat.limitConeIsLimit /-
/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
def limitConeIsLimit (F : J ⥤ CommRingCat.{max v u}) : IsLimit (limitCone F) :=
  liftedLimitIsLimit _
#align CommRing.limit_cone_is_limit CommRingCat.limitConeIsLimit
-/

/- ./././Mathport/Syntax/Translate/Command.lean:322:38: unsupported irreducible non-definition -/
#print CommRingCat.hasLimitsOfSize /-
/-- The category of commutative rings has all limits. -/
irreducible_def hasLimitsOfSize : HasLimitsOfSize.{v, v} CommRingCat.{max v u} :=
  {
    HasLimitsOfShape := fun J 𝒥 =>
      { HasLimit := fun F => has_limit_of_created F (forget₂ CommRingCat RingCat.{max v u}) } }
#align CommRing.has_limits_of_size CommRingCat.hasLimitsOfSize
-/

#print CommRingCat.hasLimits /-
instance hasLimits : HasLimits CommRingCat.{u} :=
  CommRingCat.hasLimitsOfSize.{u, u}
#align CommRing.has_limits CommRingCat.hasLimits
-/

#print CommRingCat.forget₂RingPreservesLimitsOfSize /-
/-- The forgetful functor from commutative rings to rings preserves all limits.
(That is, the underlying rings could have been computed instead as limits in the category of rings.)
-/
instance forget₂RingPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ CommRingCat RingCat.{max v u})
    where PreservesLimitsOfShape J 𝒥 := { PreservesLimit := fun F => by infer_instance }
#align CommRing.forget₂_Ring_preserves_limits_of_size CommRingCat.forget₂RingPreservesLimitsOfSize
-/

#print CommRingCat.forget₂RingPreservesLimits /-
instance forget₂RingPreservesLimits : PreservesLimits (forget₂ CommRingCat RingCat.{u}) :=
  CommRingCat.forget₂RingPreservesLimitsOfSize.{u, u}
#align CommRing.forget₂_Ring_preserves_limits CommRingCat.forget₂RingPreservesLimits
-/

/- warning: CommRing.forget₂_CommSemiRing_preserves_limits_aux -> CommRingCat.forget₂CommSemiRingPreservesLimitsAux is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 CommRingCat.{max u1 u2} CommRingCat.largeCategory.{max u1 u2}), CategoryTheory.Limits.IsLimit.{u1, max u1 u2, u1, succ (max u1 u2)} J _inst_1 CommSemiRingCat.{max u1 u2} CommSemiRingCat.largeCategory.{max u1 u2} (CategoryTheory.Functor.comp.{u1, max u1 u2, max u1 u2, u1, succ (max u1 u2), succ (max u1 u2)} J _inst_1 CommRingCat.{max u1 u2} CommRingCat.largeCategory.{max u1 u2} CommSemiRingCat.{max u1 u2} CommSemiRingCat.largeCategory.{max u1 u2} F (CategoryTheory.forget₂.{succ (max u1 u2), succ (max u1 u2), max u1 u2, max u1 u2, max u1 u2} CommRingCat.{max u1 u2} CommSemiRingCat.{max u1 u2} CommRingCat.largeCategory.{max u1 u2} CommRingCat.concreteCategory.{max u1 u2} CommSemiRingCat.largeCategory.{max u1 u2} CommSemiRingCat.concreteCategory.{max u1 u2} CommRingCat.hasForgetToCommSemiRingCat.{max u1 u2})) (CategoryTheory.Functor.mapCone.{u1, max u1 u2, max u1 u2, u1, succ (max u1 u2), succ (max u1 u2)} J _inst_1 CommRingCat.{max u1 u2} CommRingCat.largeCategory.{max u1 u2} CommSemiRingCat.{max u1 u2} CommSemiRingCat.largeCategory.{max u1 u2} F (CategoryTheory.forget₂.{succ (max u1 u2), succ (max u1 u2), max u1 u2, max u1 u2, max u1 u2} CommRingCat.{max u1 u2} CommSemiRingCat.{max u1 u2} CommRingCat.largeCategory.{max u1 u2} CommRingCat.concreteCategory.{max u1 u2} CommSemiRingCat.largeCategory.{max u1 u2} CommSemiRingCat.concreteCategory.{max u1 u2} CommRingCat.hasForgetToCommSemiRingCat.{max u1 u2}) (CommRingCat.limitCone.{u1, u2} J _inst_1 F))
but is expected to have type
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, max u2 u1, u1, max (succ u2) (succ u1)} J _inst_1 CommRingCatMax.{u1, u2} instCommRingCatLargeCategory.{max u2 u1}), CategoryTheory.Limits.IsLimit.{u1, max u2 u1, u1, succ (max u2 u1)} J _inst_1 CommSemiRingCat.{max u2 u1} instCommSemiRingCatLargeCategory.{max u2 u1} (CategoryTheory.Functor.comp.{u1, max u2 u1, max u2 u1, u1, succ (max u2 u1), succ (max u2 u1)} J _inst_1 CommRingCat.{max u2 u1} instCommRingCatLargeCategory.{max u2 u1} CommSemiRingCat.{max u2 u1} instCommSemiRingCatLargeCategory.{max u2 u1} F (CategoryTheory.forget₂.{succ (max u2 u1), succ (max u2 u1), max u2 u1, max u2 u1, max u2 u1} CommRingCat.{max u2 u1} CommSemiRingCat.{max u2 u1} instCommRingCatLargeCategory.{max u2 u1} CommRingCat.instConcreteCategoryCommRingCatInstCommRingCatLargeCategory.{max u2 u1} instCommSemiRingCatLargeCategory.{max u2 u1} CommSemiRing.instConcreteCategoryCommSemiRingCatInstCommSemiRingCatLargeCategory.{max u2 u1} CommRingCat.hasForgetToCommSemiRingCat.{max u2 u1})) (CategoryTheory.Functor.mapCone.{u1, max u2 u1, max u2 u1, u1, succ (max u2 u1), succ (max u2 u1)} J _inst_1 CommRingCat.{max u2 u1} instCommRingCatLargeCategory.{max u2 u1} CommSemiRingCat.{max u2 u1} instCommSemiRingCatLargeCategory.{max u2 u1} (CategoryTheory.forget₂.{succ (max u2 u1), succ (max u2 u1), max u2 u1, max u2 u1, max u2 u1} CommRingCat.{max u2 u1} CommSemiRingCat.{max u2 u1} instCommRingCatLargeCategory.{max u2 u1} CommRingCat.instConcreteCategoryCommRingCatInstCommRingCatLargeCategory.{max u2 u1} instCommSemiRingCatLargeCategory.{max u2 u1} CommSemiRing.instConcreteCategoryCommSemiRingCatInstCommSemiRingCatLargeCategory.{max u2 u1} CommRingCat.hasForgetToCommSemiRingCat.{max u2 u1}) F (CommRingCat.limitCone.{u1, u2} J _inst_1 F))
Case conversion may be inaccurate. Consider using '#align CommRing.forget₂_CommSemiRing_preserves_limits_aux CommRingCat.forget₂CommSemiRingPreservesLimitsAuxₓ'. -/
/-- An auxiliary declaration to speed up typechecking.
-/
def forget₂CommSemiRingPreservesLimitsAux (F : J ⥤ CommRingCat.{max v u}) :
    IsLimit ((forget₂ CommRingCat CommSemiRingCat).mapCone (limitCone F)) := by
  apply CommSemiRingCat.limitConeIsLimit (F ⋙ forget₂ CommRingCat CommSemiRingCat.{max v u})
#align CommRing.forget₂_CommSemiRing_preserves_limits_aux CommRingCat.forget₂CommSemiRingPreservesLimitsAux

#print CommRingCat.forget₂CommSemiRingPreservesLimitsOfSize /-
/-- The forgetful functor from commutative rings to commutative semirings preserves all limits.
(That is, the underlying commutative semirings could have been computed instead as limits
in the category of commutative semirings.)
-/
instance forget₂CommSemiRingPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ CommRingCat CommSemiRingCat.{max v u})
    where PreservesLimitsOfShape J 𝒥 :=
    {
      PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
          (forget₂_CommSemiRing_preserves_limits_aux F) }
#align CommRing.forget₂_CommSemiRing_preserves_limits_of_size CommRingCat.forget₂CommSemiRingPreservesLimitsOfSize
-/

#print CommRingCat.forget₂CommSemiRingPreservesLimits /-
instance forget₂CommSemiRingPreservesLimits :
    PreservesLimits (forget₂ CommRingCat CommSemiRingCat.{u}) :=
  CommRingCat.forget₂CommSemiRingPreservesLimitsOfSize.{u, u}
#align CommRing.forget₂_CommSemiRing_preserves_limits CommRingCat.forget₂CommSemiRingPreservesLimits
-/

#print CommRingCat.forgetPreservesLimitsOfSize /-
/-- The forgetful functor from commutative rings to types preserves all limits.
(That is, the underlying types could have been computed instead as limits in the category of types.)
-/
instance forgetPreservesLimitsOfSize : PreservesLimitsOfSize.{v, v} (forget CommRingCat.{max v u})
    where PreservesLimitsOfShape J 𝒥 :=
    {
      PreservesLimit := fun F =>
        limits.comp_preserves_limit (forget₂ CommRingCat RingCat) (forget RingCat) }
#align CommRing.forget_preserves_limits_of_size CommRingCat.forgetPreservesLimitsOfSize
-/

#print CommRingCat.forgetPreservesLimits /-
instance forgetPreservesLimits : PreservesLimits (forget CommRingCat.{u}) :=
  CommRingCat.forgetPreservesLimitsOfSize.{u, u}
#align CommRing.forget_preserves_limits CommRingCat.forgetPreservesLimits
-/

end CommRingCat

