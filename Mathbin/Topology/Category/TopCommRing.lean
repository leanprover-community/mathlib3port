/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module topology.category.TopCommRing
! leanprover-community/mathlib commit 33c67ae661dd8988516ff7f247b0be3018cdd952
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Ring.Basic
import Mathbin.Topology.Category.Top.Basic
import Mathbin.Topology.Algebra.Ring.Basic

/-!
# Category of topological commutative rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We introduce the category `TopCommRing` of topological commutative rings together with the relevant
forgetful functors to topological spaces and commutative rings.
-/


universe u

open CategoryTheory

#print TopCommRingCat /-
/-- A bundled topological commutative ring. -/
structure TopCommRingCat where
  α : Type u
  [isCommRing : CommRing α]
  [isTopologicalSpace : TopologicalSpace α]
  [is_topologicalRing : TopologicalRing α]
#align TopCommRing TopCommRingCat
-/

namespace TopCommRingCat

instance : Inhabited TopCommRingCat :=
  ⟨⟨PUnit⟩⟩

instance : CoeSort TopCommRingCat (Type u) :=
  ⟨TopCommRingCat.α⟩

attribute [instance] is_comm_ring is_topological_space is_topological_ring

instance : Category TopCommRingCat.{u}
    where
  Hom R S := { f : R →+* S // Continuous f }
  id R := ⟨RingHom.id R, by obviously⟩
  -- TODO remove obviously?
  comp R S T f g :=
    ⟨g.val.comp f.val,
      by
      -- TODO automate
      cases f;
      cases g
      dsimp; apply Continuous.comp <;> assumption⟩

instance : ConcreteCategory TopCommRingCat.{u}
    where
  forget :=
    { obj := fun R => R
      map := fun R S f => f.val }
  forget_faithful := { }

#print TopCommRingCat.of /-
/-- Construct a bundled `TopCommRing` from the underlying type and the appropriate typeclasses. -/
def of (X : Type u) [CommRing X] [TopologicalSpace X] [TopologicalRing X] : TopCommRingCat :=
  ⟨X⟩
#align TopCommRing.of TopCommRingCat.of
-/

#print TopCommRingCat.coe_of /-
@[simp]
theorem coe_of (X : Type u) [CommRing X] [TopologicalSpace X] [TopologicalRing X] :
    (of X : Type u) = X :=
  rfl
#align TopCommRing.coe_of TopCommRingCat.coe_of
-/

/- warning: TopCommRing.forget_topological_space -> TopCommRingCat.forgetTopologicalSpace is a dubious translation:
lean 3 declaration is
  forall (R : TopCommRingCat.{u1}), TopologicalSpace.{u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.CategoryTheory.category.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCommRingCat.{u1} TopCommRingCat.CategoryTheory.category.{u1} TopCommRingCat.CategoryTheory.concreteCategory.{u1}) R)
but is expected to have type
  forall (R : TopCommRingCat.{u1}), TopologicalSpace.{u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCommRingCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCommRingCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1} TopCommRingCat.instConcreteCategoryTopCommRingCatInstCategoryTopCommRingCat.{u1})) R)
Case conversion may be inaccurate. Consider using '#align TopCommRing.forget_topological_space TopCommRingCat.forgetTopologicalSpaceₓ'. -/
instance forgetTopologicalSpace (R : TopCommRingCat) :
    TopologicalSpace ((forget TopCommRingCat).obj R) :=
  R.isTopologicalSpace
#align TopCommRing.forget_topological_space TopCommRingCat.forgetTopologicalSpace

/- warning: TopCommRing.forget_comm_ring -> TopCommRingCat.forgetCommRing is a dubious translation:
lean 3 declaration is
  forall (R : TopCommRingCat.{u1}), CommRing.{u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.CategoryTheory.category.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCommRingCat.{u1} TopCommRingCat.CategoryTheory.category.{u1} TopCommRingCat.CategoryTheory.concreteCategory.{u1}) R)
but is expected to have type
  forall (R : TopCommRingCat.{u1}), CommRing.{u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCommRingCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCommRingCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1} TopCommRingCat.instConcreteCategoryTopCommRingCatInstCategoryTopCommRingCat.{u1})) R)
Case conversion may be inaccurate. Consider using '#align TopCommRing.forget_comm_ring TopCommRingCat.forgetCommRingₓ'. -/
instance forgetCommRing (R : TopCommRingCat) : CommRing ((forget TopCommRingCat).obj R) :=
  R.isCommRing
#align TopCommRing.forget_comm_ring TopCommRingCat.forgetCommRing

/- warning: TopCommRing.forget_topological_ring -> TopCommRingCat.forgetTopologicalRing is a dubious translation:
lean 3 declaration is
  forall (R : TopCommRingCat.{u1}), TopologicalRing.{u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.CategoryTheory.category.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCommRingCat.{u1} TopCommRingCat.CategoryTheory.category.{u1} TopCommRingCat.CategoryTheory.concreteCategory.{u1}) R) (TopCommRingCat.forgetTopologicalSpace.{u1} R) (NonAssocRing.toNonUnitalNonAssocRing.{u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.CategoryTheory.category.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCommRingCat.{u1} TopCommRingCat.CategoryTheory.category.{u1} TopCommRingCat.CategoryTheory.concreteCategory.{u1}) R) (Ring.toNonAssocRing.{u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.CategoryTheory.category.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCommRingCat.{u1} TopCommRingCat.CategoryTheory.category.{u1} TopCommRingCat.CategoryTheory.concreteCategory.{u1}) R) (CommRing.toRing.{u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.CategoryTheory.category.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCommRingCat.{u1} TopCommRingCat.CategoryTheory.category.{u1} TopCommRingCat.CategoryTheory.concreteCategory.{u1}) R) (TopCommRingCat.forgetCommRing.{u1} R))))
but is expected to have type
  forall (R : TopCommRingCat.{u1}), TopologicalRing.{u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCommRingCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCommRingCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1} TopCommRingCat.instConcreteCategoryTopCommRingCatInstCategoryTopCommRingCat.{u1})) R) (TopCommRingCat.forgetTopologicalSpace.{u1} R) (NonAssocRing.toNonUnitalNonAssocRing.{u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCommRingCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCommRingCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1} TopCommRingCat.instConcreteCategoryTopCommRingCatInstCategoryTopCommRingCat.{u1})) R) (Ring.toNonAssocRing.{u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCommRingCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCommRingCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1} TopCommRingCat.instConcreteCategoryTopCommRingCatInstCategoryTopCommRingCat.{u1})) R) (CommRing.toRing.{u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCommRingCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCommRingCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1} TopCommRingCat.instConcreteCategoryTopCommRingCatInstCategoryTopCommRingCat.{u1})) R) (TopCommRingCat.forgetCommRing.{u1} R))))
Case conversion may be inaccurate. Consider using '#align TopCommRing.forget_topological_ring TopCommRingCat.forgetTopologicalRingₓ'. -/
instance forgetTopologicalRing (R : TopCommRingCat) :
    TopologicalRing ((forget TopCommRingCat).obj R) :=
  R.is_topologicalRing
#align TopCommRing.forget_topological_ring TopCommRingCat.forgetTopologicalRing

/- warning: TopCommRing.has_forget_to_CommRing -> TopCommRingCat.hasForgetToCommRingCat is a dubious translation:
lean 3 declaration is
  CategoryTheory.HasForget₂.{succ u1, succ u1, u1, u1, u1} TopCommRingCat.{u1} CommRingCat.{u1} TopCommRingCat.CategoryTheory.category.{u1} TopCommRingCat.CategoryTheory.concreteCategory.{u1} CommRingCat.largeCategory.{u1} CommRingCat.concreteCategory.{u1}
but is expected to have type
  CategoryTheory.HasForget₂.{succ u1, succ u1, u1, u1, u1} TopCommRingCat.{u1} CommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1} TopCommRingCat.instConcreteCategoryTopCommRingCatInstCategoryTopCommRingCat.{u1} instCommRingCatLargeCategory.{u1} CommRingCat.instConcreteCategoryCommRingCatInstCommRingCatLargeCategory.{u1}
Case conversion may be inaccurate. Consider using '#align TopCommRing.has_forget_to_CommRing TopCommRingCat.hasForgetToCommRingCatₓ'. -/
instance hasForgetToCommRingCat : HasForget₂ TopCommRingCat CommRingCat :=
  HasForget₂.mk' (fun R => CommRingCat.of R) (fun x => rfl) (fun R S f => f.val) fun R S f =>
    HEq.rfl
#align TopCommRing.has_forget_to_CommRing TopCommRingCat.hasForgetToCommRingCat

/- warning: TopCommRing.forget_to_CommRing_topological_space -> TopCommRingCat.forgetToCommRingCatTopologicalSpace is a dubious translation:
lean 3 declaration is
  forall (R : TopCommRingCat.{u1}), TopologicalSpace.{u1} (coeSort.{succ (succ u1), succ (succ u1)} CommRingCat.{u1} Type.{u1} CommRingCat.hasCoeToSort.{u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.CategoryTheory.category.{u1} CommRingCat.{u1} CommRingCat.largeCategory.{u1} (CategoryTheory.forget₂.{succ u1, succ u1, u1, u1, u1} TopCommRingCat.{u1} CommRingCat.{u1} TopCommRingCat.CategoryTheory.category.{u1} TopCommRingCat.CategoryTheory.concreteCategory.{u1} CommRingCat.largeCategory.{u1} CommRingCat.concreteCategory.{u1} TopCommRingCat.hasForgetToCommRingCat.{u1}) R))
but is expected to have type
  forall (R : TopCommRingCat.{u1}), TopologicalSpace.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommRing.{u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCommRingCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCommRingCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1})) CommRingCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CommRingCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CommRingCat.{u1} instCommRingCatLargeCategory.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1} CommRingCat.{u1} instCommRingCatLargeCategory.{u1} (CategoryTheory.forget₂.{succ u1, succ u1, u1, u1, u1} TopCommRingCat.{u1} CommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1} TopCommRingCat.instConcreteCategoryTopCommRingCatInstCategoryTopCommRingCat.{u1} instCommRingCatLargeCategory.{u1} CommRingCat.instConcreteCategoryCommRingCatInstCommRingCatLargeCategory.{u1} TopCommRingCat.hasForgetToCommRingCat.{u1})) R))
Case conversion may be inaccurate. Consider using '#align TopCommRing.forget_to_CommRing_topological_space TopCommRingCat.forgetToCommRingCatTopologicalSpaceₓ'. -/
instance forgetToCommRingCatTopologicalSpace (R : TopCommRingCat) :
    TopologicalSpace ((forget₂ TopCommRingCat CommRingCat).obj R) :=
  R.isTopologicalSpace
#align TopCommRing.forget_to_CommRing_topological_space TopCommRingCat.forgetToCommRingCatTopologicalSpace

/- warning: TopCommRing.has_forget_to_Top -> TopCommRingCat.hasForgetToTopCat is a dubious translation:
lean 3 declaration is
  CategoryTheory.HasForget₂.{succ u1, succ u1, u1, u1, u1} TopCommRingCat.{u1} TopCat.{u1} TopCommRingCat.CategoryTheory.category.{u1} TopCommRingCat.CategoryTheory.concreteCategory.{u1} TopCat.largeCategory.{u1} TopCat.concreteCategory.{u1}
but is expected to have type
  CategoryTheory.HasForget₂.{succ u1, succ u1, u1, u1, u1} TopCommRingCat.{u1} TopCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1} TopCommRingCat.instConcreteCategoryTopCommRingCatInstCategoryTopCommRingCat.{u1} instTopCatLargeCategory.{u1} TopCat.concreteCategory.{u1}
Case conversion may be inaccurate. Consider using '#align TopCommRing.has_forget_to_Top TopCommRingCat.hasForgetToTopCatₓ'. -/
/-- The forgetful functor to Top. -/
instance hasForgetToTopCat : HasForget₂ TopCommRingCat TopCat :=
  HasForget₂.mk' (fun R => TopCat.of R) (fun x => rfl) (fun R S f => ⟨⇑f.1, f.2⟩) fun R S f =>
    HEq.rfl
#align TopCommRing.has_forget_to_Top TopCommRingCat.hasForgetToTopCat

/- warning: TopCommRing.forget_to_Top_comm_ring -> TopCommRingCat.forgetToTopCatCommRing is a dubious translation:
lean 3 declaration is
  forall (R : TopCommRingCat.{u1}), CommRing.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.CategoryTheory.category.{u1} TopCat.{u1} TopCat.largeCategory.{u1} (CategoryTheory.forget₂.{succ u1, succ u1, u1, u1, u1} TopCommRingCat.{u1} TopCat.{u1} TopCommRingCat.CategoryTheory.category.{u1} TopCommRingCat.CategoryTheory.concreteCategory.{u1} TopCat.largeCategory.{u1} TopCat.concreteCategory.{u1} TopCommRingCat.hasForgetToTopCat.{u1}) R))
but is expected to have type
  forall (R : TopCommRingCat.{u1}), CommRing.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCommRingCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCommRingCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1})) TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1} TopCat.{u1} instTopCatLargeCategory.{u1} (CategoryTheory.forget₂.{succ u1, succ u1, u1, u1, u1} TopCommRingCat.{u1} TopCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1} TopCommRingCat.instConcreteCategoryTopCommRingCatInstCategoryTopCommRingCat.{u1} instTopCatLargeCategory.{u1} TopCat.concreteCategory.{u1} TopCommRingCat.hasForgetToTopCat.{u1})) R))
Case conversion may be inaccurate. Consider using '#align TopCommRing.forget_to_Top_comm_ring TopCommRingCat.forgetToTopCatCommRingₓ'. -/
instance forgetToTopCatCommRing (R : TopCommRingCat) :
    CommRing ((forget₂ TopCommRingCat TopCat).obj R) :=
  R.isCommRing
#align TopCommRing.forget_to_Top_comm_ring TopCommRingCat.forgetToTopCatCommRing

/- warning: TopCommRing.forget_to_Top_topological_ring -> TopCommRingCat.forgetToTopCatTopologicalRing is a dubious translation:
lean 3 declaration is
  forall (R : TopCommRingCat.{u1}), TopologicalRing.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.CategoryTheory.category.{u1} TopCat.{u1} TopCat.largeCategory.{u1} (CategoryTheory.forget₂.{succ u1, succ u1, u1, u1, u1} TopCommRingCat.{u1} TopCat.{u1} TopCommRingCat.CategoryTheory.category.{u1} TopCommRingCat.CategoryTheory.concreteCategory.{u1} TopCat.largeCategory.{u1} TopCat.concreteCategory.{u1} TopCommRingCat.hasForgetToTopCat.{u1}) R)) (TopCat.topologicalSpace.{u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.CategoryTheory.category.{u1} TopCat.{u1} TopCat.largeCategory.{u1} (CategoryTheory.forget₂.{succ u1, succ u1, u1, u1, u1} TopCommRingCat.{u1} TopCat.{u1} TopCommRingCat.CategoryTheory.category.{u1} TopCommRingCat.CategoryTheory.concreteCategory.{u1} TopCat.largeCategory.{u1} TopCat.concreteCategory.{u1} TopCommRingCat.hasForgetToTopCat.{u1}) R)) (NonAssocRing.toNonUnitalNonAssocRing.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.CategoryTheory.category.{u1} TopCat.{u1} TopCat.largeCategory.{u1} (CategoryTheory.forget₂.{succ u1, succ u1, u1, u1, u1} TopCommRingCat.{u1} TopCat.{u1} TopCommRingCat.CategoryTheory.category.{u1} TopCommRingCat.CategoryTheory.concreteCategory.{u1} TopCat.largeCategory.{u1} TopCat.concreteCategory.{u1} TopCommRingCat.hasForgetToTopCat.{u1}) R)) (Ring.toNonAssocRing.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.CategoryTheory.category.{u1} TopCat.{u1} TopCat.largeCategory.{u1} (CategoryTheory.forget₂.{succ u1, succ u1, u1, u1, u1} TopCommRingCat.{u1} TopCat.{u1} TopCommRingCat.CategoryTheory.category.{u1} TopCommRingCat.CategoryTheory.concreteCategory.{u1} TopCat.largeCategory.{u1} TopCat.concreteCategory.{u1} TopCommRingCat.hasForgetToTopCat.{u1}) R)) (CommRing.toRing.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.CategoryTheory.category.{u1} TopCat.{u1} TopCat.largeCategory.{u1} (CategoryTheory.forget₂.{succ u1, succ u1, u1, u1, u1} TopCommRingCat.{u1} TopCat.{u1} TopCommRingCat.CategoryTheory.category.{u1} TopCommRingCat.CategoryTheory.concreteCategory.{u1} TopCat.largeCategory.{u1} TopCat.concreteCategory.{u1} TopCommRingCat.hasForgetToTopCat.{u1}) R)) (TopCommRingCat.forgetToTopCatCommRing.{u1} R))))
but is expected to have type
  forall (R : TopCommRingCat.{u1}), TopologicalRing.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCommRingCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCommRingCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1})) TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1} TopCat.{u1} instTopCatLargeCategory.{u1} (CategoryTheory.forget₂.{succ u1, succ u1, u1, u1, u1} TopCommRingCat.{u1} TopCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1} TopCommRingCat.instConcreteCategoryTopCommRingCatInstCategoryTopCommRingCat.{u1} instTopCatLargeCategory.{u1} TopCat.concreteCategory.{u1} TopCommRingCat.hasForgetToTopCat.{u1})) R)) (TopCat.topologicalSpace_coe.{u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCommRingCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCommRingCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1})) TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1} TopCat.{u1} instTopCatLargeCategory.{u1} (CategoryTheory.forget₂.{succ u1, succ u1, u1, u1, u1} TopCommRingCat.{u1} TopCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1} TopCommRingCat.instConcreteCategoryTopCommRingCatInstCategoryTopCommRingCat.{u1} instTopCatLargeCategory.{u1} TopCat.concreteCategory.{u1} TopCommRingCat.hasForgetToTopCat.{u1})) R)) (NonAssocRing.toNonUnitalNonAssocRing.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCommRingCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCommRingCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1})) TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1} TopCat.{u1} instTopCatLargeCategory.{u1} (CategoryTheory.forget₂.{succ u1, succ u1, u1, u1, u1} TopCommRingCat.{u1} TopCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1} TopCommRingCat.instConcreteCategoryTopCommRingCatInstCategoryTopCommRingCat.{u1} instTopCatLargeCategory.{u1} TopCat.concreteCategory.{u1} TopCommRingCat.hasForgetToTopCat.{u1})) R)) (Ring.toNonAssocRing.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCommRingCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCommRingCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1})) TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1} TopCat.{u1} instTopCatLargeCategory.{u1} (CategoryTheory.forget₂.{succ u1, succ u1, u1, u1, u1} TopCommRingCat.{u1} TopCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1} TopCommRingCat.instConcreteCategoryTopCommRingCatInstCategoryTopCommRingCat.{u1} instTopCatLargeCategory.{u1} TopCat.concreteCategory.{u1} TopCommRingCat.hasForgetToTopCat.{u1})) R)) (CommRing.toRing.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} TopCommRingCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCommRingCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1})) TopCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} TopCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} TopCat.{u1} instTopCatLargeCategory.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} TopCommRingCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1} TopCat.{u1} instTopCatLargeCategory.{u1} (CategoryTheory.forget₂.{succ u1, succ u1, u1, u1, u1} TopCommRingCat.{u1} TopCat.{u1} TopCommRingCat.instCategoryTopCommRingCat.{u1} TopCommRingCat.instConcreteCategoryTopCommRingCatInstCategoryTopCommRingCat.{u1} instTopCatLargeCategory.{u1} TopCat.concreteCategory.{u1} TopCommRingCat.hasForgetToTopCat.{u1})) R)) (TopCommRingCat.forgetToTopCatCommRing.{u1} R))))
Case conversion may be inaccurate. Consider using '#align TopCommRing.forget_to_Top_topological_ring TopCommRingCat.forgetToTopCatTopologicalRingₓ'. -/
instance forgetToTopCatTopologicalRing (R : TopCommRingCat) :
    TopologicalRing ((forget₂ TopCommRingCat TopCat).obj R) :=
  R.is_topologicalRing
#align TopCommRing.forget_to_Top_topological_ring TopCommRingCat.forgetToTopCatTopologicalRing

/-- The forgetful functors to `Type` do not reflect isomorphisms,
but the forgetful functor from `TopCommRing` to `Top` does.
-/
instance : ReflectsIsomorphisms (forget₂ TopCommRingCat.{u} TopCat.{u})
    where reflects X Y f _ := by
    skip
    -- We have an isomorphism in `Top`,
    let i_Top := as_iso ((forget₂ TopCommRingCat TopCat).map f)
    -- and a `ring_equiv`.
    let e_Ring : X ≃+* Y := { f.1, ((forget TopCat).mapIso i_Top).toEquiv with }
    -- Putting these together we obtain the isomorphism we're after:
    exact
      ⟨⟨⟨e_Ring.symm, i_Top.inv.2⟩,
          ⟨by
            ext x
            exact e_Ring.left_inv x, by
            ext x
            exact e_Ring.right_inv x⟩⟩⟩

end TopCommRingCat

