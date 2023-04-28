/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.noetherian
! leanprover-community/mathlib commit 7c4c90f422a4a4477e4d8bc4dc9f1e634e6b2349
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Subobject.Lattice
import Mathbin.CategoryTheory.EssentiallySmall
import Mathbin.CategoryTheory.Simple

/-!
# Artinian and noetherian categories

An artinian category is a category in which objects do not
have infinite decreasing sequences of subobjects.

A noetherian category is a category in which objects do not
have infinite increasing sequences of subobjects.

We show that any nonzero artinian object has a simple subobject.

## Future work
The Jordan-Hölder theorem, following https://stacks.math.columbia.edu/tag/0FCK.
-/


namespace CategoryTheory

open CategoryTheory.Limits

variable {C : Type _} [Category C]

#print CategoryTheory.NoetherianObject /-
/-- A noetherian object is an object
which does not have infinite increasing sequences of subobjects.

See https://stacks.math.columbia.edu/tag/0FCG
-/
class NoetherianObject (X : C) : Prop where
  subobject_gt_wellFounded : WellFounded ((· > ·) : Subobject X → Subobject X → Prop)
#align category_theory.noetherian_object CategoryTheory.NoetherianObject
-/

#print CategoryTheory.ArtinianObject /-
/- ./././Mathport/Syntax/Translate/Command.lean:393:30: infer kinds are unsupported in Lean 4: #[`subobject_lt_wellFounded] [] -/
/-- An artinian object is an object
which does not have infinite decreasing sequences of subobjects.

See https://stacks.math.columbia.edu/tag/0FCF
-/
class ArtinianObject (X : C) : Prop where
  subobject_lt_wellFounded : WellFounded ((· < ·) : Subobject X → Subobject X → Prop)
#align category_theory.artinian_object CategoryTheory.ArtinianObject
-/

variable (C)

#print CategoryTheory.Noetherian /-
/-- A category is noetherian if it is essentially small and all objects are noetherian. -/
class Noetherian extends EssentiallySmall C where
  NoetherianObject : ∀ X : C, NoetherianObject X
#align category_theory.noetherian CategoryTheory.Noetherian
-/

attribute [instance] noetherian.noetherian_object

#print CategoryTheory.Artinian /-
/-- A category is artinian if it is essentially small and all objects are artinian. -/
class Artinian extends EssentiallySmall C where
  ArtinianObject : ∀ X : C, ArtinianObject X
#align category_theory.artinian CategoryTheory.Artinian
-/

attribute [instance] artinian.artinian_object

variable {C}

open Subobject

variable [HasZeroMorphisms C] [HasZeroObject C]

/- warning: category_theory.exists_simple_subobject -> CategoryTheory.exists_simple_subobject is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u2, u1} C _inst_1] [_inst_3 : CategoryTheory.Limits.HasZeroObject.{u2, u1} C _inst_1] {X : C} [_inst_4 : CategoryTheory.ArtinianObject.{u1, u2} C _inst_1 X], (Not (CategoryTheory.Limits.IsZero.{u2, u1} C _inst_1 X)) -> (Exists.{succ (max u1 u2)} (CategoryTheory.Subobject.{u2, u1} C _inst_1 X) (fun (Y : CategoryTheory.Subobject.{u2, u1} C _inst_1 X) => CategoryTheory.Simple.{u2, u1} C _inst_1 _inst_2 ((fun (a : Type.{max u1 u2}) (b : Type.{u1}) [self : HasLiftT.{succ (max u1 u2), succ u1} a b] => self.0) (CategoryTheory.Subobject.{u2, u1} C _inst_1 X) C (HasLiftT.mk.{succ (max u1 u2), succ u1} (CategoryTheory.Subobject.{u2, u1} C _inst_1 X) C (CoeTCₓ.coe.{succ (max u1 u2), succ u1} (CategoryTheory.Subobject.{u2, u1} C _inst_1 X) C (coeBase.{succ (max u1 u2), succ u1} (CategoryTheory.Subobject.{u2, u1} C _inst_1 X) C (CategoryTheory.Subobject.hasCoe.{u2, u1} C _inst_1 X)))) Y)))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} C _inst_1] [_inst_3 : CategoryTheory.Limits.HasZeroObject.{u1, u2} C _inst_1] {X : C} [_inst_4 : CategoryTheory.ArtinianObject.{u2, u1} C _inst_1 X], (Not (CategoryTheory.Limits.IsZero.{u1, u2} C _inst_1 X)) -> (Exists.{max (succ u2) (succ u1)} (CategoryTheory.Subobject.{u1, u2} C _inst_1 X) (fun (Y : CategoryTheory.Subobject.{u1, u2} C _inst_1 X) => CategoryTheory.Simple.{u1, u2} C _inst_1 _inst_2 (Prefunctor.obj.{max (succ u2) (succ u1), succ u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} C _inst_1 X) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} C _inst_1 X) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Subobject.{u1, u2} C _inst_1 X) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} C _inst_1 X) (CategoryTheory.instPartialOrderSubobject.{u1, u2} C _inst_1 X))))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{max u2 u1, u1, max u2 u1, u2} (CategoryTheory.Subobject.{u1, u2} C _inst_1 X) (Preorder.smallCategory.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Subobject.{u1, u2} C _inst_1 X) (CategoryTheory.instPartialOrderSubobject.{u1, u2} C _inst_1 X))) C _inst_1 (CategoryTheory.Subobject.underlying.{u1, u2} C _inst_1 X)) Y)))
Case conversion may be inaccurate. Consider using '#align category_theory.exists_simple_subobject CategoryTheory.exists_simple_subobjectₓ'. -/
theorem exists_simple_subobject {X : C} [ArtinianObject X] (h : ¬IsZero X) :
    ∃ Y : Subobject X, Simple (Y : C) :=
  by
  haveI : Nontrivial (subobject X) := nontrivial_of_not_is_zero h
  haveI := isAtomic_of_orderBot_wellFounded_lt (artinian_object.subobject_lt_well_founded X)
  have := IsAtomic.eq_bot_or_exists_atom_le (⊤ : subobject X)
  obtain ⟨Y, s⟩ := (IsAtomic.eq_bot_or_exists_atom_le (⊤ : subobject X)).resolve_left top_ne_bot
  exact ⟨Y, (subobject_simple_iff_is_atom _).mpr s.1⟩
#align category_theory.exists_simple_subobject CategoryTheory.exists_simple_subobject

#print CategoryTheory.simpleSubobject /-
/-- Choose an arbitrary simple subobject of a non-zero artinian object. -/
noncomputable def simpleSubobject {X : C} [ArtinianObject X] (h : ¬IsZero X) : C :=
  (exists_simple_subobject h).some
#align category_theory.simple_subobject CategoryTheory.simpleSubobject
-/

#print CategoryTheory.simpleSubobjectArrow /-
/-- The monomorphism from the arbitrary simple subobject of a non-zero artinian object. -/
noncomputable def simpleSubobjectArrow {X : C} [ArtinianObject X] (h : ¬IsZero X) :
    simpleSubobject h ⟶ X :=
  (exists_simple_subobject h).some.arrow deriving Mono
#align category_theory.simple_subobject_arrow CategoryTheory.simpleSubobjectArrow
-/

instance {X : C} [ArtinianObject X] (h : ¬IsZero X) : Simple (simpleSubobject h) :=
  (exists_simple_subobject h).choose_spec

end CategoryTheory

