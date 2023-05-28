/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.adjunction.reflective
! leanprover-community/mathlib commit ee05e9ce1322178f0c12004eb93c00d2c8c00ed2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Adjunction.FullyFaithful
import Mathbin.CategoryTheory.Functor.ReflectsIsomorphisms
import Mathbin.CategoryTheory.EpiMono

/-!
# Reflective functors

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Basic properties of reflective functors, especially those relating to their essential image.

Note properties of reflective functors relating to limits and colimits are included in
`category_theory.monad.limits`.
-/


universe v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

open Category Adjunction

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}

variable [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]

#print CategoryTheory.Reflective /-
/--
A functor is *reflective*, or *a reflective inclusion*, if it is fully faithful and right adjoint.
-/
class Reflective (R : D ⥤ C) extends IsRightAdjoint R, Full R, Faithful R
#align category_theory.reflective CategoryTheory.Reflective
-/

variable {i : D ⥤ C}

/- warning: category_theory.unit_obj_eq_map_unit -> CategoryTheory.unit_obj_eq_map_unit is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.unit_obj_eq_map_unit CategoryTheory.unit_obj_eq_map_unitₓ'. -/
-- TODO: This holds more generally for idempotent adjunctions, not just reflective adjunctions.
/-- For a reflective functor `i` (with left adjoint `L`), with unit `η`, we have `η_iL = iL η`.
-/
theorem unit_obj_eq_map_unit [Reflective i] (X : C) :
    (ofRightAdjoint i).Unit.app (i.obj ((leftAdjoint i).obj X)) =
      i.map ((leftAdjoint i).map ((ofRightAdjoint i).Unit.app X)) :=
  by
  rw [← cancel_mono (i.map ((of_right_adjoint i).counit.app ((left_adjoint i).obj X))), ←
    i.map_comp]
  simp
#align category_theory.unit_obj_eq_map_unit CategoryTheory.unit_obj_eq_map_unit

/- warning: category_theory.is_iso_unit_obj -> CategoryTheory.isIso_unit_obj is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} {D : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u4} D] {i : CategoryTheory.Functor.{u2, u1, u4, u3} D _inst_2 C _inst_1} [_inst_4 : CategoryTheory.Reflective.{u1, u2, u3, u4} C D _inst_1 _inst_2 i] {B : D}, CategoryTheory.IsIso.{u1, u3} C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1) (CategoryTheory.Functor.obj.{u2, u1, u4, u3} D _inst_2 C _inst_1 i B)) (CategoryTheory.Functor.obj.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 (CategoryTheory.leftAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 i (CategoryTheory.Reflective.toIsRightAdjoint.{u1, u2, u3, u4} C D _inst_1 _inst_2 i _inst_4)) i) (CategoryTheory.Functor.obj.{u2, u1, u4, u3} D _inst_2 C _inst_1 i B)) (CategoryTheory.NatTrans.app.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1) (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 (CategoryTheory.leftAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 i (CategoryTheory.Reflective.toIsRightAdjoint.{u1, u2, u3, u4} C D _inst_1 _inst_2 i _inst_4)) i) (CategoryTheory.Adjunction.unit.{u1, u2, u3, u4} C _inst_1 D _inst_2 (CategoryTheory.leftAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 i (CategoryTheory.Reflective.toIsRightAdjoint.{u1, u2, u3, u4} C D _inst_1 _inst_2 i _inst_4)) i (CategoryTheory.Adjunction.ofRightAdjoint.{u2, u1, u4, u3} D _inst_2 C _inst_1 i (CategoryTheory.Reflective.toIsRightAdjoint.{u1, u2, u3, u4} C D _inst_1 _inst_2 i _inst_4))) (CategoryTheory.Functor.obj.{u2, u1, u4, u3} D _inst_2 C _inst_1 i B))
but is expected to have type
  forall {C : Type.{u3}} {D : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u4} D] {i : CategoryTheory.Functor.{u2, u1, u4, u3} D _inst_2 C _inst_1} [_inst_4 : CategoryTheory.Reflective.{u1, u2, u3, u4} C D _inst_1 _inst_2 i] {B : D}, CategoryTheory.IsIso.{u1, u3} C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u3, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1)) (Prefunctor.obj.{succ u2, succ u1, u4, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u4, u3} D _inst_2 C _inst_1 i) B)) (Prefunctor.obj.{succ u1, succ u1, u3, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 (CategoryTheory.leftAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 i (CategoryTheory.Reflective.toIsRightAdjoint.{u1, u2, u3, u4} C D _inst_1 _inst_2 i _inst_4)) i)) (Prefunctor.obj.{succ u2, succ u1, u4, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u4, u3} D _inst_2 C _inst_1 i) B)) (CategoryTheory.NatTrans.app.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1) (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 (CategoryTheory.leftAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 i (CategoryTheory.Reflective.toIsRightAdjoint.{u1, u2, u3, u4} C D _inst_1 _inst_2 i _inst_4)) i) (CategoryTheory.Adjunction.unit.{u1, u2, u3, u4} C _inst_1 D _inst_2 (CategoryTheory.leftAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 i (CategoryTheory.Reflective.toIsRightAdjoint.{u1, u2, u3, u4} C D _inst_1 _inst_2 i _inst_4)) i (CategoryTheory.Adjunction.ofRightAdjoint.{u2, u1, u4, u3} D _inst_2 C _inst_1 i (CategoryTheory.Reflective.toIsRightAdjoint.{u1, u2, u3, u4} C D _inst_1 _inst_2 i _inst_4))) (Prefunctor.obj.{succ u2, succ u1, u4, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u4, u3} D _inst_2 C _inst_1 i) B))
Case conversion may be inaccurate. Consider using '#align category_theory.is_iso_unit_obj CategoryTheory.isIso_unit_objₓ'. -/
/--
When restricted to objects in `D` given by `i : D ⥤ C`, the unit is an isomorphism. In other words,
`η_iX` is an isomorphism for any `X` in `D`.
More generally this applies to objects essentially in the reflective subcategory, see
`functor.ess_image.unit_iso`.
-/
instance isIso_unit_obj [Reflective i] {B : D} : IsIso ((ofRightAdjoint i).Unit.app (i.obj B)) :=
  by
  have :
    (of_right_adjoint i).Unit.app (i.obj B) = inv (i.map ((of_right_adjoint i).counit.app B)) :=
    by
    rw [← comp_hom_eq_id]
    apply (of_right_adjoint i).right_triangle_components
  rw [this]
  exact is_iso.inv_is_iso
#align category_theory.is_iso_unit_obj CategoryTheory.isIso_unit_obj

/- warning: category_theory.functor.ess_image.unit_is_iso -> CategoryTheory.Functor.essImage.unit_isIso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} {D : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u4} D] {i : CategoryTheory.Functor.{u2, u1, u4, u3} D _inst_2 C _inst_1} [_inst_4 : CategoryTheory.Reflective.{u1, u2, u3, u4} C D _inst_1 _inst_2 i] {A : C}, (Membership.Mem.{u3, u3} C (Set.{u3} C) (Set.hasMem.{u3} C) A (CategoryTheory.Functor.essImage.{u2, u1, u4, u3} D C _inst_2 _inst_1 i)) -> (CategoryTheory.IsIso.{u1, u3} C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1) A) (CategoryTheory.Functor.obj.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 (CategoryTheory.leftAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 i (CategoryTheory.Reflective.toIsRightAdjoint.{u1, u2, u3, u4} C D _inst_1 _inst_2 i _inst_4)) i) A) (CategoryTheory.NatTrans.app.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1) (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 (CategoryTheory.leftAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 i (CategoryTheory.Reflective.toIsRightAdjoint.{u1, u2, u3, u4} C D _inst_1 _inst_2 i _inst_4)) i) (CategoryTheory.Adjunction.unit.{u1, u2, u3, u4} C _inst_1 D _inst_2 (CategoryTheory.leftAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 i (CategoryTheory.Reflective.toIsRightAdjoint.{u1, u2, u3, u4} C D _inst_1 _inst_2 i _inst_4)) i (CategoryTheory.Adjunction.ofRightAdjoint.{u2, u1, u4, u3} D _inst_2 C _inst_1 i (CategoryTheory.Reflective.toIsRightAdjoint.{u1, u2, u3, u4} C D _inst_1 _inst_2 i _inst_4))) A))
but is expected to have type
  forall {C : Type.{u3}} {D : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u4} D] {i : CategoryTheory.Functor.{u2, u1, u4, u3} D _inst_2 C _inst_1} [_inst_4 : CategoryTheory.Reflective.{u1, u2, u3, u4} C D _inst_1 _inst_2 i] {A : C}, (Membership.mem.{u3, u3} C (Set.{u3} C) (Set.instMembershipSet.{u3} C) A (CategoryTheory.Functor.essImage.{u2, u1, u4, u3} D C _inst_2 _inst_1 i)) -> (CategoryTheory.IsIso.{u1, u3} C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u3, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1)) A) (Prefunctor.obj.{succ u1, succ u1, u3, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 (CategoryTheory.leftAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 i (CategoryTheory.Reflective.toIsRightAdjoint.{u1, u2, u3, u4} C D _inst_1 _inst_2 i _inst_4)) i)) A) (CategoryTheory.NatTrans.app.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1) (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 (CategoryTheory.leftAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 i (CategoryTheory.Reflective.toIsRightAdjoint.{u1, u2, u3, u4} C D _inst_1 _inst_2 i _inst_4)) i) (CategoryTheory.Adjunction.unit.{u1, u2, u3, u4} C _inst_1 D _inst_2 (CategoryTheory.leftAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 i (CategoryTheory.Reflective.toIsRightAdjoint.{u1, u2, u3, u4} C D _inst_1 _inst_2 i _inst_4)) i (CategoryTheory.Adjunction.ofRightAdjoint.{u2, u1, u4, u3} D _inst_2 C _inst_1 i (CategoryTheory.Reflective.toIsRightAdjoint.{u1, u2, u3, u4} C D _inst_1 _inst_2 i _inst_4))) A))
Case conversion may be inaccurate. Consider using '#align category_theory.functor.ess_image.unit_is_iso CategoryTheory.Functor.essImage.unit_isIsoₓ'. -/
/-- If `A` is essentially in the image of a reflective functor `i`, then `η_A` is an isomorphism.
This gives that the "witness" for `A` being in the essential image can instead be given as the
reflection of `A`, with the isomorphism as `η_A`.

(For any `B` in the reflective subcategory, we automatically have that `ε_B` is an iso.)
-/
theorem Functor.essImage.unit_isIso [Reflective i] {A : C} (h : A ∈ i.essImage) :
    IsIso ((ofRightAdjoint i).Unit.app A) :=
  by
  suffices
    (of_right_adjoint i).Unit.app A =
      h.get_iso.inv ≫
        (of_right_adjoint i).Unit.app (i.obj h.witness) ≫ (left_adjoint i ⋙ i).map h.get_iso.hom
    by
    rw [this]
    infer_instance
  rw [← nat_trans.naturality]
  simp
#align category_theory.functor.ess_image.unit_is_iso CategoryTheory.Functor.essImage.unit_isIso

/- warning: category_theory.mem_ess_image_of_unit_is_iso -> CategoryTheory.mem_essImage_of_unit_isIso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} {D : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u4} D] {i : CategoryTheory.Functor.{u2, u1, u4, u3} D _inst_2 C _inst_1} [_inst_4 : CategoryTheory.IsRightAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 i] (A : C) [_inst_5 : CategoryTheory.IsIso.{u1, u3} C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1) A) (CategoryTheory.Functor.obj.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 (CategoryTheory.leftAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 i _inst_4) i) A) (CategoryTheory.NatTrans.app.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1) (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 (CategoryTheory.leftAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 i _inst_4) i) (CategoryTheory.Adjunction.unit.{u1, u2, u3, u4} C _inst_1 D _inst_2 (CategoryTheory.leftAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 i _inst_4) i (CategoryTheory.Adjunction.ofRightAdjoint.{u2, u1, u4, u3} D _inst_2 C _inst_1 i _inst_4)) A)], Membership.Mem.{u3, u3} C (Set.{u3} C) (Set.hasMem.{u3} C) A (CategoryTheory.Functor.essImage.{u2, u1, u4, u3} D C _inst_2 _inst_1 i)
but is expected to have type
  forall {C : Type.{u3}} {D : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u4} D] {i : CategoryTheory.Functor.{u2, u1, u4, u3} D _inst_2 C _inst_1} [_inst_4 : CategoryTheory.IsRightAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 i] (A : C) [_inst_5 : CategoryTheory.IsIso.{u1, u3} C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u3, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1)) A) (Prefunctor.obj.{succ u1, succ u1, u3, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 (CategoryTheory.leftAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 i _inst_4) i)) A) (CategoryTheory.NatTrans.app.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1) (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 (CategoryTheory.leftAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 i _inst_4) i) (CategoryTheory.Adjunction.unit.{u1, u2, u3, u4} C _inst_1 D _inst_2 (CategoryTheory.leftAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 i _inst_4) i (CategoryTheory.Adjunction.ofRightAdjoint.{u2, u1, u4, u3} D _inst_2 C _inst_1 i _inst_4)) A)], Membership.mem.{u3, u3} C (Set.{u3} C) (Set.instMembershipSet.{u3} C) A (CategoryTheory.Functor.essImage.{u2, u1, u4, u3} D C _inst_2 _inst_1 i)
Case conversion may be inaccurate. Consider using '#align category_theory.mem_ess_image_of_unit_is_iso CategoryTheory.mem_essImage_of_unit_isIsoₓ'. -/
/-- If `η_A` is an isomorphism, then `A` is in the essential image of `i`. -/
theorem mem_essImage_of_unit_isIso [IsRightAdjoint i] (A : C)
    [IsIso ((ofRightAdjoint i).Unit.app A)] : A ∈ i.essImage :=
  ⟨(leftAdjoint i).obj A, ⟨(asIso ((ofRightAdjoint i).Unit.app A)).symm⟩⟩
#align category_theory.mem_ess_image_of_unit_is_iso CategoryTheory.mem_essImage_of_unit_isIso

/- warning: category_theory.mem_ess_image_of_unit_is_split_mono -> CategoryTheory.mem_essImage_of_unit_isSplitMono is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} {D : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u4} D] {i : CategoryTheory.Functor.{u2, u1, u4, u3} D _inst_2 C _inst_1} [_inst_4 : CategoryTheory.Reflective.{u1, u2, u3, u4} C D _inst_1 _inst_2 i] {A : C} [_inst_5 : CategoryTheory.IsSplitMono.{u1, u3} C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1) A) (CategoryTheory.Functor.obj.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 (CategoryTheory.leftAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 i (CategoryTheory.Reflective.toIsRightAdjoint.{u1, u2, u3, u4} C D _inst_1 _inst_2 i _inst_4)) i) A) (CategoryTheory.NatTrans.app.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1) (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 (CategoryTheory.leftAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 i (CategoryTheory.Reflective.toIsRightAdjoint.{u1, u2, u3, u4} C D _inst_1 _inst_2 i _inst_4)) i) (CategoryTheory.Adjunction.unit.{u1, u2, u3, u4} C _inst_1 D _inst_2 (CategoryTheory.leftAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 i (CategoryTheory.Reflective.toIsRightAdjoint.{u1, u2, u3, u4} C D _inst_1 _inst_2 i _inst_4)) i (CategoryTheory.Adjunction.ofRightAdjoint.{u2, u1, u4, u3} D _inst_2 C _inst_1 i (CategoryTheory.Reflective.toIsRightAdjoint.{u1, u2, u3, u4} C D _inst_1 _inst_2 i _inst_4))) A)], Membership.Mem.{u3, u3} C (Set.{u3} C) (Set.hasMem.{u3} C) A (CategoryTheory.Functor.essImage.{u2, u1, u4, u3} D C _inst_2 _inst_1 i)
but is expected to have type
  forall {C : Type.{u3}} {D : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u4} D] {i : CategoryTheory.Functor.{u2, u1, u4, u3} D _inst_2 C _inst_1} [_inst_4 : CategoryTheory.Reflective.{u1, u2, u3, u4} C D _inst_1 _inst_2 i] {A : C} [_inst_5 : CategoryTheory.IsSplitMono.{u1, u3} C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u3, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1)) A) (Prefunctor.obj.{succ u1, succ u1, u3, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 (CategoryTheory.leftAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 i (CategoryTheory.Reflective.toIsRightAdjoint.{u1, u2, u3, u4} C D _inst_1 _inst_2 i _inst_4)) i)) A) (CategoryTheory.NatTrans.app.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1) (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 (CategoryTheory.leftAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 i (CategoryTheory.Reflective.toIsRightAdjoint.{u1, u2, u3, u4} C D _inst_1 _inst_2 i _inst_4)) i) (CategoryTheory.Adjunction.unit.{u1, u2, u3, u4} C _inst_1 D _inst_2 (CategoryTheory.leftAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 i (CategoryTheory.Reflective.toIsRightAdjoint.{u1, u2, u3, u4} C D _inst_1 _inst_2 i _inst_4)) i (CategoryTheory.Adjunction.ofRightAdjoint.{u2, u1, u4, u3} D _inst_2 C _inst_1 i (CategoryTheory.Reflective.toIsRightAdjoint.{u1, u2, u3, u4} C D _inst_1 _inst_2 i _inst_4))) A)], Membership.mem.{u3, u3} C (Set.{u3} C) (Set.instMembershipSet.{u3} C) A (CategoryTheory.Functor.essImage.{u2, u1, u4, u3} D C _inst_2 _inst_1 i)
Case conversion may be inaccurate. Consider using '#align category_theory.mem_ess_image_of_unit_is_split_mono CategoryTheory.mem_essImage_of_unit_isSplitMonoₓ'. -/
/-- If `η_A` is a split monomorphism, then `A` is in the reflective subcategory. -/
theorem mem_essImage_of_unit_isSplitMono [Reflective i] {A : C}
    [IsSplitMono ((ofRightAdjoint i).Unit.app A)] : A ∈ i.essImage :=
  by
  let η : 𝟭 C ⟶ left_adjoint i ⋙ i := (of_right_adjoint i).Unit
  haveI : is_iso (η.app (i.obj ((left_adjoint i).obj A))) := (i.obj_mem_ess_image _).unit_isIso
  have : epi (η.app A) := by
    apply epi_of_epi (retraction (η.app A)) _
    rw [show retraction _ ≫ η.app A = _ from η.naturality (retraction (η.app A))]
    apply epi_comp (η.app (i.obj ((left_adjoint i).obj A)))
  skip
  haveI := is_iso_of_epi_of_is_split_mono (η.app A)
  exact mem_ess_image_of_unit_is_iso A
#align category_theory.mem_ess_image_of_unit_is_split_mono CategoryTheory.mem_essImage_of_unit_isSplitMono

#print CategoryTheory.Reflective.comp /-
/-- Composition of reflective functors. -/
instance Reflective.comp (F : C ⥤ D) (G : D ⥤ E) [Fr : Reflective F] [Gr : Reflective G] :
    Reflective (F ⋙ G) where to_faithful := Faithful.comp F G
#align category_theory.reflective.comp CategoryTheory.Reflective.comp
-/

/- warning: category_theory.unit_comp_partial_bijective_aux -> CategoryTheory.unitCompPartialBijectiveAux is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} {D : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u4} D] {i : CategoryTheory.Functor.{u2, u1, u4, u3} D _inst_2 C _inst_1} [_inst_4 : CategoryTheory.Reflective.{u1, u2, u3, u4} C D _inst_1 _inst_2 i] (A : C) (B : D), Equiv.{succ u1, succ u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) A (CategoryTheory.Functor.obj.{u2, u1, u4, u3} D _inst_2 C _inst_1 i B)) (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.obj.{u2, u1, u4, u3} D _inst_2 C _inst_1 i (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 (CategoryTheory.leftAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 i (CategoryTheory.Reflective.toIsRightAdjoint.{u1, u2, u3, u4} C D _inst_1 _inst_2 i _inst_4)) A)) (CategoryTheory.Functor.obj.{u2, u1, u4, u3} D _inst_2 C _inst_1 i B))
but is expected to have type
  forall {C : Type.{u3}} {D : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u4} D] {i : CategoryTheory.Functor.{u2, u1, u4, u3} D _inst_2 C _inst_1} [_inst_4 : CategoryTheory.Reflective.{u1, u2, u3, u4} C D _inst_1 _inst_2 i] (A : C) (B : D), Equiv.{succ u1, succ u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) A (Prefunctor.obj.{succ u2, succ u1, u4, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u4, u3} D _inst_2 C _inst_1 i) B)) (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (Prefunctor.obj.{succ u2, succ u1, u4, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u4, u3} D _inst_2 C _inst_1 i) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 (CategoryTheory.leftAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 i (CategoryTheory.Reflective.toIsRightAdjoint.{u1, u2, u3, u4} C D _inst_1 _inst_2 i _inst_4))) A)) (Prefunctor.obj.{succ u2, succ u1, u4, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u4, u3} D _inst_2 C _inst_1 i) B))
Case conversion may be inaccurate. Consider using '#align category_theory.unit_comp_partial_bijective_aux CategoryTheory.unitCompPartialBijectiveAuxₓ'. -/
/-- (Implementation) Auxiliary definition for `unit_comp_partial_bijective`. -/
def unitCompPartialBijectiveAux [Reflective i] (A : C) (B : D) :
    (A ⟶ i.obj B) ≃ (i.obj ((leftAdjoint i).obj A) ⟶ i.obj B) :=
  ((Adjunction.ofRightAdjoint i).homEquiv _ _).symm.trans (equivOfFullyFaithful i)
#align category_theory.unit_comp_partial_bijective_aux CategoryTheory.unitCompPartialBijectiveAux

/- warning: category_theory.unit_comp_partial_bijective_aux_symm_apply -> CategoryTheory.unitCompPartialBijectiveAux_symm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.unit_comp_partial_bijective_aux_symm_apply CategoryTheory.unitCompPartialBijectiveAux_symm_applyₓ'. -/
/-- The description of the inverse of the bijection `unit_comp_partial_bijective_aux`. -/
theorem unitCompPartialBijectiveAux_symm_apply [Reflective i] {A : C} {B : D}
    (f : i.obj ((leftAdjoint i).obj A) ⟶ i.obj B) :
    (unitCompPartialBijectiveAux _ _).symm f = (ofRightAdjoint i).Unit.app A ≫ f := by
  simp [unit_comp_partial_bijective_aux]
#align category_theory.unit_comp_partial_bijective_aux_symm_apply CategoryTheory.unitCompPartialBijectiveAux_symm_apply

/- warning: category_theory.unit_comp_partial_bijective -> CategoryTheory.unitCompPartialBijective is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} {D : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u4} D] {i : CategoryTheory.Functor.{u2, u1, u4, u3} D _inst_2 C _inst_1} [_inst_4 : CategoryTheory.Reflective.{u1, u2, u3, u4} C D _inst_1 _inst_2 i] (A : C) {B : C}, (Membership.Mem.{u3, u3} C (Set.{u3} C) (Set.hasMem.{u3} C) B (CategoryTheory.Functor.essImage.{u2, u1, u4, u3} D C _inst_2 _inst_1 i)) -> (Equiv.{succ u1, succ u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) A B) (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.obj.{u2, u1, u4, u3} D _inst_2 C _inst_1 i (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 (CategoryTheory.leftAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 i (CategoryTheory.Reflective.toIsRightAdjoint.{u1, u2, u3, u4} C D _inst_1 _inst_2 i _inst_4)) A)) B))
but is expected to have type
  forall {C : Type.{u3}} {D : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u4} D] {i : CategoryTheory.Functor.{u2, u1, u4, u3} D _inst_2 C _inst_1} [_inst_4 : CategoryTheory.Reflective.{u1, u2, u3, u4} C D _inst_1 _inst_2 i] (A : C) {B : C}, (Membership.mem.{u3, u3} C (Set.{u3} C) (Set.instMembershipSet.{u3} C) B (CategoryTheory.Functor.essImage.{u2, u1, u4, u3} D C _inst_2 _inst_1 i)) -> (Equiv.{succ u1, succ u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) A B) (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (Prefunctor.obj.{succ u2, succ u1, u4, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u4, u3} D _inst_2 C _inst_1 i) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 (CategoryTheory.leftAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 i (CategoryTheory.Reflective.toIsRightAdjoint.{u1, u2, u3, u4} C D _inst_1 _inst_2 i _inst_4))) A)) B))
Case conversion may be inaccurate. Consider using '#align category_theory.unit_comp_partial_bijective CategoryTheory.unitCompPartialBijectiveₓ'. -/
/-- If `i` has a reflector `L`, then the function `(i.obj (L.obj A) ⟶ B) → (A ⟶ B)` given by
precomposing with `η.app A` is a bijection provided `B` is in the essential image of `i`.
That is, the function `λ (f : i.obj (L.obj A) ⟶ B), η.app A ≫ f` is bijective, as long as `B` is in
the essential image of `i`.
This definition gives an equivalence: the key property that the inverse can be described
nicely is shown in `unit_comp_partial_bijective_symm_apply`.

This establishes there is a natural bijection `(A ⟶ B) ≃ (i.obj (L.obj A) ⟶ B)`. In other words,
from the point of view of objects in `D`, `A` and `i.obj (L.obj A)` look the same: specifically
that `η.app A` is an isomorphism.
-/
def unitCompPartialBijective [Reflective i] (A : C) {B : C} (hB : B ∈ i.essImage) :
    (A ⟶ B) ≃ (i.obj ((leftAdjoint i).obj A) ⟶ B) :=
  calc
    (A ⟶ B) ≃ (A ⟶ i.obj hB.witness) := Iso.homCongr (Iso.refl _) hB.getIso.symm
    _ ≃ (i.obj _ ⟶ i.obj hB.witness) := (unitCompPartialBijectiveAux _ _)
    _ ≃ (i.obj ((leftAdjoint i).obj A) ⟶ B) := Iso.homCongr (Iso.refl _) hB.getIso
    
#align category_theory.unit_comp_partial_bijective CategoryTheory.unitCompPartialBijective

/- warning: category_theory.unit_comp_partial_bijective_symm_apply -> CategoryTheory.unitCompPartialBijective_symm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.unit_comp_partial_bijective_symm_apply CategoryTheory.unitCompPartialBijective_symm_applyₓ'. -/
@[simp]
theorem unitCompPartialBijective_symm_apply [Reflective i] (A : C) {B : C} (hB : B ∈ i.essImage)
    (f) : (unitCompPartialBijective A hB).symm f = (ofRightAdjoint i).Unit.app A ≫ f := by
  simp [unit_comp_partial_bijective, unit_comp_partial_bijective_aux_symm_apply]
#align category_theory.unit_comp_partial_bijective_symm_apply CategoryTheory.unitCompPartialBijective_symm_apply

/- warning: category_theory.unit_comp_partial_bijective_symm_natural -> CategoryTheory.unitCompPartialBijective_symm_natural is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.unit_comp_partial_bijective_symm_natural CategoryTheory.unitCompPartialBijective_symm_naturalₓ'. -/
theorem unitCompPartialBijective_symm_natural [Reflective i] (A : C) {B B' : C} (h : B ⟶ B')
    (hB : B ∈ i.essImage) (hB' : B' ∈ i.essImage) (f : i.obj ((leftAdjoint i).obj A) ⟶ B) :
    (unitCompPartialBijective A hB').symm (f ≫ h) = (unitCompPartialBijective A hB).symm f ≫ h := by
  simp
#align category_theory.unit_comp_partial_bijective_symm_natural CategoryTheory.unitCompPartialBijective_symm_natural

/- warning: category_theory.unit_comp_partial_bijective_natural -> CategoryTheory.unitCompPartialBijective_natural is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.unit_comp_partial_bijective_natural CategoryTheory.unitCompPartialBijective_naturalₓ'. -/
theorem unitCompPartialBijective_natural [Reflective i] (A : C) {B B' : C} (h : B ⟶ B')
    (hB : B ∈ i.essImage) (hB' : B' ∈ i.essImage) (f : A ⟶ B) :
    (unitCompPartialBijective A hB') (f ≫ h) = unitCompPartialBijective A hB f ≫ h := by
  rw [← Equiv.eq_symm_apply, unit_comp_partial_bijective_symm_natural A h, Equiv.symm_apply_apply]
#align category_theory.unit_comp_partial_bijective_natural CategoryTheory.unitCompPartialBijective_natural

/- warning: category_theory.equiv_ess_image_of_reflective -> CategoryTheory.equivEssImageOfReflective is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} {D : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u4} D] {i : CategoryTheory.Functor.{u2, u1, u4, u3} D _inst_2 C _inst_1} [_inst_4 : CategoryTheory.Reflective.{u1, u2, u3, u4} C D _inst_1 _inst_2 i], CategoryTheory.Equivalence.{u2, u1, u4, u3} D _inst_2 (CategoryTheory.Functor.EssImageSubcategory.{u2, u1, u4, u3} D C _inst_2 _inst_1 i) (CategoryTheory.Functor.EssImageSubcategory.category.{u1, u3, u4, u2} D C _inst_2 _inst_1 i)
but is expected to have type
  forall {C : Type.{u3}} {D : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.Category.{u2, u4} D] {i : CategoryTheory.Functor.{u2, u1, u4, u3} D _inst_2 C _inst_1} [_inst_4 : CategoryTheory.Reflective.{u1, u2, u3, u4} C D _inst_1 _inst_2 i], CategoryTheory.Equivalence.{u2, u1, u4, u3} D (CategoryTheory.Functor.EssImageSubcategory.{u2, u1, u4, u3} D C _inst_2 _inst_1 i) _inst_2 (CategoryTheory.Functor.instCategoryEssImageSubcategory.{u2, u1, u4, u3} D C _inst_2 _inst_1 i)
Case conversion may be inaccurate. Consider using '#align category_theory.equiv_ess_image_of_reflective CategoryTheory.equivEssImageOfReflectiveₓ'. -/
/-- If `i : D ⥤ C` is reflective, the inverse functor of `i ≌ F.ess_image` can be explicitly
defined by the reflector. -/
@[simps]
def equivEssImageOfReflective [Reflective i] : D ≌ i.EssImageSubcategory
    where
  Functor := i.toEssImage
  inverse := i.essImageInclusion ⋙ (leftAdjoint i : _)
  unitIso :=
    NatIso.ofComponents (fun X => (asIso <| (ofRightAdjoint i).counit.app X).symm)
      (by
        intro X Y f; dsimp; simp only [is_iso.eq_inv_comp, is_iso.comp_inv_eq, category.assoc]
        exact ((of_right_adjoint i).counit.naturality _).symm)
  counitIso :=
    NatIso.ofComponents
      (fun X => by
        refine' iso.symm <| as_iso _; exact (of_right_adjoint i).Unit.app X.obj
        apply (config := { instances := false }) is_iso_of_reflects_iso _ i.ess_image_inclusion
        exact functor.ess_image.unit_is_iso X.property)
      (by
        intro X Y f; dsimp; rw [is_iso.comp_inv_eq, assoc]
        have h := ((of_right_adjoint i).Unit.naturality f).symm
        rw [functor.id_map] at h; erw [← h, is_iso.inv_hom_id_assoc, functor.comp_map])
#align category_theory.equiv_ess_image_of_reflective CategoryTheory.equivEssImageOfReflective

end CategoryTheory

