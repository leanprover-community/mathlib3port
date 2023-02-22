/-
Copyright (c) 2021 Jakob Scholbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scholbach, Joël Riou

! This file was ported from Lean 3 source module category_theory.lifting_properties.basic
! leanprover-community/mathlib commit 093c5036c7d80f381c16b74813d4ca1d4c3d7c64
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.CommSq

/-!
# Lifting properties

This file defines the lifting property of two morphisms in a category and
shows basic properties of this notion.

## Main results
- `has_lifting_property`: the definition of the lifting property

## Tags
lifting property

@TODO :
1) define llp/rlp with respect to a `morphism_property`
2) retracts, direct/inverse images, (co)products, adjunctions

-/


universe v

namespace CategoryTheory

open Category

variable {C : Type _} [Category C] {A B B' X Y Y' : C} (i : A ⟶ B) (i' : B ⟶ B') (p : X ⟶ Y)
  (p' : Y ⟶ Y')

#print CategoryTheory.HasLiftingProperty /-
/-- `has_lifting_property i p` means that `i` has the left lifting
property with respect to `p`, or equivalently that `p` has
the right lifting property with respect to `i`. -/
class HasLiftingProperty : Prop where
  sq_hasLift : ∀ {f : A ⟶ X} {g : B ⟶ Y} (sq : CommSq f i p g), sq.HasLift
#align category_theory.has_lifting_property CategoryTheory.HasLiftingProperty
-/

#print CategoryTheory.sq_hasLift_of_hasLiftingProperty /-
instance (priority := 100) sq_hasLift_of_hasLiftingProperty {f : A ⟶ X} {g : B ⟶ Y}
    (sq : CommSq f i p g) [hip : HasLiftingProperty i p] : sq.HasLift := by apply hip.sq_has_lift
#align category_theory.sq_has_lift_of_has_lifting_property CategoryTheory.sq_hasLift_of_hasLiftingProperty
-/

namespace HasLiftingProperty

variable {i p}

/- warning: category_theory.has_lifting_property.op -> CategoryTheory.HasLiftingProperty.op is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] {A : C} {B : C} {X : C} {Y : C} {i : Quiver.Hom.{succ u2, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) A B} {p : Quiver.Hom.{succ u2, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) X Y}, (CategoryTheory.HasLiftingProperty.{u1, u2} C _inst_1 A B X Y i p) -> (CategoryTheory.HasLiftingProperty.{u1, u2} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) (Opposite.op.{succ u1} C Y) (Opposite.op.{succ u1} C X) (Opposite.op.{succ u1} C B) (Opposite.op.{succ u1} C A) (Quiver.Hom.op.{u1, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) X Y p) (Quiver.Hom.op.{u1, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) A B i))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {A : C} {B : C} {X : C} {Y : C} {i : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) A B} {p : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y}, (CategoryTheory.HasLiftingProperty.{u2, u1} C _inst_1 A B X Y i p) -> (CategoryTheory.HasLiftingProperty.{u2, u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (Opposite.op.{succ u2} C Y) (Opposite.op.{succ u2} C X) (Opposite.op.{succ u2} C B) (Opposite.op.{succ u2} C A) (Quiver.Hom.op.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y p) (Quiver.Hom.op.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) A B i))
Case conversion may be inaccurate. Consider using '#align category_theory.has_lifting_property.op CategoryTheory.HasLiftingProperty.opₓ'. -/
theorem op (h : HasLiftingProperty i p) : HasLiftingProperty p.op i.op :=
  ⟨fun f g sq => by
    simp only [comm_sq.has_lift.iff_unop, Quiver.Hom.unop_op]
    infer_instance⟩
#align category_theory.has_lifting_property.op CategoryTheory.HasLiftingProperty.op

/- warning: category_theory.has_lifting_property.unop -> CategoryTheory.HasLiftingProperty.unop is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] {A : Opposite.{succ u1} C} {B : Opposite.{succ u1} C} {X : Opposite.{succ u1} C} {Y : Opposite.{succ u1} C} {i : Quiver.Hom.{succ u2, u1} (Opposite.{succ u1} C) (Quiver.opposite.{u1, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1))) A B} {p : Quiver.Hom.{succ u2, u1} (Opposite.{succ u1} C) (Quiver.opposite.{u1, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1))) X Y}, (CategoryTheory.HasLiftingProperty.{u1, u2} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) A B X Y i p) -> (CategoryTheory.HasLiftingProperty.{u1, u2} C _inst_1 (Opposite.unop.{succ u1} C Y) (Opposite.unop.{succ u1} C X) (Opposite.unop.{succ u1} C B) (Opposite.unop.{succ u1} C A) (Quiver.Hom.unop.{u1, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) X Y p) (Quiver.Hom.unop.{u1, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) A B i))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {A : Opposite.{succ u2} C} {B : Opposite.{succ u2} C} {X : Opposite.{succ u2} C} {Y : Opposite.{succ u2} C} {i : Quiver.Hom.{succ u1, u2} (Opposite.{succ u2} C) (Quiver.opposite.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1))) A B} {p : Quiver.Hom.{succ u1, u2} (Opposite.{succ u2} C) (Quiver.opposite.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1))) X Y}, (CategoryTheory.HasLiftingProperty.{u2, u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) A B X Y i p) -> (CategoryTheory.HasLiftingProperty.{u2, u1} C _inst_1 (Opposite.unop.{succ u2} C Y) (Opposite.unop.{succ u2} C X) (Opposite.unop.{succ u2} C B) (Opposite.unop.{succ u2} C A) (Quiver.Hom.unop.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y p) (Quiver.Hom.unop.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) A B i))
Case conversion may be inaccurate. Consider using '#align category_theory.has_lifting_property.unop CategoryTheory.HasLiftingProperty.unopₓ'. -/
theorem unop {A B X Y : Cᵒᵖ} {i : A ⟶ B} {p : X ⟶ Y} (h : HasLiftingProperty i p) :
    HasLiftingProperty p.unop i.unop :=
  ⟨fun f g sq => by
    rw [comm_sq.has_lift.iff_op]
    simp only [Quiver.Hom.op_unop]
    infer_instance⟩
#align category_theory.has_lifting_property.unop CategoryTheory.HasLiftingProperty.unop

/- warning: category_theory.has_lifting_property.iff_op -> CategoryTheory.HasLiftingProperty.iff_op is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] {A : C} {B : C} {X : C} {Y : C} {i : Quiver.Hom.{succ u2, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) A B} {p : Quiver.Hom.{succ u2, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) X Y}, Iff (CategoryTheory.HasLiftingProperty.{u1, u2} C _inst_1 A B X Y i p) (CategoryTheory.HasLiftingProperty.{u1, u2} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) (Opposite.op.{succ u1} C Y) (Opposite.op.{succ u1} C X) (Opposite.op.{succ u1} C B) (Opposite.op.{succ u1} C A) (Quiver.Hom.op.{u1, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) X Y p) (Quiver.Hom.op.{u1, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) A B i))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {A : C} {B : C} {X : C} {Y : C} {i : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) A B} {p : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y}, Iff (CategoryTheory.HasLiftingProperty.{u2, u1} C _inst_1 A B X Y i p) (CategoryTheory.HasLiftingProperty.{u2, u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (Opposite.op.{succ u2} C Y) (Opposite.op.{succ u2} C X) (Opposite.op.{succ u2} C B) (Opposite.op.{succ u2} C A) (Quiver.Hom.op.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y p) (Quiver.Hom.op.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) A B i))
Case conversion may be inaccurate. Consider using '#align category_theory.has_lifting_property.iff_op CategoryTheory.HasLiftingProperty.iff_opₓ'. -/
theorem iff_op : HasLiftingProperty i p ↔ HasLiftingProperty p.op i.op :=
  ⟨op, unop⟩
#align category_theory.has_lifting_property.iff_op CategoryTheory.HasLiftingProperty.iff_op

/- warning: category_theory.has_lifting_property.iff_unop -> CategoryTheory.HasLiftingProperty.iff_unop is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] {A : Opposite.{succ u1} C} {B : Opposite.{succ u1} C} {X : Opposite.{succ u1} C} {Y : Opposite.{succ u1} C} (i : Quiver.Hom.{succ u2, u1} (Opposite.{succ u1} C) (Quiver.opposite.{u1, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1))) A B) (p : Quiver.Hom.{succ u2, u1} (Opposite.{succ u1} C) (Quiver.opposite.{u1, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1))) X Y), Iff (CategoryTheory.HasLiftingProperty.{u1, u2} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u2, u1} C _inst_1) A B X Y i p) (CategoryTheory.HasLiftingProperty.{u1, u2} C _inst_1 (Opposite.unop.{succ u1} C Y) (Opposite.unop.{succ u1} C X) (Opposite.unop.{succ u1} C B) (Opposite.unop.{succ u1} C A) (Quiver.Hom.unop.{u1, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) X Y p) (Quiver.Hom.unop.{u1, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) A B i))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {A : Opposite.{succ u2} C} {B : Opposite.{succ u2} C} {X : Opposite.{succ u2} C} {Y : Opposite.{succ u2} C} (i : Quiver.Hom.{succ u1, u2} (Opposite.{succ u2} C) (Quiver.opposite.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1))) A B) (p : Quiver.Hom.{succ u1, u2} (Opposite.{succ u2} C) (Quiver.opposite.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1))) X Y), Iff (CategoryTheory.HasLiftingProperty.{u2, u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) A B X Y i p) (CategoryTheory.HasLiftingProperty.{u2, u1} C _inst_1 (Opposite.unop.{succ u2} C Y) (Opposite.unop.{succ u2} C X) (Opposite.unop.{succ u2} C B) (Opposite.unop.{succ u2} C A) (Quiver.Hom.unop.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y p) (Quiver.Hom.unop.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) A B i))
Case conversion may be inaccurate. Consider using '#align category_theory.has_lifting_property.iff_unop CategoryTheory.HasLiftingProperty.iff_unopₓ'. -/
theorem iff_unop {A B X Y : Cᵒᵖ} (i : A ⟶ B) (p : X ⟶ Y) :
    HasLiftingProperty i p ↔ HasLiftingProperty p.unop i.unop :=
  ⟨unop, op⟩
#align category_theory.has_lifting_property.iff_unop CategoryTheory.HasLiftingProperty.iff_unop

variable (i p)

#print CategoryTheory.HasLiftingProperty.of_left_iso /-
instance (priority := 100) of_left_iso [IsIso i] : HasLiftingProperty i p :=
  ⟨fun f g sq =>
    CommSq.HasLift.mk'
      { l := inv i ≫ f
        fac_left' := by simp only [is_iso.hom_inv_id_assoc]
        fac_right' := by simp only [sq.w, assoc, is_iso.inv_hom_id_assoc] }⟩
#align category_theory.has_lifting_property.of_left_iso CategoryTheory.HasLiftingProperty.of_left_iso
-/

#print CategoryTheory.HasLiftingProperty.of_right_iso /-
instance (priority := 100) of_right_iso [IsIso p] : HasLiftingProperty i p :=
  ⟨fun f g sq =>
    CommSq.HasLift.mk'
      { l := g ≫ inv p
        fac_left' := by simp only [← sq.w_assoc, is_iso.hom_inv_id, comp_id]
        fac_right' := by simp only [assoc, is_iso.inv_hom_id, comp_id] }⟩
#align category_theory.has_lifting_property.of_right_iso CategoryTheory.HasLiftingProperty.of_right_iso
-/

#print CategoryTheory.HasLiftingProperty.of_comp_left /-
instance of_comp_left [HasLiftingProperty i p] [HasLiftingProperty i' p] :
    HasLiftingProperty (i ≫ i') p :=
  ⟨fun f g sq => by
    have fac := sq.w
    rw [assoc] at fac
    exact
      comm_sq.has_lift.mk'
        { l := (comm_sq.mk (comm_sq.mk fac).fac_right).lift
          fac_left' := by simp only [assoc, comm_sq.fac_left]
          fac_right' := by simp only [comm_sq.fac_right] }⟩
#align category_theory.has_lifting_property.of_comp_left CategoryTheory.HasLiftingProperty.of_comp_left
-/

#print CategoryTheory.HasLiftingProperty.of_comp_right /-
instance of_comp_right [HasLiftingProperty i p] [HasLiftingProperty i p'] :
    HasLiftingProperty i (p ≫ p') :=
  ⟨fun f g sq => by
    have fac := sq.w
    rw [← assoc] at fac
    let sq₂ := (comm_sq.mk (comm_sq.mk fac).fac_left.symm).lift
    exact
      comm_sq.has_lift.mk'
        { l := (comm_sq.mk (comm_sq.mk fac).fac_left.symm).lift
          fac_left' := by simp only [comm_sq.fac_left]
          fac_right' := by simp only [comm_sq.fac_right_assoc, comm_sq.fac_right] }⟩
#align category_theory.has_lifting_property.of_comp_right CategoryTheory.HasLiftingProperty.of_comp_right
-/

#print CategoryTheory.HasLiftingProperty.of_arrow_iso_left /-
theorem of_arrow_iso_left {A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'}
    (e : Arrow.mk i ≅ Arrow.mk i') (p : X ⟶ Y) [hip : HasLiftingProperty i p] :
    HasLiftingProperty i' p := by
  rw [arrow.iso_w' e]
  infer_instance
#align category_theory.has_lifting_property.of_arrow_iso_left CategoryTheory.HasLiftingProperty.of_arrow_iso_left
-/

#print CategoryTheory.HasLiftingProperty.of_arrow_iso_right /-
theorem of_arrow_iso_right {A B X Y X' Y' : C} (i : A ⟶ B) {p : X ⟶ Y} {p' : X' ⟶ Y'}
    (e : Arrow.mk p ≅ Arrow.mk p') [hip : HasLiftingProperty i p] : HasLiftingProperty i p' :=
  by
  rw [arrow.iso_w' e]
  infer_instance
#align category_theory.has_lifting_property.of_arrow_iso_right CategoryTheory.HasLiftingProperty.of_arrow_iso_right
-/

#print CategoryTheory.HasLiftingProperty.iff_of_arrow_iso_left /-
theorem iff_of_arrow_iso_left {A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'}
    (e : Arrow.mk i ≅ Arrow.mk i') (p : X ⟶ Y) : HasLiftingProperty i p ↔ HasLiftingProperty i' p :=
  by
  constructor <;> intro
  exacts[of_arrow_iso_left e p, of_arrow_iso_left e.symm p]
#align category_theory.has_lifting_property.iff_of_arrow_iso_left CategoryTheory.HasLiftingProperty.iff_of_arrow_iso_left
-/

#print CategoryTheory.HasLiftingProperty.iff_of_arrow_iso_right /-
theorem iff_of_arrow_iso_right {A B X Y X' Y' : C} (i : A ⟶ B) {p : X ⟶ Y} {p' : X' ⟶ Y'}
    (e : Arrow.mk p ≅ Arrow.mk p') : HasLiftingProperty i p ↔ HasLiftingProperty i p' :=
  by
  constructor <;> intro
  exacts[of_arrow_iso_right i e, of_arrow_iso_right i e.symm]
#align category_theory.has_lifting_property.iff_of_arrow_iso_right CategoryTheory.HasLiftingProperty.iff_of_arrow_iso_right
-/

end HasLiftingProperty

end CategoryTheory

