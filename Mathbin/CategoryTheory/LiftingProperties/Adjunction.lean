/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module category_theory.lifting_properties.adjunction
! leanprover-community/mathlib commit 3dadefa3f544b1db6214777fe47910739b54c66a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.LiftingProperties.Basic
import Mathbin.CategoryTheory.Adjunction.Basic

/-!

# Lifting properties and adjunction

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we obtain `adjunction.has_lifting_property_iff`, which states
that when we have an adjunction `adj : G ⊣ F` between two functors `G : C ⥤ D`
and `F : D ⥤ C`, then a morphism of the form `G.map i` has the left lifting
property in `D` with respect to a morphism `p` if and only the morphism `i`
has the left lifting property in `C` with respect to `F.map p`.

-/


namespace CategoryTheory

open Category

variable {C D : Type _} [Category C] [Category D] {G : C ⥤ D} {F : D ⥤ C}

namespace CommSq

section

variable {A B : C} {X Y : D} {i : A ⟶ B} {p : X ⟶ Y} {u : G.obj A ⟶ X} {v : G.obj B ⟶ Y}
  (sq : CommSq u (G.map i) p v) (adj : G ⊣ F)

include sq

/- warning: category_theory.comm_sq.right_adjoint -> CategoryTheory.CommSq.right_adjoint is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.comm_sq.right_adjoint CategoryTheory.CommSq.right_adjointₓ'. -/
/-- When we have an adjunction `G ⊣ F`, any commutative square where the left
map is of the form `G.map i` and the right map is `p` has an "adjoint" commutative
square whose left map is `i` and whose right map is `F.map p`. -/
theorem right_adjoint : CommSq (adj.homEquiv _ _ u) i (F.map p) (adj.homEquiv _ _ v) :=
  ⟨by
    simp only [adjunction.hom_equiv_unit, assoc, ← F.map_comp, sq.w]
    rw [F.map_comp, adjunction.unit_naturality_assoc]⟩
#align category_theory.comm_sq.right_adjoint CategoryTheory.CommSq.right_adjoint

/- warning: category_theory.comm_sq.right_adjoint_lift_struct_equiv -> CategoryTheory.CommSq.rightAdjointLiftStructEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.comm_sq.right_adjoint_lift_struct_equiv CategoryTheory.CommSq.rightAdjointLiftStructEquivₓ'. -/
/-- The liftings of a commutative are in bijection with the liftings of its (right)
adjoint square. -/
def rightAdjointLiftStructEquiv : sq.LiftStruct ≃ (sq.rightAdjoint adj).LiftStruct
    where
  toFun l :=
    { l := adj.homEquiv _ _ l.l
      fac_left' := by rw [← adj.hom_equiv_naturality_left, l.fac_left]
      fac_right' := by rw [← adjunction.hom_equiv_naturality_right, l.fac_right] }
  invFun l :=
    { l := (adj.homEquiv _ _).symm l.l
      fac_left' := by
        rw [← adjunction.hom_equiv_naturality_left_symm, l.fac_left]
        apply (adj.hom_equiv _ _).left_inv
      fac_right' := by
        rw [← adjunction.hom_equiv_naturality_right_symm, l.fac_right]
        apply (adj.hom_equiv _ _).left_inv }
  left_inv := by tidy
  right_inv := by tidy
#align category_theory.comm_sq.right_adjoint_lift_struct_equiv CategoryTheory.CommSq.rightAdjointLiftStructEquiv

/- warning: category_theory.comm_sq.right_adjoint_has_lift_iff -> CategoryTheory.CommSq.right_adjoint_hasLift_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.comm_sq.right_adjoint_has_lift_iff CategoryTheory.CommSq.right_adjoint_hasLift_iffₓ'. -/
/-- A square has a lifting if and only if its (right) adjoint square has a lifting. -/
theorem right_adjoint_hasLift_iff : HasLift (sq.rightAdjoint adj) ↔ HasLift sq :=
  by
  simp only [has_lift.iff]
  exact Equiv.nonempty_congr (sq.right_adjoint_lift_struct_equiv adj).symm
#align category_theory.comm_sq.right_adjoint_has_lift_iff CategoryTheory.CommSq.right_adjoint_hasLift_iff

instance [HasLift sq] : HasLift (sq.rightAdjoint adj) :=
  by
  rw [right_adjoint_has_lift_iff]
  infer_instance

end

section

variable {A B : C} {X Y : D} {i : A ⟶ B} {p : X ⟶ Y} {u : A ⟶ F.obj X} {v : B ⟶ F.obj Y}
  (sq : CommSq u i (F.map p) v) (adj : G ⊣ F)

include sq

/- warning: category_theory.comm_sq.left_adjoint -> CategoryTheory.CommSq.left_adjoint is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.comm_sq.left_adjoint CategoryTheory.CommSq.left_adjointₓ'. -/
/-- When we have an adjunction `G ⊣ F`, any commutative square where the left
map is of the form `i` and the right map is `F.map p` has an "adjoint" commutative
square whose left map is `G.map i` and whose right map is `p`. -/
theorem left_adjoint : CommSq ((adj.homEquiv _ _).symm u) (G.map i) p ((adj.homEquiv _ _).symm v) :=
  ⟨by
    simp only [adjunction.hom_equiv_counit, assoc, ← G.map_comp_assoc, ← sq.w]
    rw [G.map_comp, assoc, adjunction.counit_naturality]⟩
#align category_theory.comm_sq.left_adjoint CategoryTheory.CommSq.left_adjoint

/- warning: category_theory.comm_sq.left_adjoint_lift_struct_equiv -> CategoryTheory.CommSq.leftAdjointLiftStructEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.comm_sq.left_adjoint_lift_struct_equiv CategoryTheory.CommSq.leftAdjointLiftStructEquivₓ'. -/
/-- The liftings of a commutative are in bijection with the liftings of its (left)
adjoint square. -/
def leftAdjointLiftStructEquiv : sq.LiftStruct ≃ (sq.leftAdjoint adj).LiftStruct
    where
  toFun l :=
    { l := (adj.homEquiv _ _).symm l.l
      fac_left' := by rw [← adj.hom_equiv_naturality_left_symm, l.fac_left]
      fac_right' := by rw [← adj.hom_equiv_naturality_right_symm, l.fac_right] }
  invFun l :=
    { l := (adj.homEquiv _ _) l.l
      fac_left' := by
        rw [← adj.hom_equiv_naturality_left, l.fac_left]
        apply (adj.hom_equiv _ _).right_inv
      fac_right' := by
        rw [← adj.hom_equiv_naturality_right, l.fac_right]
        apply (adj.hom_equiv _ _).right_inv }
  left_inv := by tidy
  right_inv := by tidy
#align category_theory.comm_sq.left_adjoint_lift_struct_equiv CategoryTheory.CommSq.leftAdjointLiftStructEquiv

/- warning: category_theory.comm_sq.left_adjoint_has_lift_iff -> CategoryTheory.CommSq.left_adjoint_hasLift_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.comm_sq.left_adjoint_has_lift_iff CategoryTheory.CommSq.left_adjoint_hasLift_iffₓ'. -/
/-- A (left) adjoint square has a lifting if and only if the original square has a lifting. -/
theorem left_adjoint_hasLift_iff : HasLift (sq.leftAdjoint adj) ↔ HasLift sq :=
  by
  simp only [has_lift.iff]
  exact Equiv.nonempty_congr (sq.left_adjoint_lift_struct_equiv adj).symm
#align category_theory.comm_sq.left_adjoint_has_lift_iff CategoryTheory.CommSq.left_adjoint_hasLift_iff

instance [HasLift sq] : HasLift (sq.leftAdjoint adj) :=
  by
  rw [left_adjoint_has_lift_iff]
  infer_instance

end

end CommSq

namespace Adjunction

/- warning: category_theory.adjunction.has_lifting_property_iff -> CategoryTheory.Adjunction.hasLiftingProperty_iff is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} {D : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u3, u1} C] [_inst_2 : CategoryTheory.Category.{u4, u2} D] {G : CategoryTheory.Functor.{u3, u4, u1, u2} C _inst_1 D _inst_2} {F : CategoryTheory.Functor.{u4, u3, u2, u1} D _inst_2 C _inst_1}, (CategoryTheory.Adjunction.{u3, u4, u1, u2} C _inst_1 D _inst_2 G F) -> (forall {A : C} {B : C} {X : D} {Y : D} (i : Quiver.Hom.{succ u3, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} C (CategoryTheory.Category.toCategoryStruct.{u3, u1} C _inst_1)) A B) (p : Quiver.Hom.{succ u4, u2} D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) X Y), Iff (CategoryTheory.HasLiftingProperty.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 G A) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} C _inst_1 D _inst_2 G B) X Y (CategoryTheory.Functor.map.{u3, u4, u1, u2} C _inst_1 D _inst_2 G A B i) p) (CategoryTheory.HasLiftingProperty.{u1, u3} C _inst_1 A B (CategoryTheory.Functor.obj.{u4, u3, u2, u1} D _inst_2 C _inst_1 F X) (CategoryTheory.Functor.obj.{u4, u3, u2, u1} D _inst_2 C _inst_1 F Y) i (CategoryTheory.Functor.map.{u4, u3, u2, u1} D _inst_2 C _inst_1 F X Y p)))
but is expected to have type
  forall {C : Type.{u2}} {D : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u4, u2} C] [_inst_2 : CategoryTheory.Category.{u3, u1} D] {G : CategoryTheory.Functor.{u4, u3, u2, u1} C _inst_1 D _inst_2} {F : CategoryTheory.Functor.{u3, u4, u1, u2} D _inst_2 C _inst_1}, (CategoryTheory.Adjunction.{u4, u3, u2, u1} C _inst_1 D _inst_2 G F) -> (forall {A : C} {B : C} {X : D} {Y : D} (i : Quiver.Hom.{succ u4, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} C (CategoryTheory.Category.toCategoryStruct.{u4, u2} C _inst_1)) A B) (p : Quiver.Hom.{succ u3, u1} D (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} D (CategoryTheory.Category.toCategoryStruct.{u3, u1} D _inst_2)) X Y), Iff (CategoryTheory.HasLiftingProperty.{u1, u3} D _inst_2 (Prefunctor.obj.{succ u4, succ u3, u2, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} C (CategoryTheory.Category.toCategoryStruct.{u4, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} D (CategoryTheory.Category.toCategoryStruct.{u3, u1} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u4, u3, u2, u1} C _inst_1 D _inst_2 G) A) (Prefunctor.obj.{succ u4, succ u3, u2, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} C (CategoryTheory.Category.toCategoryStruct.{u4, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} D (CategoryTheory.Category.toCategoryStruct.{u3, u1} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u4, u3, u2, u1} C _inst_1 D _inst_2 G) B) X Y (Prefunctor.map.{succ u4, succ u3, u2, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} C (CategoryTheory.Category.toCategoryStruct.{u4, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} D (CategoryTheory.Category.toCategoryStruct.{u3, u1} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u4, u3, u2, u1} C _inst_1 D _inst_2 G) A B i) p) (CategoryTheory.HasLiftingProperty.{u2, u4} C _inst_1 A B (Prefunctor.obj.{succ u3, succ u4, u1, u2} D (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} D (CategoryTheory.Category.toCategoryStruct.{u3, u1} D _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} C (CategoryTheory.Category.toCategoryStruct.{u4, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u3, u4, u1, u2} D _inst_2 C _inst_1 F) X) (Prefunctor.obj.{succ u3, succ u4, u1, u2} D (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} D (CategoryTheory.Category.toCategoryStruct.{u3, u1} D _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} C (CategoryTheory.Category.toCategoryStruct.{u4, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u3, u4, u1, u2} D _inst_2 C _inst_1 F) Y) i (Prefunctor.map.{succ u3, succ u4, u1, u2} D (CategoryTheory.CategoryStruct.toQuiver.{u3, u1} D (CategoryTheory.Category.toCategoryStruct.{u3, u1} D _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} C (CategoryTheory.Category.toCategoryStruct.{u4, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u3, u4, u1, u2} D _inst_2 C _inst_1 F) X Y p)))
Case conversion may be inaccurate. Consider using '#align category_theory.adjunction.has_lifting_property_iff CategoryTheory.Adjunction.hasLiftingProperty_iffₓ'. -/
theorem hasLiftingProperty_iff (adj : G ⊣ F) {A B : C} {X Y : D} (i : A ⟶ B) (p : X ⟶ Y) :
    HasLiftingProperty (G.map i) p ↔ HasLiftingProperty i (F.map p) :=
  by
  constructor <;> intro <;> constructor <;> intro f g sq
  · rw [← sq.left_adjoint_has_lift_iff adj]
    infer_instance
  · rw [← sq.right_adjoint_has_lift_iff adj]
    infer_instance
#align category_theory.adjunction.has_lifting_property_iff CategoryTheory.Adjunction.hasLiftingProperty_iff

end Adjunction

end CategoryTheory

