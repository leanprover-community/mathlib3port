/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.adjunction.fully_faithful
! leanprover-community/mathlib commit 9e7c80f638149bfb3504ba8ff48dfdbfc949fb1a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Adjunction.Basic
import Mathbin.CategoryTheory.Conj
import Mathbin.CategoryTheory.Yoneda

/-!
# Adjoints of fully faithful functors

A left adjoint is fully faithful, if and only if the unit is an isomorphism
(and similarly for right adjoints and the counit).

`adjunction.restrict_fully_faithful` shows that an adjunction can be restricted along fully faithful
inclusions.

## Future work

The statements from Riehl 4.5.13 for adjoints which are either full, or faithful.
-/


open CategoryTheory

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

open Category

open Opposite

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

variable {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R)

#print CategoryTheory.unit_isIso_of_L_fully_faithful /-
/-- If the left adjoint is fully faithful, then the unit is an isomorphism.

See
* Lemma 4.5.13 from [Riehl][riehl2017]
* https://math.stackexchange.com/a/2727177
* https://stacks.math.columbia.edu/tag/07RB (we only prove the forward direction!)
-/
instance unit_isIso_of_L_fully_faithful [Full L] [Faithful L] : IsIso (Adjunction.unit h) :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ (Adjunction.unit h) fun X =>
    @Yoneda.isIso _ _ _ _ ((Adjunction.unit h).app X)
      ⟨⟨{ app := fun Y f => L.preimage ((h.homEquiv (unop Y) (L.obj X)).symm f) },
          ⟨by
            ext (x f); dsimp
            apply L.map_injective
            simp, by
            ext (x f); dsimp
            simp only [adjunction.hom_equiv_counit, preimage_comp, preimage_map, category.assoc]
            rw [← h.unit_naturality]
            simp⟩⟩⟩
#align category_theory.unit_is_iso_of_L_fully_faithful CategoryTheory.unit_isIso_of_L_fully_faithful
-/

#print CategoryTheory.counit_isIso_of_R_fully_faithful /-
/-- If the right adjoint is fully faithful, then the counit is an isomorphism.

See <https://stacks.math.columbia.edu/tag/07RB> (we only prove the forward direction!)
-/
instance counit_isIso_of_R_fully_faithful [Full R] [Faithful R] : IsIso (Adjunction.counit h) :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ (Adjunction.counit h) fun X =>
    @isIso_of_op _ _ _ _ _ <|
      @Coyoneda.isIso _ _ _ _ ((Adjunction.counit h).app X).op
        ⟨⟨{ app := fun Y f => R.preimage ((h.homEquiv (R.obj X) Y) f) },
            ⟨by
              ext (x f); dsimp
              apply R.map_injective
              simp, by
              ext (x f); dsimp
              simp only [adjunction.hom_equiv_unit, preimage_comp, preimage_map]
              rw [← h.counit_naturality]
              simp⟩⟩⟩
#align category_theory.counit_is_iso_of_R_fully_faithful CategoryTheory.counit_isIso_of_R_fully_faithful
-/

/- warning: category_theory.inv_map_unit -> CategoryTheory.inv_map_unit is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {L : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} {R : CategoryTheory.Functor.{u2, u1, u4, u3} D _inst_2 C _inst_1} (h : CategoryTheory.Adjunction.{u1, u2, u3, u4} C _inst_1 D _inst_2 L R) {X : C} [_inst_3 : CategoryTheory.IsIso.{u1, u3} C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1) X) (CategoryTheory.Functor.obj.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 L R) X) (CategoryTheory.NatTrans.app.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1) (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 L R) (CategoryTheory.Adjunction.unit.{u1, u2, u3, u4} C _inst_1 D _inst_2 L R h) X)], Eq.{succ u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 L (CategoryTheory.Functor.obj.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 L R) X)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 L (CategoryTheory.Functor.obj.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1) X))) (CategoryTheory.inv.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 L (CategoryTheory.Functor.obj.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1) X)) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 L (CategoryTheory.Functor.obj.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 L R) X)) (CategoryTheory.Functor.map.{u1, u2, u3, u4} C _inst_1 D _inst_2 L (CategoryTheory.Functor.obj.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1) X) (CategoryTheory.Functor.obj.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 L R) X) (CategoryTheory.NatTrans.app.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1) (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 L R) (CategoryTheory.Adjunction.unit.{u1, u2, u3, u4} C _inst_1 D _inst_2 L R h) X)) (CategoryTheory.Functor.map_isIso.{u1, u3, u4, u2} C _inst_1 (CategoryTheory.Functor.obj.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1) X) (CategoryTheory.Functor.obj.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 L R) X) D _inst_2 L (CategoryTheory.NatTrans.app.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1) (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 L R) (CategoryTheory.Adjunction.unit.{u1, u2, u3, u4} C _inst_1 D _inst_2 L R h) X) _inst_3)) (CategoryTheory.NatTrans.app.{u2, u2, u4, u4} D _inst_2 D _inst_2 (CategoryTheory.Functor.comp.{u2, u1, u2, u4, u3, u4} D _inst_2 C _inst_1 D _inst_2 R L) (CategoryTheory.Functor.id.{u2, u4} D _inst_2) (CategoryTheory.Adjunction.counit.{u1, u2, u3, u4} C _inst_1 D _inst_2 L R h) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 L X))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {L : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} {R : CategoryTheory.Functor.{u2, u1, u4, u3} D _inst_2 C _inst_1} (h : CategoryTheory.Adjunction.{u1, u2, u3, u4} C _inst_1 D _inst_2 L R) {X : C} [_inst_3 : CategoryTheory.IsIso.{u1, u3} C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u3, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1)) X) (Prefunctor.obj.{succ u1, succ u1, u3, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 L R)) X) (CategoryTheory.NatTrans.app.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1) (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 L R) (CategoryTheory.Adjunction.unit.{u1, u2, u3, u4} C _inst_1 D _inst_2 L R h) X)], Eq.{succ u2} (Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 L) (Prefunctor.obj.{succ u1, succ u1, u3, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 L R)) X)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 L) (Prefunctor.obj.{succ u1, succ u1, u3, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1)) X))) (CategoryTheory.inv.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 L) (Prefunctor.obj.{succ u1, succ u1, u3, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1)) X)) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 L) (Prefunctor.obj.{succ u1, succ u1, u3, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 L R)) X)) (Prefunctor.map.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 L) (Prefunctor.obj.{succ u1, succ u1, u3, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1)) X) (Prefunctor.obj.{succ u1, succ u1, u3, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 L R)) X) (CategoryTheory.NatTrans.app.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1) (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 L R) (CategoryTheory.Adjunction.unit.{u1, u2, u3, u4} C _inst_1 D _inst_2 L R h) X)) (CategoryTheory.Functor.map_isIso.{u1, u3, u4, u2} C _inst_1 (Prefunctor.obj.{succ u1, succ u1, u3, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1)) X) (Prefunctor.obj.{succ u1, succ u1, u3, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 L R)) X) D _inst_2 L (CategoryTheory.NatTrans.app.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1) (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 L R) (CategoryTheory.Adjunction.unit.{u1, u2, u3, u4} C _inst_1 D _inst_2 L R h) X) _inst_3)) (CategoryTheory.NatTrans.app.{u2, u2, u4, u4} D _inst_2 D _inst_2 (CategoryTheory.Functor.comp.{u2, u1, u2, u4, u3, u4} D _inst_2 C _inst_1 D _inst_2 R L) (CategoryTheory.Functor.id.{u2, u4} D _inst_2) (CategoryTheory.Adjunction.counit.{u1, u2, u3, u4} C _inst_1 D _inst_2 L R h) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 L) X))
Case conversion may be inaccurate. Consider using '#align category_theory.inv_map_unit CategoryTheory.inv_map_unitₓ'. -/
/-- If the unit of an adjunction is an isomorphism, then its inverse on the image of L is given
by L whiskered with the counit. -/
@[simp]
theorem inv_map_unit {X : C} [IsIso (h.Unit.app X)] :
    inv (L.map (h.Unit.app X)) = h.counit.app (L.obj X) :=
  IsIso.inv_eq_of_hom_inv_id h.left_triangle_components
#align category_theory.inv_map_unit CategoryTheory.inv_map_unit

#print CategoryTheory.whiskerLeftLCounitIsoOfIsIsoUnit /-
/-- If the unit is an isomorphism, bundle one has an isomorphism `L ⋙ R ⋙ L ≅ L`. -/
@[simps]
noncomputable def whiskerLeftLCounitIsoOfIsIsoUnit [IsIso h.Unit] : L ⋙ R ⋙ L ≅ L :=
  (L.associator R L).symm ≪≫ isoWhiskerRight (asIso h.Unit).symm L ≪≫ Functor.leftUnitor _
#align category_theory.whisker_left_L_counit_iso_of_is_iso_unit CategoryTheory.whiskerLeftLCounitIsoOfIsIsoUnit
-/

/- warning: category_theory.inv_counit_map -> CategoryTheory.inv_counit_map is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {L : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} {R : CategoryTheory.Functor.{u2, u1, u4, u3} D _inst_2 C _inst_1} (h : CategoryTheory.Adjunction.{u1, u2, u3, u4} C _inst_1 D _inst_2 L R) {X : D} [_inst_3 : CategoryTheory.IsIso.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u2, u2, u4, u4} D _inst_2 D _inst_2 (CategoryTheory.Functor.comp.{u2, u1, u2, u4, u3, u4} D _inst_2 C _inst_1 D _inst_2 R L) X) (CategoryTheory.Functor.obj.{u2, u2, u4, u4} D _inst_2 D _inst_2 (CategoryTheory.Functor.id.{u2, u4} D _inst_2) X) (CategoryTheory.NatTrans.app.{u2, u2, u4, u4} D _inst_2 D _inst_2 (CategoryTheory.Functor.comp.{u2, u1, u2, u4, u3, u4} D _inst_2 C _inst_1 D _inst_2 R L) (CategoryTheory.Functor.id.{u2, u4} D _inst_2) (CategoryTheory.Adjunction.counit.{u1, u2, u3, u4} C _inst_1 D _inst_2 L R h) X)], Eq.{succ u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.obj.{u2, u1, u4, u3} D _inst_2 C _inst_1 R (CategoryTheory.Functor.obj.{u2, u2, u4, u4} D _inst_2 D _inst_2 (CategoryTheory.Functor.id.{u2, u4} D _inst_2) X)) (CategoryTheory.Functor.obj.{u2, u1, u4, u3} D _inst_2 C _inst_1 R (CategoryTheory.Functor.obj.{u2, u2, u4, u4} D _inst_2 D _inst_2 (CategoryTheory.Functor.comp.{u2, u1, u2, u4, u3, u4} D _inst_2 C _inst_1 D _inst_2 R L) X))) (CategoryTheory.inv.{u1, u3} C _inst_1 (CategoryTheory.Functor.obj.{u2, u1, u4, u3} D _inst_2 C _inst_1 R (CategoryTheory.Functor.obj.{u2, u2, u4, u4} D _inst_2 D _inst_2 (CategoryTheory.Functor.comp.{u2, u1, u2, u4, u3, u4} D _inst_2 C _inst_1 D _inst_2 R L) X)) (CategoryTheory.Functor.obj.{u2, u1, u4, u3} D _inst_2 C _inst_1 R (CategoryTheory.Functor.obj.{u2, u2, u4, u4} D _inst_2 D _inst_2 (CategoryTheory.Functor.id.{u2, u4} D _inst_2) X)) (CategoryTheory.Functor.map.{u2, u1, u4, u3} D _inst_2 C _inst_1 R (CategoryTheory.Functor.obj.{u2, u2, u4, u4} D _inst_2 D _inst_2 (CategoryTheory.Functor.comp.{u2, u1, u2, u4, u3, u4} D _inst_2 C _inst_1 D _inst_2 R L) X) (CategoryTheory.Functor.obj.{u2, u2, u4, u4} D _inst_2 D _inst_2 (CategoryTheory.Functor.id.{u2, u4} D _inst_2) X) (CategoryTheory.NatTrans.app.{u2, u2, u4, u4} D _inst_2 D _inst_2 (CategoryTheory.Functor.comp.{u2, u1, u2, u4, u3, u4} D _inst_2 C _inst_1 D _inst_2 R L) (CategoryTheory.Functor.id.{u2, u4} D _inst_2) (CategoryTheory.Adjunction.counit.{u1, u2, u3, u4} C _inst_1 D _inst_2 L R h) X)) (CategoryTheory.Functor.map_isIso.{u2, u4, u3, u1} D _inst_2 (CategoryTheory.Functor.obj.{u2, u2, u4, u4} D _inst_2 D _inst_2 (CategoryTheory.Functor.comp.{u2, u1, u2, u4, u3, u4} D _inst_2 C _inst_1 D _inst_2 R L) X) (CategoryTheory.Functor.obj.{u2, u2, u4, u4} D _inst_2 D _inst_2 (CategoryTheory.Functor.id.{u2, u4} D _inst_2) X) C _inst_1 R (CategoryTheory.NatTrans.app.{u2, u2, u4, u4} D _inst_2 D _inst_2 (CategoryTheory.Functor.comp.{u2, u1, u2, u4, u3, u4} D _inst_2 C _inst_1 D _inst_2 R L) (CategoryTheory.Functor.id.{u2, u4} D _inst_2) (CategoryTheory.Adjunction.counit.{u1, u2, u3, u4} C _inst_1 D _inst_2 L R h) X) _inst_3)) (CategoryTheory.NatTrans.app.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1) (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 L R) (CategoryTheory.Adjunction.unit.{u1, u2, u3, u4} C _inst_1 D _inst_2 L R h) (CategoryTheory.Functor.obj.{u2, u1, u4, u3} D _inst_2 C _inst_1 R X))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {L : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} {R : CategoryTheory.Functor.{u2, u1, u4, u3} D _inst_2 C _inst_1} (h : CategoryTheory.Adjunction.{u1, u2, u3, u4} C _inst_1 D _inst_2 L R) {X : D} [_inst_3 : CategoryTheory.IsIso.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u2, succ u2, u4, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u2, u4, u4} D _inst_2 D _inst_2 (CategoryTheory.Functor.comp.{u2, u1, u2, u4, u3, u4} D _inst_2 C _inst_1 D _inst_2 R L)) X) (Prefunctor.obj.{succ u2, succ u2, u4, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u2, u4, u4} D _inst_2 D _inst_2 (CategoryTheory.Functor.id.{u2, u4} D _inst_2)) X) (CategoryTheory.NatTrans.app.{u2, u2, u4, u4} D _inst_2 D _inst_2 (CategoryTheory.Functor.comp.{u2, u1, u2, u4, u3, u4} D _inst_2 C _inst_1 D _inst_2 R L) (CategoryTheory.Functor.id.{u2, u4} D _inst_2) (CategoryTheory.Adjunction.counit.{u1, u2, u3, u4} C _inst_1 D _inst_2 L R h) X)], Eq.{succ u1} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (Prefunctor.obj.{succ u2, succ u1, u4, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u4, u3} D _inst_2 C _inst_1 R) (Prefunctor.obj.{succ u2, succ u2, u4, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u2, u4, u4} D _inst_2 D _inst_2 (CategoryTheory.Functor.id.{u2, u4} D _inst_2)) X)) (Prefunctor.obj.{succ u2, succ u1, u4, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u4, u3} D _inst_2 C _inst_1 R) (Prefunctor.obj.{succ u2, succ u2, u4, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u2, u4, u4} D _inst_2 D _inst_2 (CategoryTheory.Functor.comp.{u2, u1, u2, u4, u3, u4} D _inst_2 C _inst_1 D _inst_2 R L)) X))) (CategoryTheory.inv.{u1, u3} C _inst_1 (Prefunctor.obj.{succ u2, succ u1, u4, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u4, u3} D _inst_2 C _inst_1 R) (Prefunctor.obj.{succ u2, succ u2, u4, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u2, u4, u4} D _inst_2 D _inst_2 (CategoryTheory.Functor.comp.{u2, u1, u2, u4, u3, u4} D _inst_2 C _inst_1 D _inst_2 R L)) X)) (Prefunctor.obj.{succ u2, succ u1, u4, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u4, u3} D _inst_2 C _inst_1 R) (Prefunctor.obj.{succ u2, succ u2, u4, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u2, u4, u4} D _inst_2 D _inst_2 (CategoryTheory.Functor.id.{u2, u4} D _inst_2)) X)) (Prefunctor.map.{succ u2, succ u1, u4, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u4, u3} D _inst_2 C _inst_1 R) (Prefunctor.obj.{succ u2, succ u2, u4, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u2, u4, u4} D _inst_2 D _inst_2 (CategoryTheory.Functor.comp.{u2, u1, u2, u4, u3, u4} D _inst_2 C _inst_1 D _inst_2 R L)) X) (Prefunctor.obj.{succ u2, succ u2, u4, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u2, u4, u4} D _inst_2 D _inst_2 (CategoryTheory.Functor.id.{u2, u4} D _inst_2)) X) (CategoryTheory.NatTrans.app.{u2, u2, u4, u4} D _inst_2 D _inst_2 (CategoryTheory.Functor.comp.{u2, u1, u2, u4, u3, u4} D _inst_2 C _inst_1 D _inst_2 R L) (CategoryTheory.Functor.id.{u2, u4} D _inst_2) (CategoryTheory.Adjunction.counit.{u1, u2, u3, u4} C _inst_1 D _inst_2 L R h) X)) (CategoryTheory.Functor.map_isIso.{u2, u4, u3, u1} D _inst_2 (Prefunctor.obj.{succ u2, succ u2, u4, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u2, u4, u4} D _inst_2 D _inst_2 (CategoryTheory.Functor.comp.{u2, u1, u2, u4, u3, u4} D _inst_2 C _inst_1 D _inst_2 R L)) X) (Prefunctor.obj.{succ u2, succ u2, u4, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u2, u4, u4} D _inst_2 D _inst_2 (CategoryTheory.Functor.id.{u2, u4} D _inst_2)) X) C _inst_1 R (CategoryTheory.NatTrans.app.{u2, u2, u4, u4} D _inst_2 D _inst_2 (CategoryTheory.Functor.comp.{u2, u1, u2, u4, u3, u4} D _inst_2 C _inst_1 D _inst_2 R L) (CategoryTheory.Functor.id.{u2, u4} D _inst_2) (CategoryTheory.Adjunction.counit.{u1, u2, u3, u4} C _inst_1 D _inst_2 L R h) X) _inst_3)) (CategoryTheory.NatTrans.app.{u1, u1, u3, u3} C _inst_1 C _inst_1 (CategoryTheory.Functor.id.{u1, u3} C _inst_1) (CategoryTheory.Functor.comp.{u1, u2, u1, u3, u4, u3} C _inst_1 D _inst_2 C _inst_1 L R) (CategoryTheory.Adjunction.unit.{u1, u2, u3, u4} C _inst_1 D _inst_2 L R h) (Prefunctor.obj.{succ u2, succ u1, u4, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u4, u3} D _inst_2 C _inst_1 R) X))
Case conversion may be inaccurate. Consider using '#align category_theory.inv_counit_map CategoryTheory.inv_counit_mapₓ'. -/
/-- If the counit of an adjunction is an isomorphism, then its inverse on the image of R is given
by R whiskered with the unit. -/
@[simp]
theorem inv_counit_map {X : D} [IsIso (h.counit.app X)] :
    inv (R.map (h.counit.app X)) = h.Unit.app (R.obj X) :=
  IsIso.inv_eq_of_inv_hom_id h.right_triangle_components
#align category_theory.inv_counit_map CategoryTheory.inv_counit_map

#print CategoryTheory.whiskerLeftRUnitIsoOfIsIsoCounit /-
/-- If the counit of an is an isomorphism, one has an isomorphism `(R ⋙ L ⋙ R) ≅ R`. -/
@[simps]
noncomputable def whiskerLeftRUnitIsoOfIsIsoCounit [IsIso h.counit] : R ⋙ L ⋙ R ≅ R :=
  (R.associator L R).symm ≪≫ isoWhiskerRight (asIso h.counit) R ≪≫ Functor.leftUnitor _
#align category_theory.whisker_left_R_unit_iso_of_is_iso_counit CategoryTheory.whiskerLeftRUnitIsoOfIsIsoCounit
-/

#print CategoryTheory.lFullOfUnitIsIso /-
/-- If the unit is an isomorphism, then the left adjoint is full-/
noncomputable def lFullOfUnitIsIso [IsIso h.Unit] : Full L
    where preimage X Y f := h.homEquiv X (L.obj Y) f ≫ inv (h.Unit.app Y)
#align category_theory.L_full_of_unit_is_iso CategoryTheory.lFullOfUnitIsIso
-/

#print CategoryTheory.L_faithful_of_unit_isIso /-
/-- If the unit is an isomorphism, then the left adjoint is faithful-/
theorem L_faithful_of_unit_isIso [IsIso h.Unit] : Faithful L :=
  {
    map_injective' := fun X Y f g H =>
      by
      rw [← (h.hom_equiv X (L.obj Y)).apply_eq_iff_eq] at H
      simpa using H =≫ inv (h.unit.app Y) }
#align category_theory.L_faithful_of_unit_is_iso CategoryTheory.L_faithful_of_unit_isIso
-/

#print CategoryTheory.rFullOfCounitIsIso /-
/-- If the counit is an isomorphism, then the right adjoint is full-/
noncomputable def rFullOfCounitIsIso [IsIso h.counit] : Full R
    where preimage X Y f := inv (h.counit.app X) ≫ (h.homEquiv (R.obj X) Y).symm f
#align category_theory.R_full_of_counit_is_iso CategoryTheory.rFullOfCounitIsIso
-/

#print CategoryTheory.R_faithful_of_counit_isIso /-
/-- If the counit is an isomorphism, then the right adjoint is faithful-/
theorem R_faithful_of_counit_isIso [IsIso h.counit] : Faithful R :=
  {
    map_injective' := fun X Y f g H =>
      by
      rw [← (h.hom_equiv (R.obj X) Y).symm.apply_eq_iff_eq] at H
      simpa using inv (h.counit.app X) ≫= H }
#align category_theory.R_faithful_of_counit_is_iso CategoryTheory.R_faithful_of_counit_isIso
-/

#print CategoryTheory.whiskerLeft_counit_iso_of_L_fully_faithful /-
instance whiskerLeft_counit_iso_of_L_fully_faithful [Full L] [Faithful L] :
    IsIso (whiskerLeft L h.counit) := by
  have := h.left_triangle
  rw [← is_iso.eq_inv_comp] at this
  rw [this]
  infer_instance
#align category_theory.whisker_left_counit_iso_of_L_fully_faithful CategoryTheory.whiskerLeft_counit_iso_of_L_fully_faithful
-/

#print CategoryTheory.whiskerRight_counit_iso_of_L_fully_faithful /-
instance whiskerRight_counit_iso_of_L_fully_faithful [Full L] [Faithful L] :
    IsIso (whiskerRight h.counit R) :=
  by
  have := h.right_triangle
  rw [← is_iso.eq_inv_comp] at this
  rw [this]
  infer_instance
#align category_theory.whisker_right_counit_iso_of_L_fully_faithful CategoryTheory.whiskerRight_counit_iso_of_L_fully_faithful
-/

#print CategoryTheory.whiskerLeft_unit_iso_of_R_fully_faithful /-
instance whiskerLeft_unit_iso_of_R_fully_faithful [Full R] [Faithful R] :
    IsIso (whiskerLeft R h.Unit) := by
  have := h.right_triangle
  rw [← is_iso.eq_comp_inv] at this
  rw [this]
  infer_instance
#align category_theory.whisker_left_unit_iso_of_R_fully_faithful CategoryTheory.whiskerLeft_unit_iso_of_R_fully_faithful
-/

#print CategoryTheory.whiskerRight_unit_iso_of_R_fully_faithful /-
instance whiskerRight_unit_iso_of_R_fully_faithful [Full R] [Faithful R] :
    IsIso (whiskerRight h.Unit L) := by
  have := h.left_triangle
  rw [← is_iso.eq_comp_inv] at this
  rw [this]
  infer_instance
#align category_theory.whisker_right_unit_iso_of_R_fully_faithful CategoryTheory.whiskerRight_unit_iso_of_R_fully_faithful
-/

-- TODO also do the statements from Riehl 4.5.13 for full and faithful separately?
universe v₃ v₄ u₃ u₄

variable {C' : Type u₃} [Category.{v₃} C']

variable {D' : Type u₄} [Category.{v₄} D']

#print CategoryTheory.Adjunction.restrictFullyFaithful /-
-- TODO: This needs some lemmas describing the produced adjunction, probably in terms of `adj`,
-- `iC` and `iD`.
/-- If `C` is a full subcategory of `C'` and `D` is a full subcategory of `D'`, then we can restrict
an adjunction `L' ⊣ R'` where `L' : C' ⥤ D'` and `R' : D' ⥤ C'` to `C` and `D`.
The construction here is slightly more general, in that `C` is required only to have a full and
faithful "inclusion" functor `iC : C ⥤ C'` (and similarly `iD : D ⥤ D'`) which commute (up to
natural isomorphism) with the proposed restrictions.
-/
def Adjunction.restrictFullyFaithful (iC : C ⥤ C') (iD : D ⥤ D') {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (adj : L' ⊣ R') {L : C ⥤ D} {R : D ⥤ C} (comm1 : iC ⋙ L' ≅ L ⋙ iD) (comm2 : iD ⋙ R' ≅ R ⋙ iC)
    [Full iC] [Faithful iC] [Full iD] [Faithful iD] : L ⊣ R :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        calc
          (L.obj X ⟶ Y) ≃ (iD.obj (L.obj X) ⟶ iD.obj Y) := equivOfFullyFaithful iD
          _ ≃ (L'.obj (iC.obj X) ⟶ iD.obj Y) := Iso.homCongr (comm1.symm.app X) (Iso.refl _)
          _ ≃ (iC.obj X ⟶ R'.obj (iD.obj Y)) := adj.homEquiv _ _
          _ ≃ (iC.obj X ⟶ iC.obj (R.obj Y)) := Iso.homCongr (Iso.refl _) (comm2.app Y)
          _ ≃ (X ⟶ R.obj Y) := (equivOfFullyFaithful iC).symm
          
      homEquiv_naturality_left_symm := fun X' X Y f g =>
        by
        apply iD.map_injective
        simpa using (comm1.inv.naturality_assoc f _).symm
      homEquiv_naturality_right := fun X Y' Y f g =>
        by
        apply iC.map_injective
        suffices : R'.map (iD.map g) ≫ comm2.hom.app Y = comm2.hom.app Y' ≫ iC.map (R.map g)
        simp [this]
        apply comm2.hom.naturality g }
#align category_theory.adjunction.restrict_fully_faithful CategoryTheory.Adjunction.restrictFullyFaithful
-/

end CategoryTheory

