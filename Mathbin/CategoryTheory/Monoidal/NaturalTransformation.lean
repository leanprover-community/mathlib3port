/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.monoidal.natural_transformation
! leanprover-community/mathlib commit cb3ceec8485239a61ed51d944cb9a95b68c6bafc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Monoidal.Functor
import Mathbin.CategoryTheory.FullSubcategory

/-!
# Monoidal natural transformations

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Natural transformations between (lax) monoidal functors must satisfy
an additional compatibility relation with the tensorators:
`F.μ X Y ≫ app (X ⊗ Y) = (app X ⊗ app Y) ≫ G.μ X Y`.

(Lax) monoidal functors between a fixed pair of monoidal categories
themselves form a category.
-/


open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory.Category

open CategoryTheory.Functor

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [MonoidalCategory.{v₂} D]

#print CategoryTheory.MonoidalNatTrans /-
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A monoidal natural transformation is a natural transformation between (lax) monoidal functors
additionally satisfying:
`F.μ X Y ≫ app (X ⊗ Y) = (app X ⊗ app Y) ≫ G.μ X Y`
-/
@[ext]
structure MonoidalNatTrans (F G : LaxMonoidalFunctor C D) extends
  NatTrans F.toFunctor G.toFunctor where
  unit' : F.ε ≫ app (𝟙_ C) = G.ε := by obviously
  tensor' : ∀ X Y, F.μ _ _ ≫ app (X ⊗ Y) = (app X ⊗ app Y) ≫ G.μ _ _ := by obviously
#align category_theory.monoidal_nat_trans CategoryTheory.MonoidalNatTrans
-/

restate_axiom monoidal_nat_trans.tensor'

attribute [simp, reassoc] monoidal_nat_trans.tensor

restate_axiom monoidal_nat_trans.unit'

attribute [simp, reassoc] monoidal_nat_trans.unit

namespace MonoidalNatTrans

#print CategoryTheory.MonoidalNatTrans.id /-
/-- The identity monoidal natural transformation.
-/
@[simps]
def id (F : LaxMonoidalFunctor C D) : MonoidalNatTrans F F :=
  { 𝟙 F.toFunctor with }
#align category_theory.monoidal_nat_trans.id CategoryTheory.MonoidalNatTrans.id
-/

instance (F : LaxMonoidalFunctor C D) : Inhabited (MonoidalNatTrans F F) :=
  ⟨id F⟩

#print CategoryTheory.MonoidalNatTrans.vcomp /-
/-- Vertical composition of monoidal natural transformations.
-/
@[simps]
def vcomp {F G H : LaxMonoidalFunctor C D} (α : MonoidalNatTrans F G) (β : MonoidalNatTrans G H) :
    MonoidalNatTrans F H :=
  { NatTrans.vcomp α.toNatTrans β.toNatTrans with }
#align category_theory.monoidal_nat_trans.vcomp CategoryTheory.MonoidalNatTrans.vcomp
-/

#print CategoryTheory.MonoidalNatTrans.categoryLaxMonoidalFunctor /-
instance categoryLaxMonoidalFunctor : Category (LaxMonoidalFunctor C D)
    where
  Hom := MonoidalNatTrans
  id := id
  comp F G H α β := vcomp α β
#align category_theory.monoidal_nat_trans.category_lax_monoidal_functor CategoryTheory.MonoidalNatTrans.categoryLaxMonoidalFunctor
-/

#print CategoryTheory.MonoidalNatTrans.comp_toNatTrans_lax /-
@[simp]
theorem comp_toNatTrans_lax {F G H : LaxMonoidalFunctor C D} {α : F ⟶ G} {β : G ⟶ H} :
    (α ≫ β).toNatTrans = @CategoryStruct.comp (C ⥤ D) _ _ _ _ α.toNatTrans β.toNatTrans :=
  rfl
#align category_theory.monoidal_nat_trans.comp_to_nat_trans_lax CategoryTheory.MonoidalNatTrans.comp_toNatTrans_lax
-/

#print CategoryTheory.MonoidalNatTrans.categoryMonoidalFunctor /-
instance categoryMonoidalFunctor : Category (MonoidalFunctor C D) :=
  InducedCategory.category MonoidalFunctor.toLaxMonoidalFunctor
#align category_theory.monoidal_nat_trans.category_monoidal_functor CategoryTheory.MonoidalNatTrans.categoryMonoidalFunctor
-/

#print CategoryTheory.MonoidalNatTrans.comp_toNatTrans /-
@[simp]
theorem comp_toNatTrans {F G H : MonoidalFunctor C D} {α : F ⟶ G} {β : G ⟶ H} :
    (α ≫ β).toNatTrans = @CategoryStruct.comp (C ⥤ D) _ _ _ _ α.toNatTrans β.toNatTrans :=
  rfl
#align category_theory.monoidal_nat_trans.comp_to_nat_trans CategoryTheory.MonoidalNatTrans.comp_toNatTrans
-/

variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory.{v₃} E]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.MonoidalNatTrans.hcomp /-
/-- Horizontal composition of monoidal natural transformations.
-/
@[simps]
def hcomp {F G : LaxMonoidalFunctor C D} {H K : LaxMonoidalFunctor D E} (α : MonoidalNatTrans F G)
    (β : MonoidalNatTrans H K) : MonoidalNatTrans (F ⊗⋙ H) (G ⊗⋙ K) :=
  {
    NatTrans.hcomp α.toNatTrans
      β.toNatTrans with
    unit' := by
      dsimp; simp
      conv_lhs => rw [← K.to_functor.map_comp, α.unit]
    tensor' := fun X Y => by
      dsimp; simp
      conv_lhs => rw [← K.to_functor.map_comp, α.tensor, K.to_functor.map_comp] }
#align category_theory.monoidal_nat_trans.hcomp CategoryTheory.MonoidalNatTrans.hcomp
-/

section

attribute [local simp] nat_trans.naturality monoidal_nat_trans.unit monoidal_nat_trans.tensor

#print CategoryTheory.MonoidalNatTrans.prod /-
/-- The cartesian product of two monoidal natural transformations is monoidal. -/
@[simps]
def prod {F G : LaxMonoidalFunctor C D} {H K : LaxMonoidalFunctor C E} (α : MonoidalNatTrans F G)
    (β : MonoidalNatTrans H K) : MonoidalNatTrans (F.prod' H) (G.prod' K)
    where app X := (α.app X, β.app X)
#align category_theory.monoidal_nat_trans.prod CategoryTheory.MonoidalNatTrans.prod
-/

end

end MonoidalNatTrans

namespace MonoidalNatIso

variable {F G : LaxMonoidalFunctor C D}

/- warning: category_theory.monoidal_nat_iso.of_components -> CategoryTheory.MonoidalNatIso.ofComponents is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.monoidal_nat_iso.of_components CategoryTheory.MonoidalNatIso.ofComponentsₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Construct a monoidal natural isomorphism from object level isomorphisms,
and the monoidal naturality in the forward direction.
-/
def ofComponents (app : ∀ X : C, F.obj X ≅ G.obj X)
    (naturality : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (app Y).Hom = (app X).Hom ≫ G.map f)
    (unit : F.ε ≫ (app (𝟙_ C)).Hom = G.ε)
    (tensor : ∀ X Y, F.μ X Y ≫ (app (X ⊗ Y)).Hom = ((app X).Hom ⊗ (app Y).Hom) ≫ G.μ X Y) : F ≅ G
    where
  Hom := { app := fun X => (app X).Hom }
  inv :=
    {
      (NatIso.ofComponents app
          @naturality).inv with
      app := fun X => (app X).inv
      unit' := by
        dsimp
        rw [← Unit, assoc, iso.hom_inv_id, comp_id]
      tensor' := fun X Y => by
        dsimp
        rw [iso.comp_inv_eq, assoc, tensor, ← tensor_comp_assoc, iso.inv_hom_id, iso.inv_hom_id,
          tensor_id, id_comp] }
#align category_theory.monoidal_nat_iso.of_components CategoryTheory.MonoidalNatIso.ofComponents

/- warning: category_theory.monoidal_nat_iso.of_components.hom_app -> CategoryTheory.MonoidalNatIso.ofComponents.hom_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.monoidal_nat_iso.of_components.hom_app CategoryTheory.MonoidalNatIso.ofComponents.hom_appₓ'. -/
@[simp]
theorem ofComponents.hom_app (app : ∀ X : C, F.obj X ≅ G.obj X) (naturality) (unit) (tensor) (X) :
    (ofComponents app naturality Unit tensor).Hom.app X = (app X).Hom :=
  rfl
#align category_theory.monoidal_nat_iso.of_components.hom_app CategoryTheory.MonoidalNatIso.ofComponents.hom_app

/- warning: category_theory.monoidal_nat_iso.of_components.inv_app -> CategoryTheory.MonoidalNatIso.ofComponents.inv_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.monoidal_nat_iso.of_components.inv_app CategoryTheory.MonoidalNatIso.ofComponents.inv_appₓ'. -/
@[simp]
theorem ofComponents.inv_app (app : ∀ X : C, F.obj X ≅ G.obj X) (naturality) (unit) (tensor) (X) :
    (ofComponents app naturality Unit tensor).inv.app X = (app X).inv := by simp [of_components]
#align category_theory.monoidal_nat_iso.of_components.inv_app CategoryTheory.MonoidalNatIso.ofComponents.inv_app

/- warning: category_theory.monoidal_nat_iso.is_iso_of_is_iso_app -> CategoryTheory.MonoidalNatIso.isIso_of_isIso_app is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.MonoidalCategory.{u1, u3} C _inst_1] {D : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u2, u4} D] [_inst_4 : CategoryTheory.MonoidalCategory.{u2, u4} D _inst_3] {F : CategoryTheory.LaxMonoidalFunctor.{u1, u2, u3, u4} C _inst_1 _inst_2 D _inst_3 _inst_4} {G : CategoryTheory.LaxMonoidalFunctor.{u1, u2, u3, u4} C _inst_1 _inst_2 D _inst_3 _inst_4} (α : Quiver.Hom.{succ (max u3 u2), max u3 u4 u1 u2} (CategoryTheory.LaxMonoidalFunctor.{u1, u2, u3, u4} C _inst_1 _inst_2 D _inst_3 _inst_4) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u2, max u3 u4 u1 u2} (CategoryTheory.LaxMonoidalFunctor.{u1, u2, u3, u4} C _inst_1 _inst_2 D _inst_3 _inst_4) (CategoryTheory.Category.toCategoryStruct.{max u3 u2, max u3 u4 u1 u2} (CategoryTheory.LaxMonoidalFunctor.{u1, u2, u3, u4} C _inst_1 _inst_2 D _inst_3 _inst_4) (CategoryTheory.MonoidalNatTrans.categoryLaxMonoidalFunctor.{u1, u2, u3, u4} C _inst_1 _inst_2 D _inst_3 _inst_4))) F G) [_inst_5 : forall (X : C), CategoryTheory.IsIso.{u2, u4} D _inst_3 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 (CategoryTheory.LaxMonoidalFunctor.toFunctor.{u1, u2, u3, u4} C _inst_1 _inst_2 D _inst_3 _inst_4 F) X) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_3 (CategoryTheory.LaxMonoidalFunctor.toFunctor.{u1, u2, u3, u4} C _inst_1 _inst_2 D _inst_3 _inst_4 G) X) (CategoryTheory.NatTrans.app.{u1, u2, u3, u4} C _inst_1 D _inst_3 (CategoryTheory.LaxMonoidalFunctor.toFunctor.{u1, u2, u3, u4} C _inst_1 _inst_2 D _inst_3 _inst_4 F) (CategoryTheory.LaxMonoidalFunctor.toFunctor.{u1, u2, u3, u4} C _inst_1 _inst_2 D _inst_3 _inst_4 G) (CategoryTheory.MonoidalNatTrans.toNatTrans.{u1, u2, u3, u4} C _inst_1 _inst_2 D _inst_3 _inst_4 F G α) X)], CategoryTheory.IsIso.{max u3 u2, max u3 u4 u1 u2} (CategoryTheory.LaxMonoidalFunctor.{u1, u2, u3, u4} C _inst_1 _inst_2 D _inst_3 _inst_4) (CategoryTheory.MonoidalNatTrans.categoryLaxMonoidalFunctor.{u1, u2, u3, u4} C _inst_1 _inst_2 D _inst_3 _inst_4) F G α
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] [_inst_2 : CategoryTheory.MonoidalCategory.{u1, u3} C _inst_1] {D : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u2, u4} D] [_inst_4 : CategoryTheory.MonoidalCategory.{u2, u4} D _inst_3] {F : CategoryTheory.LaxMonoidalFunctor.{u1, u2, u3, u4} C _inst_1 _inst_2 D _inst_3 _inst_4} {G : CategoryTheory.LaxMonoidalFunctor.{u1, u2, u3, u4} C _inst_1 _inst_2 D _inst_3 _inst_4} (α : Quiver.Hom.{max (succ u3) (succ u2), max (max (max u3 u4) u1) u2} (CategoryTheory.LaxMonoidalFunctor.{u1, u2, u3, u4} C _inst_1 _inst_2 D _inst_3 _inst_4) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u2, max (max (max u3 u4) u1) u2} (CategoryTheory.LaxMonoidalFunctor.{u1, u2, u3, u4} C _inst_1 _inst_2 D _inst_3 _inst_4) (CategoryTheory.Category.toCategoryStruct.{max u3 u2, max (max (max u3 u4) u1) u2} (CategoryTheory.LaxMonoidalFunctor.{u1, u2, u3, u4} C _inst_1 _inst_2 D _inst_3 _inst_4) (CategoryTheory.MonoidalNatTrans.categoryLaxMonoidalFunctor.{u1, u2, u3, u4} C _inst_1 _inst_2 D _inst_3 _inst_4))) F G) [_inst_5 : forall (X : C), CategoryTheory.IsIso.{u2, u4} D _inst_3 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 (CategoryTheory.LaxMonoidalFunctor.toFunctor.{u1, u2, u3, u4} C _inst_1 _inst_2 D _inst_3 _inst_4 F)) X) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_3 (CategoryTheory.LaxMonoidalFunctor.toFunctor.{u1, u2, u3, u4} C _inst_1 _inst_2 D _inst_3 _inst_4 G)) X) (CategoryTheory.NatTrans.app.{u1, u2, u3, u4} C _inst_1 D _inst_3 (CategoryTheory.LaxMonoidalFunctor.toFunctor.{u1, u2, u3, u4} C _inst_1 _inst_2 D _inst_3 _inst_4 F) (CategoryTheory.LaxMonoidalFunctor.toFunctor.{u1, u2, u3, u4} C _inst_1 _inst_2 D _inst_3 _inst_4 G) (CategoryTheory.MonoidalNatTrans.toNatTrans.{u1, u2, u3, u4} C _inst_1 _inst_2 D _inst_3 _inst_4 F G α) X)], CategoryTheory.IsIso.{max u3 u2, max (max (max u3 u4) u1) u2} (CategoryTheory.LaxMonoidalFunctor.{u1, u2, u3, u4} C _inst_1 _inst_2 D _inst_3 _inst_4) (CategoryTheory.MonoidalNatTrans.categoryLaxMonoidalFunctor.{u1, u2, u3, u4} C _inst_1 _inst_2 D _inst_3 _inst_4) F G α
Case conversion may be inaccurate. Consider using '#align category_theory.monoidal_nat_iso.is_iso_of_is_iso_app CategoryTheory.MonoidalNatIso.isIso_of_isIso_appₓ'. -/
instance isIso_of_isIso_app (α : F ⟶ G) [∀ X : C, IsIso (α.app X)] : IsIso α :=
  ⟨(IsIso.of_iso
        (ofComponents (fun X => asIso (α.app X)) (fun X Y f => α.toNatTrans.naturality f) α.Unit
          α.tensor)).1⟩
#align category_theory.monoidal_nat_iso.is_iso_of_is_iso_app CategoryTheory.MonoidalNatIso.isIso_of_isIso_app

end MonoidalNatIso

noncomputable section

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.monoidalUnit /-
/-- The unit of a monoidal equivalence can be upgraded to a monoidal natural transformation. -/
@[simps]
def monoidalUnit (F : MonoidalFunctor C D) [IsEquivalence F.toFunctor] :
    LaxMonoidalFunctor.id C ⟶ F.toLaxMonoidalFunctor ⊗⋙ (monoidalInverse F).toLaxMonoidalFunctor :=
  let e := F.toFunctor.asEquivalence
  { toNatTrans := e.Unit
    tensor' := fun X Y =>
      by
      -- This proof is not pretty; golfing welcome!
      dsimp
      simp only [adjunction.hom_equiv_unit, adjunction.hom_equiv_naturality_right, category.id_comp,
        category.assoc]
      simp only [← functor.map_comp]
      erw [e.counit_app_functor, e.counit_app_functor, F.to_lax_monoidal_functor.μ_natural,
        is_iso.inv_hom_id_assoc]
      simp only [CategoryTheory.IsEquivalence.inv_fun_map]
      slice_rhs 2 3 => erw [iso.hom_inv_id_app]
      dsimp
      simp only [CategoryTheory.Category.id_comp]
      slice_rhs 1 2 =>
        rw [← tensor_comp, iso.hom_inv_id_app, iso.hom_inv_id_app]
        dsimp
        rw [tensor_id]
      simp }
#align category_theory.monoidal_unit CategoryTheory.monoidalUnit
-/

instance (F : MonoidalFunctor C D) [IsEquivalence F.toFunctor] : IsIso (monoidalUnit F) :=
  haveI : ∀ X : C, is_iso ((monoidal_unit F).toNatTrans.app X) :=
    by
    intros
    dsimp
    infer_instance
  monoidal_nat_iso.is_iso_of_is_iso_app _

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.monoidalCounit /-
/-- The counit of a monoidal equivalence can be upgraded to a monoidal natural transformation. -/
@[simps]
def monoidalCounit (F : MonoidalFunctor C D) [IsEquivalence F.toFunctor] :
    (monoidalInverse F).toLaxMonoidalFunctor ⊗⋙ F.toLaxMonoidalFunctor ⟶ LaxMonoidalFunctor.id D :=
  let e := F.toFunctor.asEquivalence
  { toNatTrans := e.counit
    unit' := by
      dsimp
      simp only [category.comp_id, category.assoc, functor.map_inv, functor.map_comp,
        nat_iso.inv_inv_app, is_iso.inv_comp, is_equivalence.fun_inv_map, adjunction.hom_equiv_unit]
      erw [e.counit_app_functor, ← e.functor.map_comp_assoc, iso.hom_inv_id_app]
      dsimp; simp
    tensor' := fun X Y => by
      dsimp
      simp only [adjunction.hom_equiv_unit, adjunction.hom_equiv_naturality_right, category.assoc,
        category.comp_id, functor.map_comp]
      simp only [is_equivalence.fun_inv_map]
      erw [e.counit_app_functor]
      simp only [category.assoc]
      erw [← e.functor.map_comp_assoc]
      simp only [CategoryTheory.Iso.inv_hom_id_app, CategoryTheory.Iso.inv_hom_id_app_assoc]
      erw [iso.hom_inv_id_app]
      erw [CategoryTheory.Functor.map_id]
      simp only [category.id_comp]
      simp only [CategoryTheory.Iso.inv_hom_id_app, CategoryTheory.IsIso.hom_inv_id_assoc]
      erw [iso.inv_hom_id_app]
      dsimp; simp; rfl }
#align category_theory.monoidal_counit CategoryTheory.monoidalCounit
-/

instance (F : MonoidalFunctor C D) [IsEquivalence F.toFunctor] : IsIso (monoidalCounit F) :=
  haveI : ∀ X : D, is_iso ((monoidal_counit F).toNatTrans.app X) :=
    by
    intros
    dsimp
    infer_instance
  monoidal_nat_iso.is_iso_of_is_iso_app _

end CategoryTheory

