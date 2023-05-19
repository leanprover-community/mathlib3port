/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.limits.constructions.over.products
! leanprover-community/mathlib commit 50251fd6309cca5ca2e747882ffecd2729f38c5d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Over
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks
import Mathbin.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathbin.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Products in the over category

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Shows that products in the over category can be derived from wide pullbacks in the base category.
The main result is `over_product_of_wide_pullback`, which says that if `C` has `J`-indexed wide
pullbacks, then `over B` has `J`-indexed products.
-/


universe w v u

-- morphism levels before object levels. See note [category_theory universes].
open CategoryTheory CategoryTheory.Limits

variable {J : Type w}

variable {C : Type u} [Category.{v} C]

variable {X : C}

namespace CategoryTheory.Over

namespace ConstructProducts

#print CategoryTheory.Over.ConstructProducts.widePullbackDiagramOfDiagramOver /-
/-- (Implementation)
Given a product diagram in `C/B`, construct the corresponding wide pullback diagram
in `C`.
-/
@[reducible]
def widePullbackDiagramOfDiagramOver (B : C) {J : Type w} (F : Discrete J ⥤ Over B) :
    WidePullbackShape J ⥤ C :=
  WidePullbackShape.wideCospan B (fun j => (F.obj ⟨j⟩).left) fun j => (F.obj ⟨j⟩).Hom
#align category_theory.over.construct_products.wide_pullback_diagram_of_diagram_over CategoryTheory.Over.ConstructProducts.widePullbackDiagramOfDiagramOver
-/

#print CategoryTheory.Over.ConstructProducts.conesEquivInverseObj /-
/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps]
def conesEquivInverseObj (B : C) {J : Type w} (F : Discrete J ⥤ Over B) (c : Cone F) :
    Cone (widePullbackDiagramOfDiagramOver B F)
    where
  pt := c.pt.left
  π :=
    { app := fun X => Option.casesOn X c.pt.Hom fun j : J => (c.π.app ⟨j⟩).left
      -- `tidy` can do this using `case_bash`, but let's try to be a good `-T50000` citizen:
      naturality' := fun X Y f => by
        dsimp; cases X <;> cases Y <;> cases f
        · rw [category.id_comp, category.comp_id]
        · rw [over.w, category.id_comp]
        · rw [category.id_comp, category.comp_id] }
#align category_theory.over.construct_products.cones_equiv_inverse_obj CategoryTheory.Over.ConstructProducts.conesEquivInverseObj
-/

#print CategoryTheory.Over.ConstructProducts.conesEquivInverse /-
/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps]
def conesEquivInverse (B : C) {J : Type w} (F : Discrete J ⥤ Over B) :
    Cone F ⥤ Cone (widePullbackDiagramOfDiagramOver B F)
    where
  obj := conesEquivInverseObj B F
  map c₁ c₂ f :=
    { Hom := f.Hom.left
      w' := fun j => by
        cases j
        · simp
        · dsimp
          rw [← f.w ⟨j⟩]
          rfl }
#align category_theory.over.construct_products.cones_equiv_inverse CategoryTheory.Over.ConstructProducts.conesEquivInverse
-/

attribute [local tidy] tactic.discrete_cases

#print CategoryTheory.Over.ConstructProducts.conesEquivFunctor /-
/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps]
def conesEquivFunctor (B : C) {J : Type w} (F : Discrete J ⥤ Over B) :
    Cone (widePullbackDiagramOfDiagramOver B F) ⥤ Cone F
    where
  obj c :=
    { pt := Over.mk (c.π.app none)
      π :=
        {
          app := fun ⟨j⟩ =>
            Over.homMk (c.π.app (some j)) (by apply c.w (wide_pullback_shape.hom.term j)) } }
  map c₁ c₂ f := { Hom := Over.homMk f.Hom }
#align category_theory.over.construct_products.cones_equiv_functor CategoryTheory.Over.ConstructProducts.conesEquivFunctor
-/

attribute [local tidy] tactic.case_bash

#print CategoryTheory.Over.ConstructProducts.conesEquivUnitIso /-
/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simp]
def conesEquivUnitIso (B : C) (F : Discrete J ⥤ Over B) :
    𝟭 (Cone (widePullbackDiagramOfDiagramOver B F)) ≅
      conesEquivFunctor B F ⋙ conesEquivInverse B F :=
  NatIso.ofComponents
    (fun _ =>
      Cones.ext
        { Hom := 𝟙 _
          inv := 𝟙 _ } (by tidy))
    (by tidy)
#align category_theory.over.construct_products.cones_equiv_unit_iso CategoryTheory.Over.ConstructProducts.conesEquivUnitIso
-/

#print CategoryTheory.Over.ConstructProducts.conesEquivCounitIso /-
/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simp]
def conesEquivCounitIso (B : C) (F : Discrete J ⥤ Over B) :
    conesEquivInverse B F ⋙ conesEquivFunctor B F ≅ 𝟭 (Cone F) :=
  NatIso.ofComponents
    (fun _ =>
      Cones.ext
        { Hom := Over.homMk (𝟙 _)
          inv := Over.homMk (𝟙 _) } (by tidy))
    (by tidy)
#align category_theory.over.construct_products.cones_equiv_counit_iso CategoryTheory.Over.ConstructProducts.conesEquivCounitIso
-/

/- warning: category_theory.over.construct_products.cones_equiv -> CategoryTheory.Over.ConstructProducts.conesEquiv is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] (B : C) (F : CategoryTheory.Functor.{u1, u2, u1, max u3 u2} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) (CategoryTheory.Over.{u2, u3} C _inst_1 B) (CategoryTheory.Over.category.{u3, u2} C _inst_1 B)), CategoryTheory.Equivalence.{u2, u2, max u1 u3 u2, max u1 u3 u2} (CategoryTheory.Limits.Cone.{u1, u2, u1, u3} (CategoryTheory.Limits.WidePullbackShape.{u1} J) (CategoryTheory.Limits.WidePullbackShape.category.{u1} J) C _inst_1 (CategoryTheory.Over.ConstructProducts.widePullbackDiagramOfDiagramOver.{u1, u2, u3} C _inst_1 B J F)) (CategoryTheory.Limits.Cone.category.{u1, u2, u1, u3} (CategoryTheory.Limits.WidePullbackShape.{u1} J) (CategoryTheory.Limits.WidePullbackShape.category.{u1} J) C _inst_1 (CategoryTheory.Over.ConstructProducts.widePullbackDiagramOfDiagramOver.{u1, u2, u3} C _inst_1 B J F)) (CategoryTheory.Limits.Cone.{u1, u2, u1, max u3 u2} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) (CategoryTheory.Over.{u2, u3} C _inst_1 B) (CategoryTheory.Over.category.{u3, u2} C _inst_1 B) F) (CategoryTheory.Limits.Cone.category.{u1, u2, u1, max u3 u2} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) (CategoryTheory.Over.{u2, u3} C _inst_1 B) (CategoryTheory.Over.category.{u3, u2} C _inst_1 B) F)
but is expected to have type
  forall {J : Type.{u1}} {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] (B : C) (F : CategoryTheory.Functor.{u1, u2, u1, max u3 u2} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) (CategoryTheory.Over.{u2, u3} C _inst_1 B) (CategoryTheory.instCategoryOver.{u2, u3} C _inst_1 B)), CategoryTheory.Equivalence.{u2, u2, max (max u3 u1) u2, max (max (max u3 u2) u1) u2} (CategoryTheory.Limits.Cone.{u1, u2, u1, u3} (CategoryTheory.Limits.WidePullbackShape.{u1} J) (CategoryTheory.Limits.WidePullbackShape.category.{u1} J) C _inst_1 (CategoryTheory.Over.ConstructProducts.widePullbackDiagramOfDiagramOver.{u1, u2, u3} C _inst_1 B J F)) (CategoryTheory.Limits.Cone.{u1, u2, u1, max u3 u2} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) (CategoryTheory.Over.{u2, u3} C _inst_1 B) (CategoryTheory.instCategoryOver.{u2, u3} C _inst_1 B) F) (CategoryTheory.Limits.Cone.category.{u1, u2, u1, u3} (CategoryTheory.Limits.WidePullbackShape.{u1} J) (CategoryTheory.Limits.WidePullbackShape.category.{u1} J) C _inst_1 (CategoryTheory.Over.ConstructProducts.widePullbackDiagramOfDiagramOver.{u1, u2, u3} C _inst_1 B J F)) (CategoryTheory.Limits.Cone.category.{u1, u2, u1, max u3 u2} (CategoryTheory.Discrete.{u1} J) (CategoryTheory.discreteCategory.{u1} J) (CategoryTheory.Over.{u2, u3} C _inst_1 B) (CategoryTheory.instCategoryOver.{u2, u3} C _inst_1 B) F)
Case conversion may be inaccurate. Consider using '#align category_theory.over.construct_products.cones_equiv CategoryTheory.Over.ConstructProducts.conesEquivₓ'. -/
-- TODO: Can we add `. obviously` to the second arguments of `nat_iso.of_components` and
--       `cones.ext`?
/-- (Impl) Establish an equivalence between the category of cones for `F` and for the "grown" `F`.
-/
@[simps]
def conesEquiv (B : C) (F : Discrete J ⥤ Over B) :
    Cone (widePullbackDiagramOfDiagramOver B F) ≌ Cone F
    where
  Functor := conesEquivFunctor B F
  inverse := conesEquivInverse B F
  unitIso := conesEquivUnitIso B F
  counitIso := conesEquivCounitIso B F
#align category_theory.over.construct_products.cones_equiv CategoryTheory.Over.ConstructProducts.conesEquiv

#print CategoryTheory.Over.ConstructProducts.has_over_limit_discrete_of_widePullback_limit /-
/-- Use the above equivalence to prove we have a limit. -/
theorem has_over_limit_discrete_of_widePullback_limit {B : C} (F : Discrete J ⥤ Over B)
    [HasLimit (widePullbackDiagramOfDiagramOver B F)] : HasLimit F :=
  HasLimit.mk
    { Cone := _
      IsLimit :=
        IsLimit.ofRightAdjoint (conesEquiv B F).Functor
          (limit.isLimit (widePullbackDiagramOfDiagramOver B F)) }
#align category_theory.over.construct_products.has_over_limit_discrete_of_wide_pullback_limit CategoryTheory.Over.ConstructProducts.has_over_limit_discrete_of_widePullback_limit
-/

#print CategoryTheory.Over.ConstructProducts.over_product_of_widePullback /-
/-- Given a wide pullback in `C`, construct a product in `C/B`. -/
theorem over_product_of_widePullback [HasLimitsOfShape (WidePullbackShape J) C] {B : C} :
    HasLimitsOfShape (Discrete J) (Over B) :=
  { HasLimit := fun F => has_over_limit_discrete_of_widePullback_limit F }
#align category_theory.over.construct_products.over_product_of_wide_pullback CategoryTheory.Over.ConstructProducts.over_product_of_widePullback
-/

#print CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback /-
/-- Given a pullback in `C`, construct a binary product in `C/B`. -/
theorem over_binaryProduct_of_pullback [HasPullbacks C] {B : C} : HasBinaryProducts (Over B) :=
  over_product_of_widePullback
#align category_theory.over.construct_products.over_binary_product_of_pullback CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback
-/

#print CategoryTheory.Over.ConstructProducts.over_products_of_widePullbacks /-
/-- Given all wide pullbacks in `C`, construct products in `C/B`. -/
theorem over_products_of_widePullbacks [HasWidePullbacks.{w} C] {B : C} :
    HasProducts.{w} (Over B) := fun J => over_product_of_widePullback
#align category_theory.over.construct_products.over_products_of_wide_pullbacks CategoryTheory.Over.ConstructProducts.over_products_of_widePullbacks
-/

#print CategoryTheory.Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks /-
/-- Given all finite wide pullbacks in `C`, construct finite products in `C/B`. -/
theorem over_finiteProducts_of_finiteWidePullbacks [HasFiniteWidePullbacks C] {B : C} :
    HasFiniteProducts (Over B) :=
  ⟨fun n => over_product_of_widePullback⟩
#align category_theory.over.construct_products.over_finite_products_of_finite_wide_pullbacks CategoryTheory.Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
-/

end ConstructProducts

attribute [local tidy] tactic.discrete_cases

#print CategoryTheory.Over.over_hasTerminal /-
/-- Construct terminal object in the over category. This isn't an instance as it's not typically the
way we want to define terminal objects.
(For instance, this gives a terminal object which is different from the generic one given by
`over_product_of_wide_pullback` above.)
-/
theorem over_hasTerminal (B : C) : HasTerminal (Over B) :=
  {
    HasLimit := fun F =>
      HasLimit.mk
        { Cone :=
            { pt := Over.mk (𝟙 _)
              π := { app := fun p => p.as.elim } }
          IsLimit :=
            { lift := fun s => Over.homMk _
              fac := fun _ j => j.as.elim
              uniq := fun s m _ => by
                ext
                rw [over.hom_mk_left]
                have := m.w
                dsimp at this
                rwa [category.comp_id, category.comp_id] at this } } }
#align category_theory.over.over_has_terminal CategoryTheory.Over.over_hasTerminal
-/

end CategoryTheory.Over

