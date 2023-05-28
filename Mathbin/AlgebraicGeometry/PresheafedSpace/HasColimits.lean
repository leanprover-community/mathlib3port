/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebraic_geometry.presheafed_space.has_colimits
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicGeometry.PresheafedSpace
import Mathbin.Topology.Category.Top.Limits.Basic
import Mathbin.Topology.Sheaves.Limits

/-!
# `PresheafedSpace C` has colimits.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

If `C` has limits, then the category `PresheafedSpace C` has colimits,
and the forgetful functor to `Top` preserves these colimits.

When restricted to a diagram where the underlying continuous maps are open embeddings,
this says that we can glue presheaved spaces.

Given a diagram `F : J ⥤ PresheafedSpace C`,
we first build the colimit of the underlying topological spaces,
as `colimit (F ⋙ PresheafedSpace.forget C)`. Call that colimit space `X`.

Our strategy is to push each of the presheaves `F.obj j`
forward along the continuous map `colimit.ι (F ⋙ PresheafedSpace.forget C) j` to `X`.
Since pushforward is functorial, we obtain a diagram `J ⥤ (presheaf C X)ᵒᵖ`
of presheaves on a single space `X`.
(Note that the arrows now point the other direction,
because this is the way `PresheafedSpace C` is set up.)

The limit of this diagram then constitutes the colimit presheaf.
-/


noncomputable section

universe v' u' v u

open CategoryTheory

open TopCat

open TopCat.Presheaf

open TopologicalSpace

open Opposite

open CategoryTheory.Category

open CategoryTheory.Limits

open CategoryTheory.Functor

variable {J : Type u'} [Category.{v'} J]

variable {C : Type u} [Category.{v} C]

namespace AlgebraicGeometry

namespace PresheafedSpace

attribute [local simp] eq_to_hom_map

attribute [local tidy] tactic.auto_cases_opens

/- warning: algebraic_geometry.PresheafedSpace.map_id_c_app -> AlgebraicGeometry.PresheafedSpace.map_id_c_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.map_id_c_app AlgebraicGeometry.PresheafedSpace.map_id_c_appₓ'. -/
@[simp]
theorem map_id_c_app (F : J ⥤ PresheafedSpace.{v} C) (j) (U) :
    (F.map (𝟙 j)).c.app (op U) =
      (Pushforward.id (F.obj j).Presheaf).inv.app (op U) ≫
        (pushforwardEq
                (by
                  simp
                  rfl)
                (F.obj j).Presheaf).Hom.app
          (op U) :=
  by
  cases U
  dsimp
  simp [PresheafedSpace.congr_app (F.map_id j)]
  rfl
#align algebraic_geometry.PresheafedSpace.map_id_c_app AlgebraicGeometry.PresheafedSpace.map_id_c_app

/- warning: algebraic_geometry.PresheafedSpace.map_comp_c_app -> AlgebraicGeometry.PresheafedSpace.map_comp_c_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.map_comp_c_app AlgebraicGeometry.PresheafedSpace.map_comp_c_appₓ'. -/
@[simp]
theorem map_comp_c_app (F : J ⥤ PresheafedSpace.{v} C) {j₁ j₂ j₃} (f : j₁ ⟶ j₂) (g : j₂ ⟶ j₃) (U) :
    (F.map (f ≫ g)).c.app (op U) =
      (F.map g).c.app (op U) ≫
        (pushforwardMap (F.map g).base (F.map f).c).app (op U) ≫
          (Pushforward.comp (F.obj j₁).Presheaf (F.map f).base (F.map g).base).inv.app (op U) ≫
            (pushforwardEq
                    (by
                      rw [F.map_comp]
                      rfl)
                    _).Hom.app
              _ :=
  by
  cases U
  dsimp
  simp only [PresheafedSpace.congr_app (F.map_comp f g)]
  dsimp; simp; dsimp; simp
#align algebraic_geometry.PresheafedSpace.map_comp_c_app AlgebraicGeometry.PresheafedSpace.map_comp_c_app

/- warning: algebraic_geometry.PresheafedSpace.componentwise_diagram -> AlgebraicGeometry.PresheafedSpace.componentwiseDiagram is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] (F : CategoryTheory.Functor.{u1, u3, u2, max u4 (succ u3)} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u3, u3, u4} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u3, u4} C _inst_2)) [_inst_3 : CategoryTheory.Limits.HasColimit.{u1, u2, u3, max u4 (succ u3)} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u3, u3, u4} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u3, u4} C _inst_2) F], (TopologicalSpace.Opens.{u3} (coeSort.{succ (succ u3), succ (succ u3)} TopCat.{u3} Type.{u3} TopCat.hasCoeToSort.{u3} (AlgebraicGeometry.PresheafedSpace.carrier.{u3, u3, u4} C _inst_2 (CategoryTheory.Limits.colimit.{u1, u2, u3, max u4 (succ u3)} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u3, u3, u4} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u3, u4} C _inst_2) F _inst_3))) (TopCat.topologicalSpace.{u3} (AlgebraicGeometry.PresheafedSpace.carrier.{u3, u3, u4} C _inst_2 (CategoryTheory.Limits.colimit.{u1, u2, u3, max u4 (succ u3)} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u3, u3, u4} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u3, u4} C _inst_2) F _inst_3)))) -> (CategoryTheory.Functor.{u1, u3, u2, u4} (Opposite.{succ u2} J) (CategoryTheory.Category.opposite.{u1, u2} J _inst_1) C _inst_2)
but is expected to have type
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] (F : CategoryTheory.Functor.{u1, u3, u2, max (succ u3) u4} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u4, u3, u3} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u4, u3, u3} C _inst_2)) [_inst_3 : CategoryTheory.Limits.HasColimit.{u1, u2, u3, max u4 (succ u3)} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u4, u3, u3} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u4, u3, u3} C _inst_2) F], (TopologicalSpace.Opens.{u3} (CategoryTheory.Bundled.α.{u3, u3} TopologicalSpace.{u3} (AlgebraicGeometry.PresheafedSpace.carrier.{u4, u3, u3} C _inst_2 (CategoryTheory.Limits.colimit.{u1, u2, u3, max u4 (succ u3)} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u4, u3, u3} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u4, u3, u3} C _inst_2) F _inst_3))) (AlgebraicGeometry.PresheafedSpace.instTopologicalSpaceαCarrier.{u4, u3, u3} C _inst_2 (CategoryTheory.Limits.colimit.{u1, u2, u3, max u4 (succ u3)} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u4, u3, u3} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u4, u3, u3} C _inst_2) F _inst_3))) -> (CategoryTheory.Functor.{u1, u3, u2, u4} (Opposite.{succ u2} J) (CategoryTheory.Category.opposite.{u1, u2} J _inst_1) C _inst_2)
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.componentwise_diagram AlgebraicGeometry.PresheafedSpace.componentwiseDiagramₓ'. -/
-- See note [dsimp, simp]
/-- Given a diagram of `PresheafedSpace C`s, its colimit is computed by pushing the sheaves onto
the colimit of the underlying spaces, and taking componentwise limit.
This is the componentwise diagram for an open set `U` of the colimit of the underlying spaces.
-/
@[simps]
def componentwiseDiagram (F : J ⥤ PresheafedSpace.{v} C) [HasColimit F]
    (U : Opens (Limits.colimit F).carrier) : Jᵒᵖ ⥤ C
    where
  obj j := (F.obj (unop j)).Presheaf.obj (op ((Opens.map (colimit.ι F (unop j)).base).obj U))
  map j k f :=
    (F.map f.unop).c.app _ ≫
      (F.obj (unop k)).Presheaf.map
        (eqToHom
          (by
            rw [← colimit.w F f.unop, comp_base]
            rfl))
  map_comp' i j k f g := by
    cases U
    dsimp
    simp_rw [map_comp_c_app, category.assoc]
    congr 1
    rw [TopCat.Presheaf.Pushforward.comp_inv_app, TopCat.Presheaf.pushforwardEq_hom_app,
      CategoryTheory.NatTrans.naturality_assoc, TopCat.Presheaf.pushforwardMap_app]
    congr 1
    rw [category.id_comp, ← (F.obj (unop k)).Presheaf.map_comp]
    erw [← (F.obj (unop k)).Presheaf.map_comp]
    congr
#align algebraic_geometry.PresheafedSpace.componentwise_diagram AlgebraicGeometry.PresheafedSpace.componentwiseDiagram

variable [HasColimitsOfShape J TopCat.{v}]

/- warning: algebraic_geometry.PresheafedSpace.pushforward_diagram_to_colimit -> AlgebraicGeometry.PresheafedSpace.pushforwardDiagramToColimit is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] [_inst_3 : CategoryTheory.Limits.HasColimitsOfShape.{u1, u2, u3, succ u3} J _inst_1 TopCat.{u3} TopCat.largeCategory.{u3}] (F : CategoryTheory.Functor.{u1, u3, u2, max u4 (succ u3)} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u3, u3, u4} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u3, u4} C _inst_2)), CategoryTheory.Functor.{u1, u3, u2, max u4 u3} J _inst_1 (Opposite.{succ (max u4 u3)} (TopCat.Presheaf.{u3, u3, u4} C _inst_2 (CategoryTheory.Limits.colimit.{u1, u2, u3, succ u3} J _inst_1 TopCat.{u3} TopCat.largeCategory.{u3} (CategoryTheory.Functor.comp.{u1, u3, u3, u2, max u4 (succ u3), succ u3} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u3, u3, u4} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u3, u4} C _inst_2) TopCat.{u3} TopCat.largeCategory.{u3} F (AlgebraicGeometry.PresheafedSpace.forget.{u3, u4} C _inst_2)) (AlgebraicGeometry.PresheafedSpace.pushforwardDiagramToColimit._proof_1.{u4, u2, u3, u1} J _inst_1 C _inst_2 _inst_3 F)))) (CategoryTheory.Category.opposite.{u3, max u4 u3} (TopCat.Presheaf.{u3, u3, u4} C _inst_2 (CategoryTheory.Limits.colimit.{u1, u2, u3, succ u3} J _inst_1 TopCat.{u3} TopCat.largeCategory.{u3} (CategoryTheory.Functor.comp.{u1, u3, u3, u2, max u4 (succ u3), succ u3} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u3, u3, u4} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u3, u4} C _inst_2) TopCat.{u3} TopCat.largeCategory.{u3} F (AlgebraicGeometry.PresheafedSpace.forget.{u3, u4} C _inst_2)) (AlgebraicGeometry.PresheafedSpace.pushforwardDiagramToColimit._proof_1.{u4, u2, u3, u1} J _inst_1 C _inst_2 _inst_3 F))) (TopCat.Presheaf.category.{u3, u3, u4} C _inst_2 (CategoryTheory.Limits.colimit.{u1, u2, u3, succ u3} J _inst_1 TopCat.{u3} TopCat.largeCategory.{u3} (CategoryTheory.Functor.comp.{u1, u3, u3, u2, max u4 (succ u3), succ u3} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u3, u3, u4} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u3, u4} C _inst_2) TopCat.{u3} TopCat.largeCategory.{u3} F (AlgebraicGeometry.PresheafedSpace.forget.{u3, u4} C _inst_2)) (AlgebraicGeometry.PresheafedSpace.pushforwardDiagramToColimit._proof_1.{u4, u2, u3, u1} J _inst_1 C _inst_2 _inst_3 F))))
but is expected to have type
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] [_inst_3 : CategoryTheory.Limits.HasColimitsOfShape.{u1, u2, u3, succ u3} J _inst_1 TopCat.{u3} instTopCatLargeCategory.{u3}] (F : CategoryTheory.Functor.{u1, u3, u2, max (succ u3) u4} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u4, u3, u3} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u4, u3, u3} C _inst_2)), CategoryTheory.Functor.{u1, u3, u2, max u4 u3} J _inst_1 (Opposite.{max (succ u4) (succ u3)} (TopCat.Presheaf.{u3, u3, u4} C _inst_2 (CategoryTheory.Limits.colimit.{u1, u2, u3, succ u3} J _inst_1 TopCat.{u3} instTopCatLargeCategory.{u3} (CategoryTheory.Functor.comp.{u1, u3, u3, u2, max u4 (succ u3), succ u3} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u4, u3, u3} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u4, u3, u3} C _inst_2) TopCat.{u3} instTopCatLargeCategory.{u3} F (AlgebraicGeometry.PresheafedSpace.forget.{u4, u3, u3} C _inst_2)) (CategoryTheory.Limits.hasColimitOfHasColimitsOfShape.{u1, u2, u3, succ u3} TopCat.{u3} instTopCatLargeCategory.{u3} J _inst_1 _inst_3 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, max u4 (succ u3), succ u3} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u4, u3, u3} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u4, u3, u3} C _inst_2) TopCat.{u3} instTopCatLargeCategory.{u3} F (AlgebraicGeometry.PresheafedSpace.forget.{u4, u3, u3} C _inst_2)))))) (CategoryTheory.Category.opposite.{u3, max u4 u3} (TopCat.Presheaf.{u3, u3, u4} C _inst_2 (CategoryTheory.Limits.colimit.{u1, u2, u3, succ u3} J _inst_1 TopCat.{u3} instTopCatLargeCategory.{u3} (CategoryTheory.Functor.comp.{u1, u3, u3, u2, max u4 (succ u3), succ u3} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u4, u3, u3} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u4, u3, u3} C _inst_2) TopCat.{u3} instTopCatLargeCategory.{u3} F (AlgebraicGeometry.PresheafedSpace.forget.{u4, u3, u3} C _inst_2)) (CategoryTheory.Limits.hasColimitOfHasColimitsOfShape.{u1, u2, u3, succ u3} TopCat.{u3} instTopCatLargeCategory.{u3} J _inst_1 _inst_3 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, max u4 (succ u3), succ u3} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u4, u3, u3} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u4, u3, u3} C _inst_2) TopCat.{u3} instTopCatLargeCategory.{u3} F (AlgebraicGeometry.PresheafedSpace.forget.{u4, u3, u3} C _inst_2))))) (TopCat.instCategoryPresheaf.{u3, u3, u4} C _inst_2 (CategoryTheory.Limits.colimit.{u1, u2, u3, succ u3} J _inst_1 TopCat.{u3} instTopCatLargeCategory.{u3} (CategoryTheory.Functor.comp.{u1, u3, u3, u2, max u4 (succ u3), succ u3} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u4, u3, u3} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u4, u3, u3} C _inst_2) TopCat.{u3} instTopCatLargeCategory.{u3} F (AlgebraicGeometry.PresheafedSpace.forget.{u4, u3, u3} C _inst_2)) (CategoryTheory.Limits.hasColimitOfHasColimitsOfShape.{u1, u2, u3, succ u3} TopCat.{u3} instTopCatLargeCategory.{u3} J _inst_1 _inst_3 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, max u4 (succ u3), succ u3} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u4, u3, u3} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u4, u3, u3} C _inst_2) TopCat.{u3} instTopCatLargeCategory.{u3} F (AlgebraicGeometry.PresheafedSpace.forget.{u4, u3, u3} C _inst_2))))))
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.pushforward_diagram_to_colimit AlgebraicGeometry.PresheafedSpace.pushforwardDiagramToColimitₓ'. -/
/-- Given a diagram of presheafed spaces,
we can push all the presheaves forward to the colimit `X` of the underlying topological spaces,
obtaining a diagram in `(presheaf C X)ᵒᵖ`.
-/
@[simps]
def pushforwardDiagramToColimit (F : J ⥤ PresheafedSpace.{v} C) :
    J ⥤ (Presheaf C (colimit (F ⋙ PresheafedSpace.forget C)))ᵒᵖ
    where
  obj j := op (colimit.ι (F ⋙ PresheafedSpace.forget C) j _* (F.obj j).Presheaf)
  map j j' f :=
    (pushforwardMap (colimit.ι (F ⋙ PresheafedSpace.forget C) j') (F.map f).c ≫
        (Pushforward.comp (F.obj j).Presheaf ((F ⋙ PresheafedSpace.forget C).map f)
              (colimit.ι (F ⋙ PresheafedSpace.forget C) j')).inv ≫
          (pushforwardEq (colimit.w (F ⋙ PresheafedSpace.forget C) f) (F.obj j).Presheaf).Hom).op
  map_id' j := by
    apply (op_equiv _ _).Injective
    ext U
    induction U using Opposite.rec'
    cases U
    dsimp; simp; dsimp; simp
  map_comp' j₁ j₂ j₃ f g := by
    apply (op_equiv _ _).Injective
    ext U
    dsimp
    simp only [map_comp_c_app, id.def, eq_to_hom_op, pushforward_map_app, eq_to_hom_map, assoc,
      id_comp, pushforward.comp_inv_app, pushforward_eq_hom_app]
    dsimp
    simp only [eq_to_hom_trans, id_comp]
    congr 1
    -- The key fact is `(F.map f).c.congr`,
    -- which allows us in rewrite in the argument of `(F.map f).c.app`.
    rw [(F.map f).c.congr]
    -- Now we pick up the pieces. First, we say what we want to replace that open set by:
    pick_goal 3
    refine' op ((opens.map (colimit.ι (F ⋙ PresheafedSpace.forget C) j₂)).obj (unop U))
    -- Now we show the open sets are equal.
    swap
    · apply unop_injective
      rw [← opens.map_comp_obj]
      congr
      exact colimit.w (F ⋙ PresheafedSpace.forget C) g
    -- Finally, the original goal is now easy:
    swap
    · simp
      rfl
#align algebraic_geometry.PresheafedSpace.pushforward_diagram_to_colimit AlgebraicGeometry.PresheafedSpace.pushforwardDiagramToColimit

variable [∀ X : TopCat.{v}, HasLimitsOfShape Jᵒᵖ (X.Presheaf C)]

/- warning: algebraic_geometry.PresheafedSpace.colimit -> AlgebraicGeometry.PresheafedSpace.colimit is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] [_inst_3 : CategoryTheory.Limits.HasColimitsOfShape.{u1, u2, u3, succ u3} J _inst_1 TopCat.{u3} TopCat.largeCategory.{u3}] [_inst_4 : forall (X : TopCat.{u3}), CategoryTheory.Limits.HasLimitsOfShape.{u1, u2, u3, max u4 u3} (Opposite.{succ u2} J) (CategoryTheory.Category.opposite.{u1, u2} J _inst_1) (TopCat.Presheaf.{u3, u3, u4} C _inst_2 X) (TopCat.Presheaf.category.{u3, u3, u4} C _inst_2 X)], (CategoryTheory.Functor.{u1, u3, u2, max u4 (succ u3)} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u3, u3, u4} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u3, u4} C _inst_2)) -> (AlgebraicGeometry.PresheafedSpace.{u3, u3, u4} C _inst_2)
but is expected to have type
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] [_inst_3 : CategoryTheory.Limits.HasColimitsOfShape.{u1, u2, u3, succ u3} J _inst_1 TopCat.{u3} instTopCatLargeCategory.{u3}] [_inst_4 : forall (X : TopCat.{u3}), CategoryTheory.Limits.HasLimitsOfShape.{u1, u2, u3, max u4 u3} (Opposite.{succ u2} J) (CategoryTheory.Category.opposite.{u1, u2} J _inst_1) (TopCat.Presheaf.{u3, u3, u4} C _inst_2 X) (TopCat.instCategoryPresheaf.{u3, u3, u4} C _inst_2 X)], (CategoryTheory.Functor.{u1, u3, u2, max (succ u3) u4} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u4, u3, u3} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u4, u3, u3} C _inst_2)) -> (AlgebraicGeometry.PresheafedSpace.{u4, u3, u3} C _inst_2)
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.colimit AlgebraicGeometry.PresheafedSpace.colimitₓ'. -/
/-- Auxiliary definition for `PresheafedSpace.has_colimits`.
-/
def colimit (F : J ⥤ PresheafedSpace.{v} C) : PresheafedSpace C
    where
  carrier := colimit (F ⋙ PresheafedSpace.forget C)
  Presheaf := limit (pushforwardDiagramToColimit F).leftOp
#align algebraic_geometry.PresheafedSpace.colimit AlgebraicGeometry.PresheafedSpace.colimit

/- warning: algebraic_geometry.PresheafedSpace.colimit_carrier -> AlgebraicGeometry.PresheafedSpace.colimit_carrier is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] [_inst_3 : CategoryTheory.Limits.HasColimitsOfShape.{u1, u2, u3, succ u3} J _inst_1 TopCat.{u3} TopCat.largeCategory.{u3}] [_inst_4 : forall (X : TopCat.{u3}), CategoryTheory.Limits.HasLimitsOfShape.{u1, u2, u3, max u4 u3} (Opposite.{succ u2} J) (CategoryTheory.Category.opposite.{u1, u2} J _inst_1) (TopCat.Presheaf.{u3, u3, u4} C _inst_2 X) (TopCat.Presheaf.category.{u3, u3, u4} C _inst_2 X)] (F : CategoryTheory.Functor.{u1, u3, u2, max u4 (succ u3)} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u3, u3, u4} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u3, u4} C _inst_2)), Eq.{succ (succ u3)} TopCat.{u3} (AlgebraicGeometry.PresheafedSpace.carrier.{u3, u3, u4} C _inst_2 (AlgebraicGeometry.PresheafedSpace.colimit.{u1, u2, u3, u4} J _inst_1 C _inst_2 _inst_3 (fun (X : TopCat.{u3}) => _inst_4 X) F)) (CategoryTheory.Limits.colimit.{u1, u2, u3, succ u3} J _inst_1 TopCat.{u3} TopCat.largeCategory.{u3} (CategoryTheory.Functor.comp.{u1, u3, u3, u2, max u4 (succ u3), succ u3} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u3, u3, u4} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u3, u4} C _inst_2) TopCat.{u3} TopCat.largeCategory.{u3} F (AlgebraicGeometry.PresheafedSpace.forget.{u3, u4} C _inst_2)) (CategoryTheory.Limits.hasColimitOfHasColimitsOfShape.{u1, u2, u3, succ u3} TopCat.{u3} TopCat.largeCategory.{u3} J _inst_1 _inst_3 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, max u4 (succ u3), succ u3} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u3, u3, u4} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u3, u4} C _inst_2) TopCat.{u3} TopCat.largeCategory.{u3} F (AlgebraicGeometry.PresheafedSpace.forget.{u3, u4} C _inst_2))))
but is expected to have type
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] [_inst_3 : CategoryTheory.Limits.HasColimitsOfShape.{u1, u2, u3, succ u3} J _inst_1 TopCat.{u3} instTopCatLargeCategory.{u3}] [_inst_4 : forall (X : TopCat.{u3}), CategoryTheory.Limits.HasLimitsOfShape.{u1, u2, u3, max u4 u3} (Opposite.{succ u2} J) (CategoryTheory.Category.opposite.{u1, u2} J _inst_1) (TopCat.Presheaf.{u3, u3, u4} C _inst_2 X) (TopCat.instCategoryPresheaf.{u3, u3, u4} C _inst_2 X)] (F : CategoryTheory.Functor.{u1, u3, u2, max (succ u3) u4} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u4, u3, u3} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u4, u3, u3} C _inst_2)), Eq.{succ (succ u3)} TopCat.{u3} (AlgebraicGeometry.PresheafedSpace.carrier.{u4, u3, u3} C _inst_2 (AlgebraicGeometry.PresheafedSpace.colimit.{u1, u2, u3, u4} J _inst_1 C _inst_2 _inst_3 (fun (X : TopCat.{u3}) => _inst_4 X) F)) (CategoryTheory.Limits.colimit.{u1, u2, u3, succ u3} J _inst_1 TopCat.{u3} instTopCatLargeCategory.{u3} (CategoryTheory.Functor.comp.{u1, u3, u3, u2, max u4 (succ u3), succ u3} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u4, u3, u3} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u4, u3, u3} C _inst_2) TopCat.{u3} instTopCatLargeCategory.{u3} F (AlgebraicGeometry.PresheafedSpace.forget.{u4, u3, u3} C _inst_2)) (CategoryTheory.Limits.hasColimitOfHasColimitsOfShape.{u1, u2, u3, succ u3} TopCat.{u3} instTopCatLargeCategory.{u3} J _inst_1 _inst_3 (CategoryTheory.Functor.comp.{u1, u3, u3, u2, max u4 (succ u3), succ u3} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u4, u3, u3} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u4, u3, u3} C _inst_2) TopCat.{u3} instTopCatLargeCategory.{u3} F (AlgebraicGeometry.PresheafedSpace.forget.{u4, u3, u3} C _inst_2))))
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.colimit_carrier AlgebraicGeometry.PresheafedSpace.colimit_carrierₓ'. -/
@[simp]
theorem colimit_carrier (F : J ⥤ PresheafedSpace.{v} C) :
    (colimit F).carrier = Limits.colimit (F ⋙ PresheafedSpace.forget C) :=
  rfl
#align algebraic_geometry.PresheafedSpace.colimit_carrier AlgebraicGeometry.PresheafedSpace.colimit_carrier

/- warning: algebraic_geometry.PresheafedSpace.colimit_presheaf -> AlgebraicGeometry.PresheafedSpace.colimit_presheaf is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.colimit_presheaf AlgebraicGeometry.PresheafedSpace.colimit_presheafₓ'. -/
@[simp]
theorem colimit_presheaf (F : J ⥤ PresheafedSpace.{v} C) :
    (colimit F).Presheaf = limit (pushforwardDiagramToColimit F).leftOp :=
  rfl
#align algebraic_geometry.PresheafedSpace.colimit_presheaf AlgebraicGeometry.PresheafedSpace.colimit_presheaf

/- warning: algebraic_geometry.PresheafedSpace.colimit_cocone -> AlgebraicGeometry.PresheafedSpace.colimitCocone is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] [_inst_3 : CategoryTheory.Limits.HasColimitsOfShape.{u1, u2, u3, succ u3} J _inst_1 TopCat.{u3} TopCat.largeCategory.{u3}] [_inst_4 : forall (X : TopCat.{u3}), CategoryTheory.Limits.HasLimitsOfShape.{u1, u2, u3, max u4 u3} (Opposite.{succ u2} J) (CategoryTheory.Category.opposite.{u1, u2} J _inst_1) (TopCat.Presheaf.{u3, u3, u4} C _inst_2 X) (TopCat.Presheaf.category.{u3, u3, u4} C _inst_2 X)] (F : CategoryTheory.Functor.{u1, u3, u2, max u4 (succ u3)} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u3, u3, u4} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u3, u4} C _inst_2)), CategoryTheory.Limits.Cocone.{u1, u3, u2, max u4 (succ u3)} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u3, u3, u4} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u3, u4} C _inst_2) F
but is expected to have type
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] [_inst_3 : CategoryTheory.Limits.HasColimitsOfShape.{u1, u2, u3, succ u3} J _inst_1 TopCat.{u3} instTopCatLargeCategory.{u3}] [_inst_4 : forall (X : TopCat.{u3}), CategoryTheory.Limits.HasLimitsOfShape.{u1, u2, u3, max u4 u3} (Opposite.{succ u2} J) (CategoryTheory.Category.opposite.{u1, u2} J _inst_1) (TopCat.Presheaf.{u3, u3, u4} C _inst_2 X) (TopCat.instCategoryPresheaf.{u3, u3, u4} C _inst_2 X)] (F : CategoryTheory.Functor.{u1, u3, u2, max (succ u3) u4} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u4, u3, u3} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u4, u3, u3} C _inst_2)), CategoryTheory.Limits.Cocone.{u1, u3, u2, max u4 (succ u3)} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u4, u3, u3} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u4, u3, u3} C _inst_2) F
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.colimit_cocone AlgebraicGeometry.PresheafedSpace.colimitCoconeₓ'. -/
/-- Auxiliary definition for `PresheafedSpace.has_colimits`.
-/
@[simps]
def colimitCocone (F : J ⥤ PresheafedSpace.{v} C) : Cocone F
    where
  pt := colimit F
  ι :=
    { app := fun j =>
        { base := colimit.ι (F ⋙ PresheafedSpace.forget C) j
          c := limit.π _ (op j) }
      naturality' := fun j j' f => by
        fapply PresheafedSpace.ext
        · ext x
          exact colimit.w_apply (F ⋙ PresheafedSpace.forget C) f x
        · ext U
          induction U using Opposite.rec'
          cases U
          dsimp
          simp only [PresheafedSpace.id_c_app, eq_to_hom_op, eq_to_hom_map, assoc,
            pushforward.comp_inv_app]
          rw [← congr_arg nat_trans.app (limit.w (pushforward_diagram_to_colimit F).leftOp f.op)]
          dsimp
          simp only [eq_to_hom_op, eq_to_hom_map, assoc, id_comp, pushforward.comp_inv_app]
          congr
          dsimp
          simp only [id_comp]
          simpa }
#align algebraic_geometry.PresheafedSpace.colimit_cocone AlgebraicGeometry.PresheafedSpace.colimitCocone

variable [HasLimitsOfShape Jᵒᵖ C]

namespace ColimitCoconeIsColimit

/- warning: algebraic_geometry.PresheafedSpace.colimit_cocone_is_colimit.desc_c_app -> AlgebraicGeometry.PresheafedSpace.ColimitCoconeIsColimit.descCApp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.colimit_cocone_is_colimit.desc_c_app AlgebraicGeometry.PresheafedSpace.ColimitCoconeIsColimit.descCAppₓ'. -/
/-- Auxiliary definition for `PresheafedSpace.colimit_cocone_is_colimit`.
-/
def descCApp (F : J ⥤ PresheafedSpace.{v} C) (s : Cocone F) (U : (Opens ↥s.pt.carrier)ᵒᵖ) :
    s.pt.Presheaf.obj U ⟶
      (colimit.desc (F ⋙ PresheafedSpace.forget C) ((PresheafedSpace.forget C).mapCocone s) _*
            limit (pushforwardDiagramToColimit F).leftOp).obj
        U :=
  by
  refine'
    limit.lift _
        { pt := s.X.presheaf.obj U
          π :=
            { app := fun j => _
              naturality' := fun j j' f => _ } } ≫
      (limit_obj_iso_limit_comp_evaluation _ _).inv
  -- We still need to construct the `app` and `naturality'` fields omitted above.
  · refine' (s.ι.app (unop j)).c.app U ≫ (F.obj (unop j)).Presheaf.map (eq_to_hom _)
    dsimp
    rw [← opens.map_comp_obj]
    simp
  · rw [PresheafedSpace.congr_app (s.w f.unop).symm U]
    dsimp
    have w :=
      functor.congr_obj
        (congr_arg opens.map (colimit.ι_desc ((PresheafedSpace.forget C).mapCocone s) (unop j)))
        (unop U)
    simp only [opens.map_comp_obj_unop] at w
    replace w := congr_arg op w
    have w' := nat_trans.congr (F.map f.unop).c w
    rw [w']
    dsimp
    simp
    dsimp
    simp
#align algebraic_geometry.PresheafedSpace.colimit_cocone_is_colimit.desc_c_app AlgebraicGeometry.PresheafedSpace.ColimitCoconeIsColimit.descCApp

/- warning: algebraic_geometry.PresheafedSpace.colimit_cocone_is_colimit.desc_c_naturality -> AlgebraicGeometry.PresheafedSpace.ColimitCoconeIsColimit.desc_c_naturality is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.colimit_cocone_is_colimit.desc_c_naturality AlgebraicGeometry.PresheafedSpace.ColimitCoconeIsColimit.desc_c_naturalityₓ'. -/
theorem desc_c_naturality (F : J ⥤ PresheafedSpace.{v} C) (s : Cocone F)
    {U V : (Opens ↥s.pt.carrier)ᵒᵖ} (i : U ⟶ V) :
    s.pt.Presheaf.map i ≫ descCApp F s V =
      descCApp F s U ≫
        (colimit.desc (F ⋙ forget C) ((forget C).mapCocone s) _* (colimitCocone F).pt.Presheaf).map
          i :=
  by
  dsimp [desc_c_app]
  ext
  simp only [limit.lift_π, nat_trans.naturality, limit.lift_π_assoc, eq_to_hom_map, assoc,
    pushforward_obj_map, nat_trans.naturality_assoc, op_map,
    limit_obj_iso_limit_comp_evaluation_inv_π_app_assoc,
    limit_obj_iso_limit_comp_evaluation_inv_π_app]
  dsimp
  have w :=
    functor.congr_hom
      (congr_arg opens.map (colimit.ι_desc ((PresheafedSpace.forget C).mapCocone s) (unop j)))
      i.unop
  simp only [opens.map_comp_map] at w
  replace w := congr_arg Quiver.Hom.op w
  rw [w]
  dsimp; simp
#align algebraic_geometry.PresheafedSpace.colimit_cocone_is_colimit.desc_c_naturality AlgebraicGeometry.PresheafedSpace.ColimitCoconeIsColimit.desc_c_naturality

/- warning: algebraic_geometry.PresheafedSpace.colimit_cocone_is_colimit.desc -> AlgebraicGeometry.PresheafedSpace.ColimitCoconeIsColimit.desc is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] [_inst_3 : CategoryTheory.Limits.HasColimitsOfShape.{u1, u2, u3, succ u3} J _inst_1 TopCat.{u3} TopCat.largeCategory.{u3}] [_inst_4 : forall (X : TopCat.{u3}), CategoryTheory.Limits.HasLimitsOfShape.{u1, u2, u3, max u4 u3} (Opposite.{succ u2} J) (CategoryTheory.Category.opposite.{u1, u2} J _inst_1) (TopCat.Presheaf.{u3, u3, u4} C _inst_2 X) (TopCat.Presheaf.category.{u3, u3, u4} C _inst_2 X)] [_inst_5 : CategoryTheory.Limits.HasLimitsOfShape.{u1, u2, u3, u4} (Opposite.{succ u2} J) (CategoryTheory.Category.opposite.{u1, u2} J _inst_1) C _inst_2] (F : CategoryTheory.Functor.{u1, u3, u2, max u4 (succ u3)} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u3, u3, u4} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u3, u4} C _inst_2)) (s : CategoryTheory.Limits.Cocone.{u1, u3, u2, max u4 (succ u3)} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u3, u3, u4} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u3, u4} C _inst_2) F), Quiver.Hom.{succ u3, max u4 (succ u3)} (AlgebraicGeometry.PresheafedSpace.{u3, u3, u4} C _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{u3, max u4 (succ u3)} (AlgebraicGeometry.PresheafedSpace.{u3, u3, u4} C _inst_2) (CategoryTheory.Category.toCategoryStruct.{u3, max u4 (succ u3)} (AlgebraicGeometry.PresheafedSpace.{u3, u3, u4} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u3, u4} C _inst_2))) (AlgebraicGeometry.PresheafedSpace.colimit.{u1, u2, u3, u4} J _inst_1 C _inst_2 _inst_3 (AlgebraicGeometry.PresheafedSpace.ColimitCoconeIsColimit.desc._proof_1.{u4, u2, u3, u1} J _inst_1 C _inst_2 _inst_4) F) (CategoryTheory.Limits.Cocone.pt.{u1, u3, u2, max u4 (succ u3)} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u3, u3, u4} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u3, u4} C _inst_2) F s)
but is expected to have type
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] [_inst_3 : CategoryTheory.Limits.HasColimitsOfShape.{u1, u2, u3, succ u3} J _inst_1 TopCat.{u3} instTopCatLargeCategory.{u3}] [_inst_4 : forall (X : TopCat.{u3}), CategoryTheory.Limits.HasLimitsOfShape.{u1, u2, u3, max u4 u3} (Opposite.{succ u2} J) (CategoryTheory.Category.opposite.{u1, u2} J _inst_1) (TopCat.Presheaf.{u3, u3, u4} C _inst_2 X) (TopCat.instCategoryPresheaf.{u3, u3, u4} C _inst_2 X)] [_inst_5 : CategoryTheory.Limits.HasLimitsOfShape.{u1, u2, u3, u4} (Opposite.{succ u2} J) (CategoryTheory.Category.opposite.{u1, u2} J _inst_1) C _inst_2] (F : CategoryTheory.Functor.{u1, u3, u2, max (succ u3) u4} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u4, u3, u3} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u4, u3, u3} C _inst_2)) (s : CategoryTheory.Limits.Cocone.{u1, u3, u2, max u4 (succ u3)} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u4, u3, u3} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u4, u3, u3} C _inst_2) F), Quiver.Hom.{succ u3, max u4 (succ u3)} (AlgebraicGeometry.PresheafedSpace.{u4, u3, u3} C _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{u3, max u4 (succ u3)} (AlgebraicGeometry.PresheafedSpace.{u4, u3, u3} C _inst_2) (CategoryTheory.Category.toCategoryStruct.{u3, max u4 (succ u3)} (AlgebraicGeometry.PresheafedSpace.{u4, u3, u3} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u4, u3, u3} C _inst_2))) (AlgebraicGeometry.PresheafedSpace.colimit.{u1, u2, u3, u4} J _inst_1 C _inst_2 _inst_3 (fun (X : TopCat.{u3}) => _inst_4 X) F) (CategoryTheory.Limits.Cocone.pt.{u1, u3, u2, max u4 (succ u3)} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u4, u3, u3} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u4, u3, u3} C _inst_2) F s)
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.colimit_cocone_is_colimit.desc AlgebraicGeometry.PresheafedSpace.ColimitCoconeIsColimit.descₓ'. -/
/-- Auxiliary definition for `PresheafedSpace.colimit_cocone_is_colimit`.
-/
def desc (F : J ⥤ PresheafedSpace.{v} C) (s : Cocone F) : colimit F ⟶ s.pt
    where
  base := colimit.desc (F ⋙ PresheafedSpace.forget C) ((PresheafedSpace.forget C).mapCocone s)
  c :=
    { app := fun U => descCApp F s U
      naturality' := fun U V i => desc_c_naturality F s i }
#align algebraic_geometry.PresheafedSpace.colimit_cocone_is_colimit.desc AlgebraicGeometry.PresheafedSpace.ColimitCoconeIsColimit.desc

/- warning: algebraic_geometry.PresheafedSpace.colimit_cocone_is_colimit.desc_fac -> AlgebraicGeometry.PresheafedSpace.ColimitCoconeIsColimit.desc_fac is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.colimit_cocone_is_colimit.desc_fac AlgebraicGeometry.PresheafedSpace.ColimitCoconeIsColimit.desc_facₓ'. -/
theorem desc_fac (F : J ⥤ PresheafedSpace.{v} C) (s : Cocone F) (j : J) :
    (colimitCocone F).ι.app j ≫ desc F s = s.ι.app j :=
  by
  fapply PresheafedSpace.ext
  · simp [desc]
  · ext
    dsimp [desc, desc_c_app]
    simpa
#align algebraic_geometry.PresheafedSpace.colimit_cocone_is_colimit.desc_fac AlgebraicGeometry.PresheafedSpace.ColimitCoconeIsColimit.desc_fac

end ColimitCoconeIsColimit

open ColimitCoconeIsColimit

/- warning: algebraic_geometry.PresheafedSpace.colimit_cocone_is_colimit -> AlgebraicGeometry.PresheafedSpace.colimitCoconeIsColimit is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] [_inst_3 : CategoryTheory.Limits.HasColimitsOfShape.{u1, u2, u3, succ u3} J _inst_1 TopCat.{u3} TopCat.largeCategory.{u3}] [_inst_4 : forall (X : TopCat.{u3}), CategoryTheory.Limits.HasLimitsOfShape.{u1, u2, u3, max u4 u3} (Opposite.{succ u2} J) (CategoryTheory.Category.opposite.{u1, u2} J _inst_1) (TopCat.Presheaf.{u3, u3, u4} C _inst_2 X) (TopCat.Presheaf.category.{u3, u3, u4} C _inst_2 X)] [_inst_5 : CategoryTheory.Limits.HasLimitsOfShape.{u1, u2, u3, u4} (Opposite.{succ u2} J) (CategoryTheory.Category.opposite.{u1, u2} J _inst_1) C _inst_2] (F : CategoryTheory.Functor.{u1, u3, u2, max u4 (succ u3)} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u3, u3, u4} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u3, u4} C _inst_2)), CategoryTheory.Limits.IsColimit.{u1, u3, u2, max u4 (succ u3)} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u3, u3, u4} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u3, u4} C _inst_2) F (AlgebraicGeometry.PresheafedSpace.colimitCocone.{u1, u2, u3, u4} J _inst_1 C _inst_2 _inst_3 (AlgebraicGeometry.PresheafedSpace.colimitCoconeIsColimit._proof_1.{u4, u2, u3, u1} J _inst_1 C _inst_2 _inst_4) F)
but is expected to have type
  forall {J : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} J] {C : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} C] [_inst_3 : CategoryTheory.Limits.HasColimitsOfShape.{u1, u2, u3, succ u3} J _inst_1 TopCat.{u3} instTopCatLargeCategory.{u3}] [_inst_4 : forall (X : TopCat.{u3}), CategoryTheory.Limits.HasLimitsOfShape.{u1, u2, u3, max u4 u3} (Opposite.{succ u2} J) (CategoryTheory.Category.opposite.{u1, u2} J _inst_1) (TopCat.Presheaf.{u3, u3, u4} C _inst_2 X) (TopCat.instCategoryPresheaf.{u3, u3, u4} C _inst_2 X)] [_inst_5 : CategoryTheory.Limits.HasLimitsOfShape.{u1, u2, u3, u4} (Opposite.{succ u2} J) (CategoryTheory.Category.opposite.{u1, u2} J _inst_1) C _inst_2] (F : CategoryTheory.Functor.{u1, u3, u2, max (succ u3) u4} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u4, u3, u3} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u4, u3, u3} C _inst_2)), CategoryTheory.Limits.IsColimit.{u1, u3, u2, max u4 (succ u3)} J _inst_1 (AlgebraicGeometry.PresheafedSpace.{u4, u3, u3} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u4, u3, u3} C _inst_2) F (AlgebraicGeometry.PresheafedSpace.colimitCocone.{u1, u2, u3, u4} J _inst_1 C _inst_2 _inst_3 (fun (X : TopCat.{u3}) => _inst_4 X) F)
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.colimit_cocone_is_colimit AlgebraicGeometry.PresheafedSpace.colimitCoconeIsColimitₓ'. -/
/-- Auxiliary definition for `PresheafedSpace.has_colimits`.
-/
def colimitCoconeIsColimit (F : J ⥤ PresheafedSpace.{v} C) : IsColimit (colimitCocone F)
    where
  desc s := desc F s
  fac s := desc_fac F s
  uniq s m w :=
    by
    -- We need to use the identity on the continuous maps twice, so we prepare that first:
    have t :
      m.base =
        colimit.desc (F ⋙ PresheafedSpace.forget C) ((PresheafedSpace.forget C).mapCocone s) :=
      by
      apply CategoryTheory.Limits.colimit.hom_ext
      intro j
      apply ContinuousMap.ext
      intro x
      dsimp
      simp only [colimit.ι_desc_apply, map_cocone_ι_app]
      rw [← w j]
      simp
    fapply PresheafedSpace.ext
    -- could `ext` please not reorder goals?
    · exact t
    · ext (U j)
      dsimp [desc, desc_c_app]
      simp only [limit.lift_π, eq_to_hom_op, eq_to_hom_map, assoc,
        limit_obj_iso_limit_comp_evaluation_inv_π_app]
      rw [PresheafedSpace.congr_app (w (unop j)).symm U]
      dsimp
      have w := congr_arg op (functor.congr_obj (congr_arg opens.map t) (unop U))
      rw [nat_trans.congr (limit.π (pushforward_diagram_to_colimit F).leftOp j) w]
      simp
#align algebraic_geometry.PresheafedSpace.colimit_cocone_is_colimit AlgebraicGeometry.PresheafedSpace.colimitCoconeIsColimit

instance : HasColimitsOfShape J (PresheafedSpace.{v} C)
    where HasColimit F :=
    HasColimit.mk
      { Cocone := colimitCocone F
        IsColimit := colimitCoconeIsColimit F }

instance : PreservesColimitsOfShape J (PresheafedSpace.forget C)
    where PreservesColimit F :=
    preservesColimitOfPreservesColimitCocone (colimitCoconeIsColimit F)
      (by
        apply is_colimit.of_iso_colimit (colimit.is_colimit _)
        fapply cocones.ext
        · rfl
        · intro j
          dsimp
          simp)

/-- When `C` has limits, the category of presheaved spaces with values in `C` itself has colimits.
-/
instance [HasLimits C] : HasColimits (PresheafedSpace.{v} C)
    where HasColimitsOfShape J 𝒥 :=
    {
      HasColimit := fun F =>
        has_colimit.mk
          { Cocone := colimit_cocone F
            IsColimit := colimit_cocone_is_colimit F } }

/- warning: algebraic_geometry.PresheafedSpace.forget_preserves_colimits -> AlgebraicGeometry.PresheafedSpace.forgetPreservesColimits is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} C] [_inst_6 : CategoryTheory.Limits.HasLimits.{u1, u2} C _inst_2], CategoryTheory.Limits.PreservesColimits.{u1, u1, max u2 (succ u1), succ u1} (AlgebraicGeometry.PresheafedSpace.{u1, u1, u2} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u1, u2} C _inst_2) TopCat.{u1} TopCat.largeCategory.{u1} (AlgebraicGeometry.PresheafedSpace.forget.{u1, u2} C _inst_2)
but is expected to have type
  forall {C : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u1, u2} C] [_inst_6 : CategoryTheory.Limits.HasLimits.{u1, u2} C _inst_2], CategoryTheory.Limits.PreservesColimits.{u1, u1, max (max u2 u1) (succ u1), succ u1} (AlgebraicGeometry.PresheafedSpace.{u2, u1, u1} C _inst_2) (AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces.{u2, u1, u1} C _inst_2) TopCat.{u1} instTopCatLargeCategory.{u1} (AlgebraicGeometry.PresheafedSpace.forget.{u2, u1, u1} C _inst_2)
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.forget_preserves_colimits AlgebraicGeometry.PresheafedSpace.forgetPreservesColimitsₓ'. -/
/-- The underlying topological space of a colimit of presheaved spaces is
the colimit of the underlying topological spaces.
-/
instance forgetPreservesColimits [HasLimits C] : PreservesColimits (PresheafedSpace.forget C)
    where PreservesColimitsOfShape J 𝒥 :=
    {
      PreservesColimit := fun F =>
        preserves_colimit_of_preserves_colimit_cocone (colimit_cocone_is_colimit F)
          (by
            apply is_colimit.of_iso_colimit (colimit.is_colimit _)
            fapply cocones.ext
            · rfl
            · intro j
              dsimp
              simp) }
#align algebraic_geometry.PresheafedSpace.forget_preserves_colimits AlgebraicGeometry.PresheafedSpace.forgetPreservesColimits

/- warning: algebraic_geometry.PresheafedSpace.colimit_presheaf_obj_iso_componentwise_limit -> AlgebraicGeometry.PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.colimit_presheaf_obj_iso_componentwise_limit AlgebraicGeometry.PresheafedSpace.colimitPresheafObjIsoComponentwiseLimitₓ'. -/
/-- The components of the colimit of a diagram of `PresheafedSpace C` is obtained
via taking componentwise limits.
-/
def colimitPresheafObjIsoComponentwiseLimit (F : J ⥤ PresheafedSpace.{v} C) [HasColimit F]
    (U : Opens (Limits.colimit F).carrier) :
    (Limits.colimit F).Presheaf.obj (op U) ≅ limit (componentwiseDiagram F U) :=
  by
  refine'
    ((sheaf_iso_of_iso (colimit.iso_colimit_cocone ⟨_, colimit_cocone_is_colimit F⟩).symm).app
          (op U)).trans
      _
  refine' (limit_obj_iso_limit_comp_evaluation _ _).trans (limits.lim.map_iso _)
  fapply nat_iso.of_components
  · intro X
    refine' (F.obj (unop X)).Presheaf.mapIso (eq_to_iso _)
    simp only [functor.op_obj, unop_op, op_inj_iff, opens.map_coe, SetLike.ext'_iff,
      Set.preimage_preimage]
    simp_rw [← comp_app]
    congr 2
    exact ι_preserves_colimits_iso_inv (forget C) F (unop X)
  · intro X Y f
    change ((F.map f.unop).c.app _ ≫ _ ≫ _) ≫ (F.obj (unop Y)).Presheaf.map _ = _ ≫ _
    rw [TopCat.Presheaf.Pushforward.comp_inv_app]
    erw [category.id_comp]
    rw [category.assoc]
    erw [← (F.obj (unop Y)).Presheaf.map_comp, (F.map f.unop).c.naturality_assoc, ←
      (F.obj (unop Y)).Presheaf.map_comp]
    congr
#align algebraic_geometry.PresheafedSpace.colimit_presheaf_obj_iso_componentwise_limit AlgebraicGeometry.PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit

/- warning: algebraic_geometry.PresheafedSpace.colimit_presheaf_obj_iso_componentwise_limit_inv_ι_app -> AlgebraicGeometry.PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_inv_ι_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.colimit_presheaf_obj_iso_componentwise_limit_inv_ι_app AlgebraicGeometry.PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_inv_ι_appₓ'. -/
@[simp]
theorem colimitPresheafObjIsoComponentwiseLimit_inv_ι_app (F : J ⥤ PresheafedSpace.{v} C)
    (U : Opens (Limits.colimit F).carrier) (j : J) :
    (colimitPresheafObjIsoComponentwiseLimit F U).inv ≫ (colimit.ι F j).c.app (op U) =
      limit.π _ (op j) :=
  by
  delta colimit_presheaf_obj_iso_componentwise_limit
  rw [iso.trans_inv, iso.trans_inv, iso.app_inv, sheaf_iso_of_iso_inv, pushforward_to_of_iso_app,
    congr_app (iso.symm_inv _)]
  simp_rw [category.assoc]
  rw [← functor.map_comp_assoc, nat_trans.naturality]
  erw [← comp_c_app_assoc]
  rw [congr_app (colimit.iso_colimit_cocone_ι_hom _ _)]
  simp_rw [category.assoc]
  erw [limit_obj_iso_limit_comp_evaluation_inv_π_app_assoc, lim_map_π_assoc]
  convert category.comp_id _
  erw [← (F.obj j).Presheaf.map_id]
  iterate 2 erw [← (F.obj j).Presheaf.map_comp]
  congr
#align algebraic_geometry.PresheafedSpace.colimit_presheaf_obj_iso_componentwise_limit_inv_ι_app AlgebraicGeometry.PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_inv_ι_app

/- warning: algebraic_geometry.PresheafedSpace.colimit_presheaf_obj_iso_componentwise_limit_hom_π -> AlgebraicGeometry.PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_hom_π is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_geometry.PresheafedSpace.colimit_presheaf_obj_iso_componentwise_limit_hom_π AlgebraicGeometry.PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_hom_πₓ'. -/
@[simp]
theorem colimitPresheafObjIsoComponentwiseLimit_hom_π (F : J ⥤ PresheafedSpace.{v} C)
    (U : Opens (Limits.colimit F).carrier) (j : J) :
    (colimitPresheafObjIsoComponentwiseLimit F U).Hom ≫ limit.π _ (op j) =
      (colimit.ι F j).c.app (op U) :=
  by rw [← iso.eq_inv_comp, colimit_presheaf_obj_iso_componentwise_limit_inv_ι_app]
#align algebraic_geometry.PresheafedSpace.colimit_presheaf_obj_iso_componentwise_limit_hom_π AlgebraicGeometry.PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_hom_π

end PresheafedSpace

end AlgebraicGeometry

