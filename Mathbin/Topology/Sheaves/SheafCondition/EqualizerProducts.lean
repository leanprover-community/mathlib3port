/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module topology.sheaves.sheaf_condition.equalizer_products
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Shapes.Equalizers
import Mathbin.CategoryTheory.Limits.Shapes.Products
import Mathbin.Topology.Sheaves.SheafCondition.PairwiseIntersections

/-!
# The sheaf condition in terms of an equalizer of products

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Here we set up the machinery for the "usual" definition of the sheaf condition,
e.g. as in https://stacks.math.columbia.edu/tag/0072
in terms of an equalizer diagram where the two objects are
`∏ F.obj (U i)` and `∏ F.obj (U i) ⊓ (U j)`.

We show that this sheaf condition is equivalent to the `pairwise_intersections` sheaf condition when
the presheaf is valued in a category with products, and thereby equivalent to the default sheaf
condition.
-/


universe v' v u

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

open TopologicalSpace

open Opposite

open TopologicalSpace.Opens

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasProducts.{v'} C]

variable {X : TopCat.{v'}} (F : Presheaf C X) {ι : Type v'} (U : ι → Opens X)

namespace Presheaf

namespace SheafConditionEqualizerProducts

#print TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens /-
/-- The product of the sections of a presheaf over a family of open sets. -/
def piOpens : C :=
  ∏ fun i : ι => F.obj (op (U i))
#align Top.presheaf.sheaf_condition_equalizer_products.pi_opens TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens
-/

#print TopCat.Presheaf.SheafConditionEqualizerProducts.piInters /-
/-- The product of the sections of a presheaf over the pairwise intersections of
a family of open sets.
-/
def piInters : C :=
  ∏ fun p : ι × ι => F.obj (op (U p.1 ⊓ U p.2))
#align Top.presheaf.sheaf_condition_equalizer_products.pi_inters TopCat.Presheaf.SheafConditionEqualizerProducts.piInters
-/

#print TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes /-
/-- The morphism `Π F.obj (U i) ⟶ Π F.obj (U i) ⊓ (U j)` whose components
are given by the restriction maps from `U i` to `U i ⊓ U j`.
-/
def leftRes : piOpens F U ⟶ piInters.{v'} F U :=
  Pi.lift fun p : ι × ι => Pi.π _ p.1 ≫ F.map (inf_le_left (U p.1) (U p.2)).op
#align Top.presheaf.sheaf_condition_equalizer_products.left_res TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes
-/

#print TopCat.Presheaf.SheafConditionEqualizerProducts.rightRes /-
/-- The morphism `Π F.obj (U i) ⟶ Π F.obj (U i) ⊓ (U j)` whose components
are given by the restriction maps from `U j` to `U i ⊓ U j`.
-/
def rightRes : piOpens F U ⟶ piInters.{v'} F U :=
  Pi.lift fun p : ι × ι => Pi.π _ p.2 ≫ F.map (inf_le_right (U p.1) (U p.2)).op
#align Top.presheaf.sheaf_condition_equalizer_products.right_res TopCat.Presheaf.SheafConditionEqualizerProducts.rightRes
-/

/- warning: Top.presheaf.sheaf_condition_equalizer_products.res -> TopCat.Presheaf.SheafConditionEqualizerProducts.res is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] [_inst_2 : CategoryTheory.Limits.HasProducts.{u1, u2, u3} C _inst_1] {X : TopCat.{u1}} (F : TopCat.Presheaf.{u1, u2, u3} C _inst_1 X) {ι : Type.{u1}} (U : ι -> (TopologicalSpace.Opens.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (TopCat.topologicalSpace.{u1} X))), Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.obj.{u1, u2, u1, u3} (Opposite.{succ u1} (TopologicalSpace.Opens.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (TopCat.topologicalSpace.{u1} X))) (CategoryTheory.Category.opposite.{u1, u1} (TopologicalSpace.Opens.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (TopCat.topologicalSpace.{u1} X)) (Preorder.smallCategory.{u1} (TopologicalSpace.Opens.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (TopCat.topologicalSpace.{u1} X)) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (TopCat.topologicalSpace.{u1} X)) (SetLike.partialOrder.{u1, u1} (TopologicalSpace.Opens.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (TopCat.topologicalSpace.{u1} X)) (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (TopologicalSpace.Opens.setLike.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (TopCat.topologicalSpace.{u1} X)))))) C _inst_1 F (Opposite.op.{succ u1} (TopologicalSpace.Opens.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (TopCat.topologicalSpace.{u1} X)) (iSup.{u1, succ u1} (TopologicalSpace.Opens.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (TopCat.topologicalSpace.{u1} X)) (ConditionallyCompleteLattice.toHasSup.{u1} (TopologicalSpace.Opens.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (TopCat.topologicalSpace.{u1} X)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (TopCat.topologicalSpace.{u1} X)) (TopologicalSpace.Opens.completeLattice.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (TopCat.topologicalSpace.{u1} X)))) ι U))) (TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens.{u1, u2, u3} C _inst_1 (TopCat.Presheaf.SheafConditionEqualizerProducts.res._proof_1.{u3, u2, u1} C _inst_1 _inst_2) X F ι U)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] [_inst_2 : CategoryTheory.Limits.HasProducts.{u1, u2, u3} C _inst_1] {X : TopCat.{u1}} (F : TopCat.Presheaf.{u1, u2, u3} C _inst_1 X) {ι : Type.{u1}} (U : ι -> (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X))), Quiver.Hom.{succ u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (Prefunctor.obj.{succ u1, succ u2, u1, u3} (Opposite.{succ u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X))) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (Opposite.{succ u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X))) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (Opposite.{succ u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X))) (CategoryTheory.Category.opposite.{u1, u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X)) (Preorder.smallCategory.{u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X)) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X)) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X)) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X))))))))) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u1, u3} (Opposite.{succ u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X))) (CategoryTheory.Category.opposite.{u1, u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X)) (Preorder.smallCategory.{u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X)) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X)) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X)) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X))))))) C _inst_1 F) (Opposite.op.{succ u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X)) (iSup.{u1, succ u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X)) (ConditionallyCompleteLattice.toSupSet.{u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X)) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X)))) ι U))) (TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens.{u1, u2, u3} C _inst_1 (fun (J : Type.{u1}) => _inst_2 J) X F ι U)
Case conversion may be inaccurate. Consider using '#align Top.presheaf.sheaf_condition_equalizer_products.res TopCat.Presheaf.SheafConditionEqualizerProducts.resₓ'. -/
/-- The morphism `F.obj U ⟶ Π F.obj (U i)` whose components
are given by the restriction maps from `U j` to `U i ⊓ U j`.
-/
def res : F.obj (op (iSup U)) ⟶ piOpens.{v'} F U :=
  Pi.lift fun i : ι => F.map (TopologicalSpace.Opens.leSupr U i).op
#align Top.presheaf.sheaf_condition_equalizer_products.res TopCat.Presheaf.SheafConditionEqualizerProducts.res

/- warning: Top.presheaf.sheaf_condition_equalizer_products.res_π -> TopCat.Presheaf.SheafConditionEqualizerProducts.res_π is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Top.presheaf.sheaf_condition_equalizer_products.res_π TopCat.Presheaf.SheafConditionEqualizerProducts.res_πₓ'. -/
@[simp, elementwise]
theorem res_π (i : ι) : res F U ≫ limit.π _ ⟨i⟩ = F.map (Opens.leSupr U i).op := by
  rw [res, limit.lift_π, fan.mk_π_app]
#align Top.presheaf.sheaf_condition_equalizer_products.res_π TopCat.Presheaf.SheafConditionEqualizerProducts.res_π

/- warning: Top.presheaf.sheaf_condition_equalizer_products.w -> TopCat.Presheaf.SheafConditionEqualizerProducts.w is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Top.presheaf.sheaf_condition_equalizer_products.w TopCat.Presheaf.SheafConditionEqualizerProducts.wₓ'. -/
@[elementwise]
theorem w : res F U ≫ leftRes F U = res F U ≫ rightRes F U :=
  by
  dsimp [res, left_res, right_res]
  ext
  simp only [limit.lift_π, limit.lift_π_assoc, fan.mk_π_app, category.assoc]
  rw [← F.map_comp]
  rw [← F.map_comp]
  congr
#align Top.presheaf.sheaf_condition_equalizer_products.w TopCat.Presheaf.SheafConditionEqualizerProducts.w

#print TopCat.Presheaf.SheafConditionEqualizerProducts.diagram /-
/-- The equalizer diagram for the sheaf condition.
-/
@[reducible]
def diagram : WalkingParallelPair ⥤ C :=
  parallelPair (leftRes.{v'} F U) (rightRes F U)
#align Top.presheaf.sheaf_condition_equalizer_products.diagram TopCat.Presheaf.SheafConditionEqualizerProducts.diagram
-/

#print TopCat.Presheaf.SheafConditionEqualizerProducts.fork /-
/-- The restriction map `F.obj U ⟶ Π F.obj (U i)` gives a cone over the equalizer diagram
for the sheaf condition. The sheaf condition asserts this cone is a limit cone.
-/
def fork : Fork.{v} (leftRes F U) (rightRes F U) :=
  Fork.ofι _ (w F U)
#align Top.presheaf.sheaf_condition_equalizer_products.fork TopCat.Presheaf.SheafConditionEqualizerProducts.fork
-/

/- warning: Top.presheaf.sheaf_condition_equalizer_products.fork_X -> TopCat.Presheaf.SheafConditionEqualizerProducts.fork_pt is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] [_inst_2 : CategoryTheory.Limits.HasProducts.{u1, u2, u3} C _inst_1] {X : TopCat.{u1}} (F : TopCat.Presheaf.{u1, u2, u3} C _inst_1 X) {ι : Type.{u1}} (U : ι -> (TopologicalSpace.Opens.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (TopCat.topologicalSpace.{u1} X))), Eq.{succ u3} C (CategoryTheory.Limits.Cone.pt.{0, u2, 0, u3} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u2, u3} C _inst_1 (TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens.{u1, u2, u3} C _inst_1 (TopCat.Presheaf.SheafConditionEqualizerProducts.fork._proof_1.{u3, u2, u1} C _inst_1 (fun (J : Type.{u1}) => _inst_2 J)) X F ι U) (TopCat.Presheaf.SheafConditionEqualizerProducts.piInters.{u1, u2, u3} C _inst_1 (TopCat.Presheaf.SheafConditionEqualizerProducts.fork._proof_2.{u3, u2, u1} C _inst_1 (fun (J : Type.{u1}) => _inst_2 J)) X F ι U) (TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes.{u1, u2, u3} C _inst_1 (TopCat.Presheaf.SheafConditionEqualizerProducts.fork._proof_3.{u3, u2, u1} C _inst_1 (fun (J : Type.{u1}) => _inst_2 J)) X F ι U) (TopCat.Presheaf.SheafConditionEqualizerProducts.rightRes.{u1, u2, u3} C _inst_1 (TopCat.Presheaf.SheafConditionEqualizerProducts.fork._proof_4.{u3, u2, u1} C _inst_1 (fun (J : Type.{u1}) => _inst_2 J)) X F ι U)) (TopCat.Presheaf.SheafConditionEqualizerProducts.fork.{u1, u2, u3} C _inst_1 (fun (J : Type.{u1}) => _inst_2 J) X F ι U)) (CategoryTheory.Functor.obj.{u1, u2, u1, u3} (Opposite.{succ u1} (TopologicalSpace.Opens.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (TopCat.topologicalSpace.{u1} X))) (CategoryTheory.Category.opposite.{u1, u1} (TopologicalSpace.Opens.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (TopCat.topologicalSpace.{u1} X)) (Preorder.smallCategory.{u1} (TopologicalSpace.Opens.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (TopCat.topologicalSpace.{u1} X)) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (TopCat.topologicalSpace.{u1} X)) (SetLike.partialOrder.{u1, u1} (TopologicalSpace.Opens.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (TopCat.topologicalSpace.{u1} X)) (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (TopologicalSpace.Opens.setLike.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (TopCat.topologicalSpace.{u1} X)))))) C _inst_1 F (Opposite.op.{succ u1} (TopologicalSpace.Opens.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (TopCat.topologicalSpace.{u1} X)) (iSup.{u1, succ u1} (TopologicalSpace.Opens.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (TopCat.topologicalSpace.{u1} X)) (ConditionallyCompleteLattice.toHasSup.{u1} (TopologicalSpace.Opens.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (TopCat.topologicalSpace.{u1} X)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (TopCat.topologicalSpace.{u1} X)) (TopologicalSpace.Opens.completeLattice.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (TopCat.topologicalSpace.{u1} X)))) ι U)))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] [_inst_2 : CategoryTheory.Limits.HasProducts.{u1, u2, u3} C _inst_1] {X : TopCat.{u1}} (F : TopCat.Presheaf.{u1, u2, u3} C _inst_1 X) {ι : Type.{u1}} (U : ι -> (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X))), Eq.{succ u3} C (CategoryTheory.Limits.Cone.pt.{0, u2, 0, u3} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1 (CategoryTheory.Limits.parallelPair.{u2, u3} C _inst_1 (TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens.{u1, u2, u3} C _inst_1 (fun (J : Type.{u1}) => _inst_2 J) X F ι U) (TopCat.Presheaf.SheafConditionEqualizerProducts.piInters.{u1, u2, u3} C _inst_1 (fun (J : Type.{u1}) => _inst_2 J) X F ι U) (TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes.{u1, u2, u3} C _inst_1 (fun (J : Type.{u1}) => _inst_2 J) X F ι U) (TopCat.Presheaf.SheafConditionEqualizerProducts.rightRes.{u1, u2, u3} C _inst_1 (fun (J : Type.{u1}) => _inst_2 J) X F ι U)) (TopCat.Presheaf.SheafConditionEqualizerProducts.fork.{u1, u2, u3} C _inst_1 (fun (J : Type.{u1}) => _inst_2 J) X F ι U)) (Prefunctor.obj.{succ u1, succ u2, u1, u3} (Opposite.{succ u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X))) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (Opposite.{succ u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X))) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (Opposite.{succ u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X))) (CategoryTheory.Category.opposite.{u1, u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X)) (Preorder.smallCategory.{u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X)) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X)) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X)) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X))))))))) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u1, u3} (Opposite.{succ u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X))) (CategoryTheory.Category.opposite.{u1, u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X)) (Preorder.smallCategory.{u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X)) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X)) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X)) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X))))))) C _inst_1 F) (Opposite.op.{succ u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X)) (iSup.{u1, succ u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X)) (ConditionallyCompleteLattice.toSupSet.{u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X)) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X)))) ι U)))
Case conversion may be inaccurate. Consider using '#align Top.presheaf.sheaf_condition_equalizer_products.fork_X TopCat.Presheaf.SheafConditionEqualizerProducts.fork_ptₓ'. -/
@[simp]
theorem fork_pt : (fork F U).pt = F.obj (op (iSup U)) :=
  rfl
#align Top.presheaf.sheaf_condition_equalizer_products.fork_X TopCat.Presheaf.SheafConditionEqualizerProducts.fork_pt

/- warning: Top.presheaf.sheaf_condition_equalizer_products.fork_ι -> TopCat.Presheaf.SheafConditionEqualizerProducts.fork_ι is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Top.presheaf.sheaf_condition_equalizer_products.fork_ι TopCat.Presheaf.SheafConditionEqualizerProducts.fork_ιₓ'. -/
@[simp]
theorem fork_ι : (fork F U).ι = res F U :=
  rfl
#align Top.presheaf.sheaf_condition_equalizer_products.fork_ι TopCat.Presheaf.SheafConditionEqualizerProducts.fork_ι

/- warning: Top.presheaf.sheaf_condition_equalizer_products.fork_π_app_walking_parallel_pair_zero -> TopCat.Presheaf.SheafConditionEqualizerProducts.fork_π_app_walkingParallelPair_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Top.presheaf.sheaf_condition_equalizer_products.fork_π_app_walking_parallel_pair_zero TopCat.Presheaf.SheafConditionEqualizerProducts.fork_π_app_walkingParallelPair_zeroₓ'. -/
@[simp]
theorem fork_π_app_walkingParallelPair_zero : (fork F U).π.app WalkingParallelPair.zero = res F U :=
  rfl
#align Top.presheaf.sheaf_condition_equalizer_products.fork_π_app_walking_parallel_pair_zero TopCat.Presheaf.SheafConditionEqualizerProducts.fork_π_app_walkingParallelPair_zero

/- warning: Top.presheaf.sheaf_condition_equalizer_products.fork_π_app_walking_parallel_pair_one -> TopCat.Presheaf.SheafConditionEqualizerProducts.fork_π_app_walkingParallelPair_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Top.presheaf.sheaf_condition_equalizer_products.fork_π_app_walking_parallel_pair_one TopCat.Presheaf.SheafConditionEqualizerProducts.fork_π_app_walkingParallelPair_oneₓ'. -/
@[simp]
theorem fork_π_app_walkingParallelPair_one :
    (fork F U).π.app WalkingParallelPair.one = res F U ≫ leftRes F U :=
  rfl
#align Top.presheaf.sheaf_condition_equalizer_products.fork_π_app_walking_parallel_pair_one TopCat.Presheaf.SheafConditionEqualizerProducts.fork_π_app_walkingParallelPair_one

variable {F} {G : Presheaf C X}

/- warning: Top.presheaf.sheaf_condition_equalizer_products.pi_opens.iso_of_iso -> TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens.isoOfIso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] [_inst_2 : CategoryTheory.Limits.HasProducts.{u1, u2, u3} C _inst_1] {X : TopCat.{u1}} {F : TopCat.Presheaf.{u1, u2, u3} C _inst_1 X} {ι : Type.{u1}} (U : ι -> (TopologicalSpace.Opens.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (TopCat.topologicalSpace.{u1} X))) {G : TopCat.Presheaf.{u1, u2, u3} C _inst_1 X}, (CategoryTheory.Iso.{max u1 u2, max u3 u2 u1} (TopCat.Presheaf.{u1, u2, u3} C _inst_1 X) (TopCat.Presheaf.category.{u2, u1, u3} C _inst_1 X) F G) -> (CategoryTheory.Iso.{u2, u3} C _inst_1 (TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens.{u1, u2, u3} C _inst_1 (TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens.isoOfIso._proof_1.{u3, u2, u1} C _inst_1 _inst_2) X F ι U) (TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens.{u1, u2, u3} C _inst_1 (TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens.isoOfIso._proof_2.{u3, u2, u1} C _inst_1 _inst_2) X G ι U))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] [_inst_2 : CategoryTheory.Limits.HasProducts.{u1, u2, u3} C _inst_1] {X : TopCat.{u1}} {F : TopCat.Presheaf.{u1, u2, u3} C _inst_1 X} {ι : Type.{u1}} (U : ι -> (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X))) {G : TopCat.Presheaf.{u1, u2, u3} C _inst_1 X}, (CategoryTheory.Iso.{max u2 u1, max (max u3 u2) u1} (TopCat.Presheaf.{u1, u2, u3} C _inst_1 X) (TopCat.instCategoryPresheaf.{u1, u2, u3} C _inst_1 X) F G) -> (CategoryTheory.Iso.{u2, u3} C _inst_1 (TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens.{u1, u2, u3} C _inst_1 (fun (J : Type.{u1}) => _inst_2 J) X F ι U) (TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens.{u1, u2, u3} C _inst_1 (fun (J : Type.{u1}) => _inst_2 J) X G ι U))
Case conversion may be inaccurate. Consider using '#align Top.presheaf.sheaf_condition_equalizer_products.pi_opens.iso_of_iso TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens.isoOfIsoₓ'. -/
/-- Isomorphic presheaves have isomorphic `pi_opens` for any cover `U`. -/
@[simp]
def piOpens.isoOfIso (α : F ≅ G) : piOpens F U ≅ piOpens.{v'} G U :=
  Pi.mapIso fun X => α.app _
#align Top.presheaf.sheaf_condition_equalizer_products.pi_opens.iso_of_iso TopCat.Presheaf.SheafConditionEqualizerProducts.piOpens.isoOfIso

/- warning: Top.presheaf.sheaf_condition_equalizer_products.pi_inters.iso_of_iso -> TopCat.Presheaf.SheafConditionEqualizerProducts.piInters.isoOfIso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] [_inst_2 : CategoryTheory.Limits.HasProducts.{u1, u2, u3} C _inst_1] {X : TopCat.{u1}} {F : TopCat.Presheaf.{u1, u2, u3} C _inst_1 X} {ι : Type.{u1}} (U : ι -> (TopologicalSpace.Opens.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (TopCat.topologicalSpace.{u1} X))) {G : TopCat.Presheaf.{u1, u2, u3} C _inst_1 X}, (CategoryTheory.Iso.{max u1 u2, max u3 u2 u1} (TopCat.Presheaf.{u1, u2, u3} C _inst_1 X) (TopCat.Presheaf.category.{u2, u1, u3} C _inst_1 X) F G) -> (CategoryTheory.Iso.{u2, u3} C _inst_1 (TopCat.Presheaf.SheafConditionEqualizerProducts.piInters.{u1, u2, u3} C _inst_1 (TopCat.Presheaf.SheafConditionEqualizerProducts.piInters.isoOfIso._proof_1.{u3, u2, u1} C _inst_1 _inst_2) X F ι U) (TopCat.Presheaf.SheafConditionEqualizerProducts.piInters.{u1, u2, u3} C _inst_1 (TopCat.Presheaf.SheafConditionEqualizerProducts.piInters.isoOfIso._proof_2.{u3, u2, u1} C _inst_1 _inst_2) X G ι U))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] [_inst_2 : CategoryTheory.Limits.HasProducts.{u1, u2, u3} C _inst_1] {X : TopCat.{u1}} {F : TopCat.Presheaf.{u1, u2, u3} C _inst_1 X} {ι : Type.{u1}} (U : ι -> (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X))) {G : TopCat.Presheaf.{u1, u2, u3} C _inst_1 X}, (CategoryTheory.Iso.{max u2 u1, max (max u3 u2) u1} (TopCat.Presheaf.{u1, u2, u3} C _inst_1 X) (TopCat.instCategoryPresheaf.{u1, u2, u3} C _inst_1 X) F G) -> (CategoryTheory.Iso.{u2, u3} C _inst_1 (TopCat.Presheaf.SheafConditionEqualizerProducts.piInters.{u1, u2, u3} C _inst_1 (fun (J : Type.{u1}) => _inst_2 J) X F ι U) (TopCat.Presheaf.SheafConditionEqualizerProducts.piInters.{u1, u2, u3} C _inst_1 (fun (J : Type.{u1}) => _inst_2 J) X G ι U))
Case conversion may be inaccurate. Consider using '#align Top.presheaf.sheaf_condition_equalizer_products.pi_inters.iso_of_iso TopCat.Presheaf.SheafConditionEqualizerProducts.piInters.isoOfIsoₓ'. -/
/-- Isomorphic presheaves have isomorphic `pi_inters` for any cover `U`. -/
@[simp]
def piInters.isoOfIso (α : F ≅ G) : piInters F U ≅ piInters.{v'} G U :=
  Pi.mapIso fun X => α.app _
#align Top.presheaf.sheaf_condition_equalizer_products.pi_inters.iso_of_iso TopCat.Presheaf.SheafConditionEqualizerProducts.piInters.isoOfIso

/- warning: Top.presheaf.sheaf_condition_equalizer_products.diagram.iso_of_iso -> TopCat.Presheaf.SheafConditionEqualizerProducts.diagram.isoOfIso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] [_inst_2 : CategoryTheory.Limits.HasProducts.{u1, u2, u3} C _inst_1] {X : TopCat.{u1}} {F : TopCat.Presheaf.{u1, u2, u3} C _inst_1 X} {ι : Type.{u1}} (U : ι -> (TopologicalSpace.Opens.{u1} (coeSort.{succ (succ u1), succ (succ u1)} TopCat.{u1} Type.{u1} TopCat.hasCoeToSort.{u1} X) (TopCat.topologicalSpace.{u1} X))) {G : TopCat.Presheaf.{u1, u2, u3} C _inst_1 X}, (CategoryTheory.Iso.{max u1 u2, max u3 u2 u1} (TopCat.Presheaf.{u1, u2, u3} C _inst_1 X) (TopCat.Presheaf.category.{u2, u1, u3} C _inst_1 X) F G) -> (CategoryTheory.Iso.{u2, max u2 u3} (CategoryTheory.Functor.{0, u2, 0, u3} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.category.{0, u2, 0, u3} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (TopCat.Presheaf.SheafConditionEqualizerProducts.diagram.{u1, u2, u3} C _inst_1 (TopCat.Presheaf.SheafConditionEqualizerProducts.diagram.isoOfIso._proof_1.{u3, u2, u1} C _inst_1 _inst_2) X F ι U) (TopCat.Presheaf.SheafConditionEqualizerProducts.diagram.{u1, u2, u3} C _inst_1 (TopCat.Presheaf.SheafConditionEqualizerProducts.diagram.isoOfIso._proof_2.{u3, u2, u1} C _inst_1 _inst_2) X G ι U))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] [_inst_2 : CategoryTheory.Limits.HasProducts.{u1, u2, u3} C _inst_1] {X : TopCat.{u1}} {F : TopCat.Presheaf.{u1, u2, u3} C _inst_1 X} {ι : Type.{u1}} (U : ι -> (TopologicalSpace.Opens.{u1} (CategoryTheory.Bundled.α.{u1, u1} TopologicalSpace.{u1} X) (TopCat.topologicalSpace_coe.{u1} X))) {G : TopCat.Presheaf.{u1, u2, u3} C _inst_1 X}, (CategoryTheory.Iso.{max u2 u1, max (max u3 u2) u1} (TopCat.Presheaf.{u1, u2, u3} C _inst_1 X) (TopCat.instCategoryPresheaf.{u1, u2, u3} C _inst_1 X) F G) -> (CategoryTheory.Iso.{u2, max u3 u2} (CategoryTheory.Functor.{0, u2, 0, u3} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (CategoryTheory.Functor.category.{0, u2, 0, u3} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory C _inst_1) (TopCat.Presheaf.SheafConditionEqualizerProducts.diagram.{u1, u2, u3} C _inst_1 (fun (J : Type.{u1}) => _inst_2 J) X F ι U) (TopCat.Presheaf.SheafConditionEqualizerProducts.diagram.{u1, u2, u3} C _inst_1 (fun (J : Type.{u1}) => _inst_2 J) X G ι U))
Case conversion may be inaccurate. Consider using '#align Top.presheaf.sheaf_condition_equalizer_products.diagram.iso_of_iso TopCat.Presheaf.SheafConditionEqualizerProducts.diagram.isoOfIsoₓ'. -/
/-- Isomorphic presheaves have isomorphic sheaf condition diagrams. -/
def diagram.isoOfIso (α : F ≅ G) : diagram F U ≅ diagram.{v'} G U :=
  NatIso.ofComponents (by rintro ⟨⟩; exact pi_opens.iso_of_iso U α; exact pi_inters.iso_of_iso U α)
    (by
      rintro ⟨⟩ ⟨⟩ ⟨⟩
      · simp
      · ext
        simp [left_res]
      · ext
        simp [right_res]
      · simp)
#align Top.presheaf.sheaf_condition_equalizer_products.diagram.iso_of_iso TopCat.Presheaf.SheafConditionEqualizerProducts.diagram.isoOfIso

/- warning: Top.presheaf.sheaf_condition_equalizer_products.fork.iso_of_iso -> TopCat.Presheaf.SheafConditionEqualizerProducts.fork.isoOfIso is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Top.presheaf.sheaf_condition_equalizer_products.fork.iso_of_iso TopCat.Presheaf.SheafConditionEqualizerProducts.fork.isoOfIsoₓ'. -/
/-- If `F G : presheaf C X` are isomorphic presheaves,
then the `fork F U`, the canonical cone of the sheaf condition diagram for `F`,
is isomorphic to `fork F G` postcomposed with the corresponding isomorphism between
sheaf condition diagrams.
-/
def fork.isoOfIso (α : F ≅ G) :
    fork F U ≅ (Cones.postcompose (diagram.isoOfIso U α).inv).obj (fork G U) :=
  by
  fapply fork.ext
  · apply α.app
  · ext
    dsimp only [fork.ι]
    -- Ugh, `simp` can't unfold abbreviations.
    simp [res, diagram.iso_of_iso]
#align Top.presheaf.sheaf_condition_equalizer_products.fork.iso_of_iso TopCat.Presheaf.SheafConditionEqualizerProducts.fork.isoOfIso

end SheafConditionEqualizerProducts

#print TopCat.Presheaf.IsSheafEqualizerProducts /-
/-- The sheaf condition for a `F : presheaf C X` requires that the morphism
`F.obj U ⟶ ∏ F.obj (U i)` (where `U` is some open set which is the union of the `U i`)
is the equalizer of the two morphisms
`∏ F.obj (U i) ⟶ ∏ F.obj (U i) ⊓ (U j)`.
-/
def IsSheafEqualizerProducts (F : Presheaf.{v', v, u} C X) : Prop :=
  ∀ ⦃ι : Type v'⦄ (U : ι → Opens X), Nonempty (IsLimit (SheafConditionEqualizerProducts.fork F U))
#align Top.presheaf.is_sheaf_equalizer_products TopCat.Presheaf.IsSheafEqualizerProducts
-/

/-!
The remainder of this file shows that the equalizer_products sheaf condition is equivalent
to the pariwise_intersections sheaf condition.
-/


namespace SheafConditionPairwiseIntersections

open CategoryTheory.Pairwise CategoryTheory.Pairwise.Hom

/- warning: Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_functor_obj -> TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivFunctorObj is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_functor_obj TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivFunctorObjₓ'. -/
/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def coneEquivFunctorObj (c : Cone ((diagram U).op ⋙ F)) :
    Cone (SheafConditionEqualizerProducts.diagram F U)
    where
  pt := c.pt
  π :=
    { app := fun Z =>
        WalkingParallelPair.casesOn Z (Pi.lift fun i : ι => c.π.app (op (single i)))
          (Pi.lift fun b : ι × ι => c.π.app (op (pair b.1 b.2)))
      naturality' := fun Y Z f => by
        cases Y <;> cases Z <;> cases f
        · ext i
          dsimp
          simp only [limit.lift_π, category.id_comp, fan.mk_π_app, CategoryTheory.Functor.map_id,
            category.assoc]
          dsimp
          simp only [limit.lift_π, category.id_comp, fan.mk_π_app]
        · ext ⟨i, j⟩
          dsimp [sheaf_condition_equalizer_products.left_res]
          simp only [limit.lift_π, limit.lift_π_assoc, category.id_comp, fan.mk_π_app,
            category.assoc]
          have h := c.π.naturality (Quiver.Hom.op (hom.left i j))
          dsimp at h
          simpa using h
        · ext ⟨i, j⟩
          dsimp [sheaf_condition_equalizer_products.right_res]
          simp only [limit.lift_π, limit.lift_π_assoc, category.id_comp, fan.mk_π_app,
            category.assoc]
          have h := c.π.naturality (Quiver.Hom.op (hom.right i j))
          dsimp at h
          simpa using h
        · ext i
          dsimp
          simp only [limit.lift_π, category.id_comp, fan.mk_π_app, CategoryTheory.Functor.map_id,
            category.assoc]
          dsimp
          simp only [limit.lift_π, category.id_comp, fan.mk_π_app] }
#align Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_functor_obj TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivFunctorObj

section

attribute [local tidy] tactic.case_bash

/- warning: Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_functor -> TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivFunctor is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_functor TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivFunctorₓ'. -/
/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def coneEquivFunctor :
    Limits.Cone ((diagram U).op ⋙ F) ⥤ Limits.Cone (SheafConditionEqualizerProducts.diagram F U)
    where
  obj c := coneEquivFunctorObj F U c
  map c c' f :=
    { Hom := f.Hom
      w' := fun j => by
        cases j <;>
          · ext
            simp only [limits.fan.mk_π_app, limits.cone_morphism.w, limits.limit.lift_π,
              category.assoc, cone_equiv_functor_obj_π_app] }
#align Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_functor TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivFunctor

end

/- warning: Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_inverse_obj -> TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivInverseObj is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_inverse_obj TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivInverseObjₓ'. -/
/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def coneEquivInverseObj (c : Limits.Cone (SheafConditionEqualizerProducts.diagram F U)) :
    Limits.Cone ((diagram U).op ⋙ F) where
  pt := c.pt
  π :=
    { app := by
        intro x
        induction x using Opposite.rec'
        rcases x with (⟨i⟩ | ⟨i, j⟩)
        · exact c.π.app walking_parallel_pair.zero ≫ pi.π _ i
        · exact c.π.app walking_parallel_pair.one ≫ pi.π _ (i, j)
      naturality' := by
        intro x y f
        induction x using Opposite.rec'
        induction y using Opposite.rec'
        have ef : f = f.unop.op := rfl
        revert ef
        generalize f.unop = f'
        rintro rfl
        rcases x with (⟨i⟩ | ⟨⟩) <;> rcases y with (⟨⟩ | ⟨j, j⟩) <;> rcases f' with ⟨⟩
        · dsimp
          erw [F.map_id]
          simp
        · dsimp
          simp only [category.id_comp, category.assoc]
          have h := c.π.naturality walking_parallel_pair_hom.left
          dsimp [sheaf_condition_equalizer_products.left_res] at h
          simp only [category.id_comp] at h
          have h' := h =≫ pi.π _ (i, j)
          rw [h']
          simp only [category.assoc, limit.lift_π, fan.mk_π_app]
          rfl
        · dsimp
          simp only [category.id_comp, category.assoc]
          have h := c.π.naturality walking_parallel_pair_hom.right
          dsimp [sheaf_condition_equalizer_products.right_res] at h
          simp only [category.id_comp] at h
          have h' := h =≫ pi.π _ (j, i)
          rw [h']
          simp
          rfl
        · dsimp
          erw [F.map_id]
          simp }
#align Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_inverse_obj TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivInverseObj

/- warning: Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_inverse -> TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivInverse is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_inverse TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivInverseₓ'. -/
/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def coneEquivInverse :
    Limits.Cone (SheafConditionEqualizerProducts.diagram F U) ⥤ Limits.Cone ((diagram U).op ⋙ F)
    where
  obj c := coneEquivInverseObj F U c
  map c c' f :=
    { Hom := f.Hom
      w' := by
        intro x
        induction x using Opposite.rec'
        rcases x with (⟨i⟩ | ⟨i, j⟩)
        · dsimp
          dsimp only [fork.ι]
          rw [← f.w walking_parallel_pair.zero, category.assoc]
        · dsimp
          rw [← f.w walking_parallel_pair.one, category.assoc] }
#align Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_inverse TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivInverse

/- warning: Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_unit_iso_app -> TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivUnitIsoApp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_unit_iso_app TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivUnitIsoAppₓ'. -/
/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def coneEquivUnitIsoApp (c : Cone ((diagram U).op ⋙ F)) :
    (𝟭 (Cone ((diagram U).op ⋙ F))).obj c ≅ (coneEquivFunctor F U ⋙ coneEquivInverse F U).obj c
    where
  Hom :=
    { Hom := 𝟙 _
      w' := fun j => by induction j using Opposite.rec';
        rcases j with ⟨⟩ <;>
          · dsimp
            simp only [limits.fan.mk_π_app, category.id_comp, limits.limit.lift_π] }
  inv :=
    { Hom := 𝟙 _
      w' := fun j => by induction j using Opposite.rec';
        rcases j with ⟨⟩ <;>
          · dsimp
            simp only [limits.fan.mk_π_app, category.id_comp, limits.limit.lift_π] }
  hom_inv_id' := by
    ext
    simp only [category.comp_id, limits.cone.category_comp_hom, limits.cone.category_id_hom]
  inv_hom_id' := by
    ext
    simp only [category.comp_id, limits.cone.category_comp_hom, limits.cone.category_id_hom]
#align Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_unit_iso_app TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivUnitIsoApp

/- warning: Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_unit_iso -> TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivUnitIso is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_unit_iso TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivUnitIsoₓ'. -/
/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def coneEquivUnitIso :
    𝟭 (Limits.Cone ((diagram U).op ⋙ F)) ≅ coneEquivFunctor F U ⋙ coneEquivInverse F U :=
  NatIso.ofComponents (coneEquivUnitIsoApp F U) (by tidy)
#align Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_unit_iso TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivUnitIso

#print TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivCounitIso /-
/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def coneEquivCounitIso :
    coneEquivInverse F U ⋙ coneEquivFunctor F U ≅
      𝟭 (Limits.Cone (SheafConditionEqualizerProducts.diagram F U)) :=
  NatIso.ofComponents
    (fun c =>
      { Hom :=
          { Hom := 𝟙 _
            w' := by
              rintro ⟨_ | _⟩
              · ext ⟨j⟩
                dsimp
                simp only [category.id_comp, limits.fan.mk_π_app, limits.limit.lift_π]
              · ext ⟨i, j⟩
                dsimp
                simp only [category.id_comp, limits.fan.mk_π_app, limits.limit.lift_π] }
        inv :=
          { Hom := 𝟙 _
            w' := by
              rintro ⟨_ | _⟩
              · ext ⟨j⟩
                dsimp
                simp only [category.id_comp, limits.fan.mk_π_app, limits.limit.lift_π]
              · ext ⟨i, j⟩
                dsimp
                simp only [category.id_comp, limits.fan.mk_π_app, limits.limit.lift_π] }
        hom_inv_id' := by
          ext
          dsimp
          simp only [category.comp_id]
        inv_hom_id' := by
          ext
          dsimp
          simp only [category.comp_id] })
    fun c d f => by
    ext
    dsimp
    simp only [category.comp_id, category.id_comp]
#align Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv_counit_iso TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivCounitIso
-/

/- warning: Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv -> TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquivₓ'. -/
/--
Cones over `diagram U ⋙ F` are the same as a cones over the usual sheaf condition equalizer diagram.
-/
@[simps]
def coneEquiv :
    Limits.Cone ((diagram U).op ⋙ F) ≌ Limits.Cone (SheafConditionEqualizerProducts.diagram F U)
    where
  Functor := coneEquivFunctor F U
  inverse := coneEquivInverse F U
  unitIso := coneEquivUnitIso F U
  counitIso := coneEquivCounitIso F U
#align Top.presheaf.sheaf_condition_pairwise_intersections.cone_equiv TopCat.Presheaf.SheafConditionPairwiseIntersections.coneEquiv

attribute [local reducible]
  sheaf_condition_equalizer_products.res sheaf_condition_equalizer_products.left_res

/- warning: Top.presheaf.sheaf_condition_pairwise_intersections.is_limit_map_cone_of_is_limit_sheaf_condition_fork -> TopCat.Presheaf.SheafConditionPairwiseIntersections.isLimitMapConeOfIsLimitSheafConditionFork is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Top.presheaf.sheaf_condition_pairwise_intersections.is_limit_map_cone_of_is_limit_sheaf_condition_fork TopCat.Presheaf.SheafConditionPairwiseIntersections.isLimitMapConeOfIsLimitSheafConditionForkₓ'. -/
/-- If `sheaf_condition_equalizer_products.fork` is an equalizer,
then `F.map_cone (cone U)` is a limit cone.
-/
def isLimitMapConeOfIsLimitSheafConditionFork
    (P : IsLimit (SheafConditionEqualizerProducts.fork F U)) : IsLimit (F.mapCone (cocone U).op) :=
  IsLimit.ofIsoLimit ((IsLimit.ofConeEquiv (coneEquiv F U).symm).symm P)
    { Hom :=
        { Hom := 𝟙 _
          w' := by
            intro x
            induction x using Opposite.rec'
            rcases x with ⟨⟩
            · dsimp
              simp
              rfl
            · dsimp
              simp only [limit.lift_π, limit.lift_π_assoc, category.id_comp, fan.mk_π_app,
                category.assoc]
              rw [← F.map_comp]
              rfl }
      inv :=
        { Hom := 𝟙 _
          w' := by
            intro x
            induction x using Opposite.rec'
            rcases x with ⟨⟩
            · dsimp
              simp
              rfl
            · dsimp
              simp only [limit.lift_π, limit.lift_π_assoc, category.id_comp, fan.mk_π_app,
                category.assoc]
              rw [← F.map_comp]
              rfl }
      hom_inv_id' := by
        ext
        dsimp
        simp only [category.comp_id]
      inv_hom_id' := by
        ext
        dsimp
        simp only [category.comp_id] }
#align Top.presheaf.sheaf_condition_pairwise_intersections.is_limit_map_cone_of_is_limit_sheaf_condition_fork TopCat.Presheaf.SheafConditionPairwiseIntersections.isLimitMapConeOfIsLimitSheafConditionFork

/- warning: Top.presheaf.sheaf_condition_pairwise_intersections.is_limit_sheaf_condition_fork_of_is_limit_map_cone -> TopCat.Presheaf.SheafConditionPairwiseIntersections.isLimitSheafConditionForkOfIsLimitMapCone is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Top.presheaf.sheaf_condition_pairwise_intersections.is_limit_sheaf_condition_fork_of_is_limit_map_cone TopCat.Presheaf.SheafConditionPairwiseIntersections.isLimitSheafConditionForkOfIsLimitMapConeₓ'. -/
/-- If `F.map_cone (cone U)` is a limit cone,
then `sheaf_condition_equalizer_products.fork` is an equalizer.
-/
def isLimitSheafConditionForkOfIsLimitMapCone (Q : IsLimit (F.mapCone (cocone U).op)) :
    IsLimit (SheafConditionEqualizerProducts.fork F U) :=
  IsLimit.ofIsoLimit ((IsLimit.ofConeEquiv (coneEquiv F U)).symm Q)
    { Hom :=
        { Hom := 𝟙 _
          w' := by
            rintro ⟨⟩
            · dsimp
              simp
              rfl
            · dsimp
              ext ⟨i, j⟩
              simp only [limit.lift_π, limit.lift_π_assoc, category.id_comp, fan.mk_π_app,
                category.assoc]
              rw [← F.map_comp]
              rfl }
      inv :=
        { Hom := 𝟙 _
          w' := by
            rintro ⟨⟩
            · dsimp
              simp
              rfl
            · dsimp
              ext ⟨i, j⟩
              simp only [limit.lift_π, limit.lift_π_assoc, category.id_comp, fan.mk_π_app,
                category.assoc]
              rw [← F.map_comp]
              rfl }
      hom_inv_id' := by
        ext
        dsimp
        simp only [category.comp_id]
      inv_hom_id' := by
        ext
        dsimp
        simp only [category.comp_id] }
#align Top.presheaf.sheaf_condition_pairwise_intersections.is_limit_sheaf_condition_fork_of_is_limit_map_cone TopCat.Presheaf.SheafConditionPairwiseIntersections.isLimitSheafConditionForkOfIsLimitMapCone

end SheafConditionPairwiseIntersections

open SheafConditionPairwiseIntersections

#print TopCat.Presheaf.isSheaf_iff_isSheafEqualizerProducts /-
/-- The sheaf condition in terms of an equalizer diagram is equivalent
to the default sheaf condition.
-/
theorem isSheaf_iff_isSheafEqualizerProducts (F : Presheaf C X) :
    F.IsSheaf ↔ F.IsSheafEqualizerProducts :=
  (isSheaf_iff_isSheafPairwiseIntersections F).trans <|
    Iff.intro (fun h ι U => ⟨isLimitSheafConditionForkOfIsLimitMapCone F U (h U).some⟩) fun h ι U =>
      ⟨isLimitMapConeOfIsLimitSheafConditionFork F U (h U).some⟩
#align Top.presheaf.is_sheaf_iff_is_sheaf_equalizer_products TopCat.Presheaf.isSheaf_iff_isSheafEqualizerProducts
-/

end Presheaf

end TopCat

