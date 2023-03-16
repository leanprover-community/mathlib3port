/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.limits.connected
! leanprover-community/mathlib commit 10bf4f825ad729c5653adc039dafa3622e7f93c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Limits.Shapes.Equalizers
import Mathbin.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathbin.CategoryTheory.IsConnected
import Mathbin.CategoryTheory.Limits.Preserves.Basic

/-!
# Connected limits

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A connected limit is a limit whose shape is a connected category.

We give examples of connected categories, and prove that the functor given
by `(X × -)` preserves any connected limit. That is, any limit of shape `J`
where `J` is a connected category is preserved by the functor `(X × -)`.
-/


noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace CategoryTheory

section Examples

#print CategoryTheory.widePullbackShape_connected /-
instance widePullbackShape_connected (J : Type v₁) : IsConnected (WidePullbackShape J) :=
  by
  apply is_connected.of_induct
  introv hp t
  cases j
  · exact hp
  · rwa [t (wide_pullback_shape.hom.term j)]
#align category_theory.wide_pullback_shape_connected CategoryTheory.widePullbackShape_connected
-/

#print CategoryTheory.widePushoutShape_connected /-
instance widePushoutShape_connected (J : Type v₁) : IsConnected (WidePushoutShape J) :=
  by
  apply is_connected.of_induct
  introv hp t
  cases j
  · exact hp
  · rwa [← t (wide_pushout_shape.hom.init j)]
#align category_theory.wide_pushout_shape_connected CategoryTheory.widePushoutShape_connected
-/

#print CategoryTheory.parallelPairInhabited /-
instance parallelPairInhabited : Inhabited WalkingParallelPair :=
  ⟨WalkingParallelPair.one⟩
#align category_theory.parallel_pair_inhabited CategoryTheory.parallelPairInhabited
-/

#print CategoryTheory.parallel_pair_connected /-
instance parallel_pair_connected : IsConnected WalkingParallelPair :=
  by
  apply is_connected.of_induct
  introv _ t
  cases j
  · rwa [t walking_parallel_pair_hom.left]
  · assumption
#align category_theory.parallel_pair_connected CategoryTheory.parallel_pair_connected
-/

end Examples

attribute [local tidy] tactic.case_bash

variable {C : Type u₂} [Category.{v₂} C]

variable [HasBinaryProducts C]

variable {J : Type v₂} [SmallCategory J]

namespace ProdPreservesConnectedLimits

/- warning: category_theory.prod_preserves_connected_limits.γ₂ -> CategoryTheory.ProdPreservesConnectedLimits.γ₂ is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasBinaryProducts.{u1, u2} C _inst_1] {J : Type.{u1}} [_inst_3 : CategoryTheory.SmallCategory.{u1} J] {K : CategoryTheory.Functor.{u1, u1, u1, u2} J _inst_3 C _inst_1} (X : C), Quiver.Hom.{succ u1, max u1 u2} (CategoryTheory.Functor.{u1, u1, u1, u2} J _inst_3 C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u1 u2} (CategoryTheory.Functor.{u1, u1, u1, u2} J _inst_3 C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u1 u2} (CategoryTheory.Functor.{u1, u1, u1, u2} J _inst_3 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u1, u2} J _inst_3 C _inst_1))) (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u2} J _inst_3 C _inst_1 C _inst_1 K (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Limits.prod.functor.{u1, u2} C _inst_1 _inst_2) X)) K
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasBinaryProducts.{u1, u2} C _inst_1] {J : Type.{u1}} [_inst_3 : CategoryTheory.SmallCategory.{u1} J] {K : CategoryTheory.Functor.{u1, u1, u1, u2} J _inst_3 C _inst_1} (X : C), Quiver.Hom.{succ u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u1, u2} J _inst_3 C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u1, u2} J _inst_3 C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u1, u2} J _inst_3 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u1, u2} J _inst_3 C _inst_1))) (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u2} J _inst_3 C _inst_1 C _inst_1 K (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Limits.prod.functor.{u1, u2} C _inst_1 _inst_2)) X)) K
Case conversion may be inaccurate. Consider using '#align category_theory.prod_preserves_connected_limits.γ₂ CategoryTheory.ProdPreservesConnectedLimits.γ₂ₓ'. -/
/-- (Impl). The obvious natural transformation from (X × K -) to K. -/
@[simps]
def γ₂ {K : J ⥤ C} (X : C) : K ⋙ prod.functor.obj X ⟶ K where app Y := Limits.prod.snd
#align category_theory.prod_preserves_connected_limits.γ₂ CategoryTheory.ProdPreservesConnectedLimits.γ₂

/- warning: category_theory.prod_preserves_connected_limits.γ₁ -> CategoryTheory.ProdPreservesConnectedLimits.γ₁ is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasBinaryProducts.{u1, u2} C _inst_1] {J : Type.{u1}} [_inst_3 : CategoryTheory.SmallCategory.{u1} J] {K : CategoryTheory.Functor.{u1, u1, u1, u2} J _inst_3 C _inst_1} (X : C), Quiver.Hom.{succ u1, max u1 u2} (CategoryTheory.Functor.{u1, u1, u1, u2} J _inst_3 C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u1 u2} (CategoryTheory.Functor.{u1, u1, u1, u2} J _inst_3 C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u1 u2} (CategoryTheory.Functor.{u1, u1, u1, u2} J _inst_3 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u1, u2} J _inst_3 C _inst_1))) (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u2} J _inst_3 C _inst_1 C _inst_1 K (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Limits.prod.functor.{u1, u2} C _inst_1 _inst_2) X)) (CategoryTheory.Functor.obj.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{u1, u1, u1, u2} J _inst_3 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u1, u2} J _inst_3 C _inst_1) (CategoryTheory.Functor.const.{u1, u1, u1, u2} J _inst_3 C _inst_1) X)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasBinaryProducts.{u1, u2} C _inst_1] {J : Type.{u1}} [_inst_3 : CategoryTheory.SmallCategory.{u1} J] {K : CategoryTheory.Functor.{u1, u1, u1, u2} J _inst_3 C _inst_1} (X : C), Quiver.Hom.{succ u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u1, u2} J _inst_3 C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u1, u2} J _inst_3 C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u1, u2} J _inst_3 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u1, u2} J _inst_3 C _inst_1))) (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u2} J _inst_3 C _inst_1 C _inst_1 K (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Limits.prod.functor.{u1, u2} C _inst_1 _inst_2)) X)) (Prefunctor.obj.{succ u1, succ u1, u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{u1, u1, u1, u2} J _inst_3 C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u1 u2} (CategoryTheory.Functor.{u1, u1, u1, u2} J _inst_3 C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u1 u2} (CategoryTheory.Functor.{u1, u1, u1, u2} J _inst_3 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u1, u2} J _inst_3 C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{u1, u1, u1, u2} J _inst_3 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u1, u2} J _inst_3 C _inst_1) (CategoryTheory.Functor.const.{u1, u1, u1, u2} J _inst_3 C _inst_1)) X)
Case conversion may be inaccurate. Consider using '#align category_theory.prod_preserves_connected_limits.γ₁ CategoryTheory.ProdPreservesConnectedLimits.γ₁ₓ'. -/
/-- (Impl). The obvious natural transformation from (X × K -) to X -/
@[simps]
def γ₁ {K : J ⥤ C} (X : C) : K ⋙ prod.functor.obj X ⟶ (Functor.const J).obj X
    where app Y := Limits.prod.fst
#align category_theory.prod_preserves_connected_limits.γ₁ CategoryTheory.ProdPreservesConnectedLimits.γ₁

/- warning: category_theory.prod_preserves_connected_limits.forget_cone -> CategoryTheory.ProdPreservesConnectedLimits.forgetCone is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasBinaryProducts.{u1, u2} C _inst_1] {J : Type.{u1}} [_inst_3 : CategoryTheory.SmallCategory.{u1} J] {X : C} {K : CategoryTheory.Functor.{u1, u1, u1, u2} J _inst_3 C _inst_1}, (CategoryTheory.Limits.Cone.{u1, u1, u1, u2} J _inst_3 C _inst_1 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u2} J _inst_3 C _inst_1 C _inst_1 K (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Limits.prod.functor.{u1, u2} C _inst_1 _inst_2) X))) -> (CategoryTheory.Limits.Cone.{u1, u1, u1, u2} J _inst_3 C _inst_1 K)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasBinaryProducts.{u1, u2} C _inst_1] {J : Type.{u1}} [_inst_3 : CategoryTheory.SmallCategory.{u1} J] {X : C} {K : CategoryTheory.Functor.{u1, u1, u1, u2} J _inst_3 C _inst_1}, (CategoryTheory.Limits.Cone.{u1, u1, u1, u2} J _inst_3 C _inst_1 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u2} J _inst_3 C _inst_1 C _inst_1 K (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Limits.prod.functor.{u1, u2} C _inst_1 _inst_2)) X))) -> (CategoryTheory.Limits.Cone.{u1, u1, u1, u2} J _inst_3 C _inst_1 K)
Case conversion may be inaccurate. Consider using '#align category_theory.prod_preserves_connected_limits.forget_cone CategoryTheory.ProdPreservesConnectedLimits.forgetConeₓ'. -/
/-- (Impl).
Given a cone for (X × K -), produce a cone for K using the natural transformation `γ₂` -/
@[simps]
def forgetCone {X : C} {K : J ⥤ C} (s : Cone (K ⋙ prod.functor.obj X)) : Cone K
    where
  pt := s.pt
  π := s.π ≫ γ₂ X
#align category_theory.prod_preserves_connected_limits.forget_cone CategoryTheory.ProdPreservesConnectedLimits.forgetCone

end ProdPreservesConnectedLimits

open ProdPreservesConnectedLimits

/- warning: category_theory.prod_preserves_connected_limits -> CategoryTheory.prodPreservesConnectedLimits is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasBinaryProducts.{u1, u2} C _inst_1] {J : Type.{u1}} [_inst_3 : CategoryTheory.SmallCategory.{u1} J] [_inst_4 : CategoryTheory.IsConnected.{u1, u1} J _inst_3] (X : C), CategoryTheory.Limits.PreservesLimitsOfShape.{u1, u1, u1, u1, u2, u2} C _inst_1 C _inst_1 J _inst_3 (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Limits.prod.functor.{u1, u2} C _inst_1 _inst_2) X)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasBinaryProducts.{u1, u2} C _inst_1] {J : Type.{u1}} [_inst_3 : CategoryTheory.SmallCategory.{u1} J] [_inst_4 : CategoryTheory.IsConnected.{u1, u1} J _inst_3] (X : C), CategoryTheory.Limits.PreservesLimitsOfShape.{u1, u1, u1, u1, u2, u2} C _inst_1 C _inst_1 J _inst_3 (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u2, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 u1} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Limits.prod.functor.{u1, u2} C _inst_1 _inst_2)) X)
Case conversion may be inaccurate. Consider using '#align category_theory.prod_preserves_connected_limits CategoryTheory.prodPreservesConnectedLimitsₓ'. -/
/-- The functor `(X × -)` preserves any connected limit.
Note that this functor does not preserve the two most obvious disconnected limits - that is,
`(X × -)` does not preserve products or terminal object, eg `(X ⨯ A) ⨯ (X ⨯ B)` is not isomorphic to
`X ⨯ (A ⨯ B)` and `X ⨯ 1` is not isomorphic to `1`.
-/
noncomputable def prodPreservesConnectedLimits [IsConnected J] (X : C) :
    PreservesLimitsOfShape J (prod.functor.obj X)
    where PreservesLimit K :=
    {
      preserves := fun c l =>
        { lift := fun s =>
            prod.lift (s.π.app (Classical.arbitrary _) ≫ Limits.prod.fst) (l.lift (forgetCone s))
          fac := fun s j => by
            apply prod.hom_ext
            · erw [assoc, lim_map_π, comp_id, limit.lift_π]
              exact (nat_trans_from_is_connected (s.π ≫ γ₁ X) j (Classical.arbitrary _)).symm
            · simp [← l.fac (forget_cone s) j]
          uniq := fun s m L => by
            apply prod.hom_ext
            · erw [limit.lift_π, ← L (Classical.arbitrary J), assoc, lim_map_π, comp_id]
              rfl
            · rw [limit.lift_π]
              apply l.uniq (forget_cone s)
              intro j
              simp [← L j] } }
#align category_theory.prod_preserves_connected_limits CategoryTheory.prodPreservesConnectedLimits

end CategoryTheory

