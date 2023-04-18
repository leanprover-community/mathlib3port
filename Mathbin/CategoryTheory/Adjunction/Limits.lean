/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Johan Commelin

! This file was ported from Lean 3 source module category_theory.adjunction.limits
! leanprover-community/mathlib commit f47581155c818e6361af4e4fda60d27d020c226b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Adjunction.Basic
import Mathbin.CategoryTheory.Limits.Creates

/-!
# Adjunctions and limits

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A left adjoint preserves colimits (`category_theory.adjunction.left_adjoint_preserves_colimits`),
and a right adjoint preserves limits (`category_theory.adjunction.right_adjoint_preserves_limits`).

Equivalences create and reflect (co)limits.
(`category_theory.adjunction.is_equivalence_creates_limits`,
`category_theory.adjunction.is_equivalence_creates_colimits`,
`category_theory.adjunction.is_equivalence_reflects_limits`,
`category_theory.adjunction.is_equivalence_reflects_colimits`,)

In `category_theory.adjunction.cocones_iso` we show that
when `F ⊣ G`,
the functor associating to each `Y` the cocones over `K ⋙ F` with cone point `Y`
is naturally isomorphic to
the functor associating to each `Y` the cocones over `K` with cone point `G.obj Y`.
-/


open Opposite

namespace CategoryTheory.Adjunction

open CategoryTheory

open CategoryTheory.Functor

open CategoryTheory.Limits

universe v u v₁ v₂ v₀ u₁ u₂

section ArbitraryUniverse

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

include adj

section PreservationColimits

variable {J : Type u} [Category.{v} J] (K : J ⥤ C)

#print CategoryTheory.Adjunction.functorialityRightAdjoint /-
/-- The right adjoint of `cocones.functoriality K F : cocone K ⥤ cocone (K ⋙ F)`.

Auxiliary definition for `functoriality_is_left_adjoint`.
-/
def functorialityRightAdjoint : Cocone (K ⋙ F) ⥤ Cocone K :=
  Cocones.functoriality _ G ⋙
    Cocones.precompose (K.rightUnitor.inv ≫ whiskerLeft K adj.Unit ≫ (associator _ _ _).inv)
#align category_theory.adjunction.functoriality_right_adjoint CategoryTheory.Adjunction.functorialityRightAdjoint
-/

attribute [local reducible] functoriality_right_adjoint

#print CategoryTheory.Adjunction.functorialityUnit /-
/-- The unit for the adjunction for `cocones.functoriality K F : cocone K ⥤ cocone (K ⋙ F)`.

Auxiliary definition for `functoriality_is_left_adjoint`.
-/
@[simps]
def functorialityUnit : 𝟭 (Cocone K) ⟶ Cocones.functoriality _ F ⋙ functorialityRightAdjoint adj K
    where app c := { Hom := adj.Unit.app c.pt }
#align category_theory.adjunction.functoriality_unit CategoryTheory.Adjunction.functorialityUnit
-/

#print CategoryTheory.Adjunction.functorialityCounit /-
/-- The counit for the adjunction for `cocones.functoriality K F : cocone K ⥤ cocone (K ⋙ F)`.

Auxiliary definition for `functoriality_is_left_adjoint`.
-/
@[simps]
def functorialityCounit :
    functorialityRightAdjoint adj K ⋙ Cocones.functoriality _ F ⟶ 𝟭 (Cocone (K ⋙ F))
    where app c := { Hom := adj.counit.app c.pt }
#align category_theory.adjunction.functoriality_counit CategoryTheory.Adjunction.functorialityCounit
-/

#print CategoryTheory.Adjunction.functorialityIsLeftAdjoint /-
/-- The functor `cocones.functoriality K F : cocone K ⥤ cocone (K ⋙ F)` is a left adjoint. -/
def functorialityIsLeftAdjoint : IsLeftAdjoint (Cocones.functoriality K F)
    where
  right := functorialityRightAdjoint adj K
  adj :=
    mkOfUnitCounit
      { Unit := functorialityUnit adj K
        counit := functorialityCounit adj K }
#align category_theory.adjunction.functoriality_is_left_adjoint CategoryTheory.Adjunction.functorialityIsLeftAdjoint
-/

#print CategoryTheory.Adjunction.leftAdjointPreservesColimits /-
/-- A left adjoint preserves colimits.

See <https://stacks.math.columbia.edu/tag/0038>.
-/
def leftAdjointPreservesColimits : PreservesColimitsOfSize.{v, u} F
    where PreservesColimitsOfShape J 𝒥 :=
    {
      PreservesColimit := fun F =>
        {
          preserves := fun c hc =>
            is_colimit.iso_unique_cocone_morphism.inv fun s =>
              @Equiv.unique _ _ (is_colimit.iso_unique_cocone_morphism.hom hc _)
                ((adj.functoriality_is_left_adjoint _).adj.homEquiv _ _) } }
#align category_theory.adjunction.left_adjoint_preserves_colimits CategoryTheory.Adjunction.leftAdjointPreservesColimits
-/

omit adj

#print CategoryTheory.Adjunction.isEquivalencePreservesColimits /-
-- see Note [lower instance priority]
instance (priority := 100) isEquivalencePreservesColimits (E : C ⥤ D) [IsEquivalence E] :
    PreservesColimitsOfSize.{v, u} E :=
  leftAdjointPreservesColimits E.Adjunction
#align category_theory.adjunction.is_equivalence_preserves_colimits CategoryTheory.Adjunction.isEquivalencePreservesColimits
-/

#print CategoryTheory.Adjunction.isEquivalenceReflectsColimits /-
-- see Note [lower instance priority]
instance (priority := 100) isEquivalenceReflectsColimits (E : D ⥤ C) [IsEquivalence E] :
    ReflectsColimitsOfSize.{v, u} E
    where ReflectsColimitsOfShape J 𝒥 :=
    {
      ReflectsColimit := fun K =>
        {
          reflects := fun c t =>
            by
            have l :=
              (is_colimit_of_preserves E.inv t).mapCoconeEquiv E.as_equivalence.unit_iso.symm
            refine' ((is_colimit.precompose_inv_equiv K.right_unitor _).symm l).ofIsoColimit _
            tidy } }
#align category_theory.adjunction.is_equivalence_reflects_colimits CategoryTheory.Adjunction.isEquivalenceReflectsColimits
-/

#print CategoryTheory.Adjunction.isEquivalenceCreatesColimits /-
-- see Note [lower instance priority]
instance (priority := 100) isEquivalenceCreatesColimits (H : D ⥤ C) [IsEquivalence H] :
    CreatesColimitsOfSize.{v, u} H
    where CreatesColimitsOfShape J 𝒥 :=
    {
      CreatesColimit := fun F =>
        {
          lifts := fun c t =>
            { liftedCocone := H.map_cocone_inv c
              validLift := H.map_cocone_map_cocone_inv c } } }
#align category_theory.adjunction.is_equivalence_creates_colimits CategoryTheory.Adjunction.isEquivalenceCreatesColimits
-/

-- verify the preserve_colimits instance works as expected:
example (E : C ⥤ D) [IsEquivalence E] (c : Cocone K) (h : IsColimit c) :
    IsColimit (E.mapCocone c) :=
  PreservesColimit.preserves h

#print CategoryTheory.Adjunction.hasColimit_comp_equivalence /-
theorem hasColimit_comp_equivalence (E : C ⥤ D) [IsEquivalence E] [HasColimit K] :
    HasColimit (K ⋙ E) :=
  HasColimit.mk
    { Cocone := E.mapCocone (colimit.cocone K)
      IsColimit := PreservesColimit.preserves (colimit.isColimit K) }
#align category_theory.adjunction.has_colimit_comp_equivalence CategoryTheory.Adjunction.hasColimit_comp_equivalence
-/

#print CategoryTheory.Adjunction.hasColimit_of_comp_equivalence /-
theorem hasColimit_of_comp_equivalence (E : C ⥤ D) [IsEquivalence E] [HasColimit (K ⋙ E)] :
    HasColimit K :=
  @hasColimitOfIso _ _ _ _ (K ⋙ E ⋙ inv E) K
    (@hasColimit_comp_equivalence _ _ _ _ _ _ (K ⋙ E) (inv E) _ _)
    ((Functor.rightUnitor _).symm ≪≫ isoWhiskerLeft K E.asEquivalence.unitIso)
#align category_theory.adjunction.has_colimit_of_comp_equivalence CategoryTheory.Adjunction.hasColimit_of_comp_equivalence
-/

#print CategoryTheory.Adjunction.hasColimitsOfShape_of_equivalence /-
/-- Transport a `has_colimits_of_shape` instance across an equivalence. -/
theorem hasColimitsOfShape_of_equivalence (E : C ⥤ D) [IsEquivalence E] [HasColimitsOfShape J D] :
    HasColimitsOfShape J C :=
  ⟨fun F => has_colimit_of_comp_equivalence F E⟩
#align category_theory.adjunction.has_colimits_of_shape_of_equivalence CategoryTheory.Adjunction.hasColimitsOfShape_of_equivalence
-/

#print CategoryTheory.Adjunction.has_colimits_of_equivalence /-
/-- Transport a `has_colimits` instance across an equivalence. -/
theorem has_colimits_of_equivalence (E : C ⥤ D) [IsEquivalence E] [HasColimitsOfSize.{v, u} D] :
    HasColimitsOfSize.{v, u} C :=
  ⟨fun J hJ => has_colimits_of_shape_of_equivalence E⟩
#align category_theory.adjunction.has_colimits_of_equivalence CategoryTheory.Adjunction.has_colimits_of_equivalence
-/

end PreservationColimits

section PreservationLimits

variable {J : Type u} [Category.{v} J] (K : J ⥤ D)

#print CategoryTheory.Adjunction.functorialityLeftAdjoint /-
/-- The left adjoint of `cones.functoriality K G : cone K ⥤ cone (K ⋙ G)`.

Auxiliary definition for `functoriality_is_right_adjoint`.
-/
def functorialityLeftAdjoint : Cone (K ⋙ G) ⥤ Cone K :=
  Cones.functoriality _ F ⋙
    Cones.postcompose ((associator _ _ _).Hom ≫ whiskerLeft K adj.counit ≫ K.rightUnitor.Hom)
#align category_theory.adjunction.functoriality_left_adjoint CategoryTheory.Adjunction.functorialityLeftAdjoint
-/

attribute [local reducible] functoriality_left_adjoint

#print CategoryTheory.Adjunction.functorialityUnit' /-
/-- The unit for the adjunction for`cones.functoriality K G : cone K ⥤ cone (K ⋙ G)`.

Auxiliary definition for `functoriality_is_right_adjoint`.
-/
@[simps]
def functorialityUnit' : 𝟭 (Cone (K ⋙ G)) ⟶ functorialityLeftAdjoint adj K ⋙ Cones.functoriality _ G
    where app c := { Hom := adj.Unit.app c.pt }
#align category_theory.adjunction.functoriality_unit' CategoryTheory.Adjunction.functorialityUnit'
-/

#print CategoryTheory.Adjunction.functorialityCounit' /-
/-- The counit for the adjunction for`cones.functoriality K G : cone K ⥤ cone (K ⋙ G)`.

Auxiliary definition for `functoriality_is_right_adjoint`.
-/
@[simps]
def functorialityCounit' : Cones.functoriality _ G ⋙ functorialityLeftAdjoint adj K ⟶ 𝟭 (Cone K)
    where app c := { Hom := adj.counit.app c.pt }
#align category_theory.adjunction.functoriality_counit' CategoryTheory.Adjunction.functorialityCounit'
-/

#print CategoryTheory.Adjunction.functorialityIsRightAdjoint /-
/-- The functor `cones.functoriality K G : cone K ⥤ cone (K ⋙ G)` is a right adjoint. -/
def functorialityIsRightAdjoint : IsRightAdjoint (Cones.functoriality K G)
    where
  left := functorialityLeftAdjoint adj K
  adj :=
    mkOfUnitCounit
      { Unit := functorialityUnit' adj K
        counit := functorialityCounit' adj K }
#align category_theory.adjunction.functoriality_is_right_adjoint CategoryTheory.Adjunction.functorialityIsRightAdjoint
-/

#print CategoryTheory.Adjunction.rightAdjointPreservesLimits /-
/-- A right adjoint preserves limits.

See <https://stacks.math.columbia.edu/tag/0038>.
-/
def rightAdjointPreservesLimits : PreservesLimitsOfSize.{v, u} G
    where PreservesLimitsOfShape J 𝒥 :=
    {
      PreservesLimit := fun K =>
        {
          preserves := fun c hc =>
            is_limit.iso_unique_cone_morphism.inv fun s =>
              @Equiv.unique _ _ (is_limit.iso_unique_cone_morphism.hom hc _)
                ((adj.functoriality_is_right_adjoint _).adj.homEquiv _ _).symm } }
#align category_theory.adjunction.right_adjoint_preserves_limits CategoryTheory.Adjunction.rightAdjointPreservesLimits
-/

omit adj

#print CategoryTheory.Adjunction.isEquivalencePreservesLimits /-
-- see Note [lower instance priority]
instance (priority := 100) isEquivalencePreservesLimits (E : D ⥤ C) [IsEquivalence E] :
    PreservesLimitsOfSize.{v, u} E :=
  rightAdjointPreservesLimits E.inv.Adjunction
#align category_theory.adjunction.is_equivalence_preserves_limits CategoryTheory.Adjunction.isEquivalencePreservesLimits
-/

#print CategoryTheory.Adjunction.isEquivalenceReflectsLimits /-
-- see Note [lower instance priority]
instance (priority := 100) isEquivalenceReflectsLimits (E : D ⥤ C) [IsEquivalence E] :
    ReflectsLimitsOfSize.{v, u} E
    where ReflectsLimitsOfShape J 𝒥 :=
    {
      ReflectsLimit := fun K =>
        {
          reflects := fun c t =>
            by
            have := (is_limit_of_preserves E.inv t).mapConeEquiv E.as_equivalence.unit_iso.symm
            refine' ((is_limit.postcompose_hom_equiv K.left_unitor _).symm this).ofIsoLimit _
            tidy } }
#align category_theory.adjunction.is_equivalence_reflects_limits CategoryTheory.Adjunction.isEquivalenceReflectsLimits
-/

#print CategoryTheory.Adjunction.isEquivalenceCreatesLimits /-
-- see Note [lower instance priority]
instance (priority := 100) isEquivalenceCreatesLimits (H : D ⥤ C) [IsEquivalence H] :
    CreatesLimitsOfSize.{v, u} H
    where CreatesLimitsOfShape J 𝒥 :=
    {
      CreatesLimit := fun F =>
        {
          lifts := fun c t =>
            { liftedCone := H.map_cone_inv c
              validLift := H.map_cone_map_cone_inv c } } }
#align category_theory.adjunction.is_equivalence_creates_limits CategoryTheory.Adjunction.isEquivalenceCreatesLimits
-/

-- verify the preserve_limits instance works as expected:
example (E : D ⥤ C) [IsEquivalence E] (c : Cone K) [h : IsLimit c] : IsLimit (E.mapCone c) :=
  PreservesLimit.preserves h

#print CategoryTheory.Adjunction.hasLimit_comp_equivalence /-
theorem hasLimit_comp_equivalence (E : D ⥤ C) [IsEquivalence E] [HasLimit K] : HasLimit (K ⋙ E) :=
  HasLimit.mk
    { Cone := E.mapCone (limit.cone K)
      IsLimit := PreservesLimit.preserves (limit.isLimit K) }
#align category_theory.adjunction.has_limit_comp_equivalence CategoryTheory.Adjunction.hasLimit_comp_equivalence
-/

#print CategoryTheory.Adjunction.hasLimit_of_comp_equivalence /-
theorem hasLimit_of_comp_equivalence (E : D ⥤ C) [IsEquivalence E] [HasLimit (K ⋙ E)] :
    HasLimit K :=
  @hasLimitOfIso _ _ _ _ (K ⋙ E ⋙ inv E) K
    (@hasLimit_comp_equivalence _ _ _ _ _ _ (K ⋙ E) (inv E) _ _)
    (isoWhiskerLeft K E.asEquivalence.unitIso.symm ≪≫ Functor.rightUnitor _)
#align category_theory.adjunction.has_limit_of_comp_equivalence CategoryTheory.Adjunction.hasLimit_of_comp_equivalence
-/

#print CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence /-
/-- Transport a `has_limits_of_shape` instance across an equivalence. -/
theorem hasLimitsOfShape_of_equivalence (E : D ⥤ C) [IsEquivalence E] [HasLimitsOfShape J C] :
    HasLimitsOfShape J D :=
  ⟨fun F => has_limit_of_comp_equivalence F E⟩
#align category_theory.adjunction.has_limits_of_shape_of_equivalence CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence
-/

#print CategoryTheory.Adjunction.has_limits_of_equivalence /-
/-- Transport a `has_limits` instance across an equivalence. -/
theorem has_limits_of_equivalence (E : D ⥤ C) [IsEquivalence E] [HasLimitsOfSize.{v, u} C] :
    HasLimitsOfSize.{v, u} D :=
  ⟨fun J hJ => has_limits_of_shape_of_equivalence E⟩
#align category_theory.adjunction.has_limits_of_equivalence CategoryTheory.Adjunction.has_limits_of_equivalence
-/

end PreservationLimits

/- warning: category_theory.adjunction.cocones_iso_component_hom -> CategoryTheory.Adjunction.coconesIsoComponentHom is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u3, u5} C] {D : Type.{u6}} [_inst_2 : CategoryTheory.Category.{u4, u6} D] {F : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} {G : CategoryTheory.Functor.{u4, u3, u6, u5} D _inst_2 C _inst_1}, (CategoryTheory.Adjunction.{u3, u4, u5, u6} C _inst_1 D _inst_2 F G) -> (forall {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1} (Y : D), (CategoryTheory.Functor.obj.{u4, max u2 u4, u6, succ (max u2 u4)} D _inst_2 Type.{max u2 u4} CategoryTheory.types.{max u2 u4} (CategoryTheory.Functor.obj.{max u2 u4, max u6 u2 u4, max u1 u4 u2 u6, max u4 (max u2 u4) u6 (succ (max u2 u4))} (Opposite.{succ (max u1 u4 u2 u6)} (CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2)) (CategoryTheory.Category.opposite.{max u2 u4, max u1 u4 u2 u6} (CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u4, u2, u6} J _inst_3 D _inst_2)) (CategoryTheory.Functor.{u4, max u2 u4, u6, succ (max u2 u4)} D _inst_2 Type.{max u2 u4} CategoryTheory.types.{max u2 u4}) (CategoryTheory.Functor.category.{u4, max u2 u4, u6, succ (max u2 u4)} D _inst_2 Type.{max u2 u4} CategoryTheory.types.{max u2 u4}) (CategoryTheory.cocones.{u1, u4, u2, u6} J _inst_3 D _inst_2) (Opposite.op.{succ (max u1 u4 u2 u6)} (CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2) (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F))) Y) -> (CategoryTheory.Functor.obj.{u4, max u2 u3, u6, succ (max u2 u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3} (CategoryTheory.Functor.comp.{u4, u3, max u2 u3, u6, u5, succ (max u2 u3)} D _inst_2 C _inst_1 Type.{max u2 u3} CategoryTheory.types.{max u2 u3} G (CategoryTheory.Functor.obj.{max u2 u3, max u5 u2 u3, max u1 u3 u2 u5, max u3 (max u2 u3) u5 (succ (max u2 u3))} (Opposite.{succ (max u1 u3 u2 u5)} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1)) (CategoryTheory.Category.opposite.{max u2 u3, max u1 u3 u2 u5} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1) (CategoryTheory.Functor.category.{u1, u3, u2, u5} J _inst_3 C _inst_1)) (CategoryTheory.Functor.{u3, max u2 u3, u5, succ (max u2 u3)} C _inst_1 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Functor.category.{u3, max u2 u3, u5, succ (max u2 u3)} C _inst_1 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.cocones.{u1, u3, u2, u5} J _inst_3 C _inst_1) (Opposite.op.{succ (max u1 u3 u2 u5)} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1) K))) Y))
but is expected to have type
  forall {C : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u3, u5} C] {D : Type.{u6}} [_inst_2 : CategoryTheory.Category.{u4, u6} D] {F : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} {G : CategoryTheory.Functor.{u4, u3, u6, u5} D _inst_2 C _inst_1}, (CategoryTheory.Adjunction.{u3, u4, u5, u6} C _inst_1 D _inst_2 F G) -> (forall {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1} (Y : D), (Prefunctor.obj.{succ u4, max (succ u2) (succ u4), u6, max (succ u2) (succ u4)} D (CategoryTheory.CategoryStruct.toQuiver.{u4, u6} D (CategoryTheory.Category.toCategoryStruct.{u4, u6} D _inst_2)) Type.{max u2 u4} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u4, max (succ u2) (succ u4)} Type.{max u2 u4} (CategoryTheory.Category.toCategoryStruct.{max u2 u4, max (succ u2) (succ u4)} Type.{max u2 u4} CategoryTheory.types.{max u2 u4})) (CategoryTheory.Functor.toPrefunctor.{u4, max u2 u4, u6, max (succ u2) (succ u4)} D _inst_2 Type.{max u2 u4} CategoryTheory.types.{max u2 u4} (Prefunctor.obj.{max (succ u2) (succ u4), max (max (succ u2) (succ u6)) (succ u4), max (max (max u2 u6) u1) u4, max (max (succ u2) u6) (succ u4)} (Opposite.{max (max (max (succ u6) (succ u2)) (succ u4)) (succ u1)} (CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2)) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u4, max (max (max u2 u6) u1) u4} (Opposite.{max (max (max (succ u6) (succ u2)) (succ u4)) (succ u1)} (CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2)) (CategoryTheory.Category.toCategoryStruct.{max u2 u4, max (max (max u2 u6) u1) u4} (Opposite.{max (max (max (succ u6) (succ u2)) (succ u4)) (succ u1)} (CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2)) (CategoryTheory.Category.opposite.{max u2 u4, max (max (max u2 u6) u1) u4} (CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u4, u2, u6} J _inst_3 D _inst_2)))) (CategoryTheory.Functor.{u4, max u2 u4, u6, max (succ u2) (succ u4)} D _inst_2 Type.{max u2 u4} CategoryTheory.types.{max u2 u4}) (CategoryTheory.CategoryStruct.toQuiver.{max (max u2 u6) u4, max (max (succ u2) u6) (succ u4)} (CategoryTheory.Functor.{u4, max u2 u4, u6, max (succ u2) (succ u4)} D _inst_2 Type.{max u2 u4} CategoryTheory.types.{max u2 u4}) (CategoryTheory.Category.toCategoryStruct.{max (max u2 u6) u4, max (max (succ u2) u6) (succ u4)} (CategoryTheory.Functor.{u4, max u2 u4, u6, max (succ u2) (succ u4)} D _inst_2 Type.{max u2 u4} CategoryTheory.types.{max u2 u4}) (CategoryTheory.Functor.category.{u4, max u2 u4, u6, max (succ u2) (succ u4)} D _inst_2 Type.{max u2 u4} CategoryTheory.types.{max u2 u4}))) (CategoryTheory.Functor.toPrefunctor.{max u2 u4, max (max u2 u6) u4, max (max (max u2 u6) u1) u4, max (max (succ u2) u6) (succ u4)} (Opposite.{max (max (max (succ u6) (succ u2)) (succ u4)) (succ u1)} (CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2)) (CategoryTheory.Category.opposite.{max u2 u4, max (max (max u2 u6) u1) u4} (CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u4, u2, u6} J _inst_3 D _inst_2)) (CategoryTheory.Functor.{u4, max u2 u4, u6, max (succ u2) (succ u4)} D _inst_2 Type.{max u2 u4} CategoryTheory.types.{max u2 u4}) (CategoryTheory.Functor.category.{u4, max u2 u4, u6, max (succ u2) (succ u4)} D _inst_2 Type.{max u2 u4} CategoryTheory.types.{max u2 u4}) (CategoryTheory.cocones.{u1, u4, u2, u6} J _inst_3 D _inst_2)) (Opposite.op.{max (max (max (succ u2) (succ u6)) (succ u1)) (succ u4)} (CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2) (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)))) Y) -> (Prefunctor.obj.{succ u4, max (succ u2) (succ u3), u6, max (succ u2) (succ u3)} D (CategoryTheory.CategoryStruct.toQuiver.{u4, u6} D (CategoryTheory.Category.toCategoryStruct.{u4, u6} D _inst_2)) Type.{max u2 u3} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u3, max (succ u2) (succ u3)} Type.{max u2 u3} (CategoryTheory.Category.toCategoryStruct.{max u2 u3, max (succ u2) (succ u3)} Type.{max u2 u3} CategoryTheory.types.{max u2 u3})) (CategoryTheory.Functor.toPrefunctor.{u4, max u2 u3, u6, max (succ u2) (succ u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3} (CategoryTheory.Functor.comp.{u4, u3, max u2 u3, u6, u5, max (succ u2) (succ u3)} D _inst_2 C _inst_1 Type.{max u2 u3} CategoryTheory.types.{max u2 u3} G (Prefunctor.obj.{max (succ u2) (succ u3), max (max (succ u2) (succ u5)) (succ u3), max (max (max u2 u5) u1) u3, max (max (succ u2) u5) (succ u3)} (Opposite.{max (max (max (succ u5) (succ u2)) (succ u3)) (succ u1)} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1)) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u3, max (max (max u2 u5) u1) u3} (Opposite.{max (max (max (succ u5) (succ u2)) (succ u3)) (succ u1)} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1)) (CategoryTheory.Category.toCategoryStruct.{max u2 u3, max (max (max u2 u5) u1) u3} (Opposite.{max (max (max (succ u5) (succ u2)) (succ u3)) (succ u1)} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1)) (CategoryTheory.Category.opposite.{max u2 u3, max (max (max u2 u5) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1) (CategoryTheory.Functor.category.{u1, u3, u2, u5} J _inst_3 C _inst_1)))) (CategoryTheory.Functor.{u3, max u2 u3, u5, max (succ u2) (succ u3)} C _inst_1 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.CategoryStruct.toQuiver.{max (max u2 u5) u3, max (max (succ u2) u5) (succ u3)} (CategoryTheory.Functor.{u3, max u2 u3, u5, max (succ u2) (succ u3)} C _inst_1 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Category.toCategoryStruct.{max (max u2 u5) u3, max (max (succ u2) u5) (succ u3)} (CategoryTheory.Functor.{u3, max u2 u3, u5, max (succ u2) (succ u3)} C _inst_1 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Functor.category.{u3, max u2 u3, u5, max (succ u2) (succ u3)} C _inst_1 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}))) (CategoryTheory.Functor.toPrefunctor.{max u2 u3, max (max u2 u5) u3, max (max (max u2 u5) u1) u3, max (max (succ u2) u5) (succ u3)} (Opposite.{max (max (max (succ u5) (succ u2)) (succ u3)) (succ u1)} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1)) (CategoryTheory.Category.opposite.{max u2 u3, max (max (max u2 u5) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1) (CategoryTheory.Functor.category.{u1, u3, u2, u5} J _inst_3 C _inst_1)) (CategoryTheory.Functor.{u3, max u2 u3, u5, max (succ u2) (succ u3)} C _inst_1 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Functor.category.{u3, max u2 u3, u5, max (succ u2) (succ u3)} C _inst_1 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.cocones.{u1, u3, u2, u5} J _inst_3 C _inst_1)) (Opposite.op.{max (max (max (succ u2) (succ u5)) (succ u1)) (succ u3)} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1) K)))) Y))
Case conversion may be inaccurate. Consider using '#align category_theory.adjunction.cocones_iso_component_hom CategoryTheory.Adjunction.coconesIsoComponentHomₓ'. -/
/-- auxiliary construction for `cocones_iso` -/
@[simps]
def coconesIsoComponentHom {J : Type u} [Category.{v} J] {K : J ⥤ C} (Y : D)
    (t : ((cocones J D).obj (op (K ⋙ F))).obj Y) : (G ⋙ (cocones J C).obj (op K)).obj Y
    where
  app j := (adj.homEquiv (K.obj j) Y) (t.app j)
  naturality' j j' f := by
    erw [← adj.hom_equiv_naturality_left, t.naturality]
    dsimp
    simp
#align category_theory.adjunction.cocones_iso_component_hom CategoryTheory.Adjunction.coconesIsoComponentHom

/- warning: category_theory.adjunction.cocones_iso_component_inv -> CategoryTheory.Adjunction.coconesIsoComponentInv is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u3, u5} C] {D : Type.{u6}} [_inst_2 : CategoryTheory.Category.{u4, u6} D] {F : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} {G : CategoryTheory.Functor.{u4, u3, u6, u5} D _inst_2 C _inst_1}, (CategoryTheory.Adjunction.{u3, u4, u5, u6} C _inst_1 D _inst_2 F G) -> (forall {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1} (Y : D), (CategoryTheory.Functor.obj.{u4, max u2 u3, u6, succ (max u2 u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3} (CategoryTheory.Functor.comp.{u4, u3, max u2 u3, u6, u5, succ (max u2 u3)} D _inst_2 C _inst_1 Type.{max u2 u3} CategoryTheory.types.{max u2 u3} G (CategoryTheory.Functor.obj.{max u2 u3, max u5 u2 u3, max u1 u3 u2 u5, max u3 (max u2 u3) u5 (succ (max u2 u3))} (Opposite.{succ (max u1 u3 u2 u5)} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1)) (CategoryTheory.Category.opposite.{max u2 u3, max u1 u3 u2 u5} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1) (CategoryTheory.Functor.category.{u1, u3, u2, u5} J _inst_3 C _inst_1)) (CategoryTheory.Functor.{u3, max u2 u3, u5, succ (max u2 u3)} C _inst_1 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Functor.category.{u3, max u2 u3, u5, succ (max u2 u3)} C _inst_1 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.cocones.{u1, u3, u2, u5} J _inst_3 C _inst_1) (Opposite.op.{succ (max u1 u3 u2 u5)} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1) K))) Y) -> (CategoryTheory.Functor.obj.{u4, max u2 u4, u6, succ (max u2 u4)} D _inst_2 Type.{max u2 u4} CategoryTheory.types.{max u2 u4} (CategoryTheory.Functor.obj.{max u2 u4, max u6 u2 u4, max u1 u4 u2 u6, max u4 (max u2 u4) u6 (succ (max u2 u4))} (Opposite.{succ (max u1 u4 u2 u6)} (CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2)) (CategoryTheory.Category.opposite.{max u2 u4, max u1 u4 u2 u6} (CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u4, u2, u6} J _inst_3 D _inst_2)) (CategoryTheory.Functor.{u4, max u2 u4, u6, succ (max u2 u4)} D _inst_2 Type.{max u2 u4} CategoryTheory.types.{max u2 u4}) (CategoryTheory.Functor.category.{u4, max u2 u4, u6, succ (max u2 u4)} D _inst_2 Type.{max u2 u4} CategoryTheory.types.{max u2 u4}) (CategoryTheory.cocones.{u1, u4, u2, u6} J _inst_3 D _inst_2) (Opposite.op.{succ (max u1 u4 u2 u6)} (CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2) (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F))) Y))
but is expected to have type
  forall {C : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u3, u5} C] {D : Type.{u6}} [_inst_2 : CategoryTheory.Category.{u4, u6} D] {F : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} {G : CategoryTheory.Functor.{u4, u3, u6, u5} D _inst_2 C _inst_1}, (CategoryTheory.Adjunction.{u3, u4, u5, u6} C _inst_1 D _inst_2 F G) -> (forall {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1} (Y : D), (Prefunctor.obj.{succ u4, max (succ u2) (succ u3), u6, max (succ u2) (succ u3)} D (CategoryTheory.CategoryStruct.toQuiver.{u4, u6} D (CategoryTheory.Category.toCategoryStruct.{u4, u6} D _inst_2)) Type.{max u2 u3} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u3, max (succ u2) (succ u3)} Type.{max u2 u3} (CategoryTheory.Category.toCategoryStruct.{max u2 u3, max (succ u2) (succ u3)} Type.{max u2 u3} CategoryTheory.types.{max u2 u3})) (CategoryTheory.Functor.toPrefunctor.{u4, max u2 u3, u6, max (succ u2) (succ u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3} (CategoryTheory.Functor.comp.{u4, u3, max u2 u3, u6, u5, max (succ u2) (succ u3)} D _inst_2 C _inst_1 Type.{max u2 u3} CategoryTheory.types.{max u2 u3} G (Prefunctor.obj.{max (succ u2) (succ u3), max (max (succ u2) (succ u5)) (succ u3), max (max (max u2 u5) u1) u3, max (max (succ u2) u5) (succ u3)} (Opposite.{max (max (max (succ u5) (succ u2)) (succ u3)) (succ u1)} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1)) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u3, max (max (max u2 u5) u1) u3} (Opposite.{max (max (max (succ u5) (succ u2)) (succ u3)) (succ u1)} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1)) (CategoryTheory.Category.toCategoryStruct.{max u2 u3, max (max (max u2 u5) u1) u3} (Opposite.{max (max (max (succ u5) (succ u2)) (succ u3)) (succ u1)} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1)) (CategoryTheory.Category.opposite.{max u2 u3, max (max (max u2 u5) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1) (CategoryTheory.Functor.category.{u1, u3, u2, u5} J _inst_3 C _inst_1)))) (CategoryTheory.Functor.{u3, max u2 u3, u5, max (succ u2) (succ u3)} C _inst_1 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.CategoryStruct.toQuiver.{max (max u2 u5) u3, max (max (succ u2) u5) (succ u3)} (CategoryTheory.Functor.{u3, max u2 u3, u5, max (succ u2) (succ u3)} C _inst_1 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Category.toCategoryStruct.{max (max u2 u5) u3, max (max (succ u2) u5) (succ u3)} (CategoryTheory.Functor.{u3, max u2 u3, u5, max (succ u2) (succ u3)} C _inst_1 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Functor.category.{u3, max u2 u3, u5, max (succ u2) (succ u3)} C _inst_1 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}))) (CategoryTheory.Functor.toPrefunctor.{max u2 u3, max (max u2 u5) u3, max (max (max u2 u5) u1) u3, max (max (succ u2) u5) (succ u3)} (Opposite.{max (max (max (succ u5) (succ u2)) (succ u3)) (succ u1)} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1)) (CategoryTheory.Category.opposite.{max u2 u3, max (max (max u2 u5) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1) (CategoryTheory.Functor.category.{u1, u3, u2, u5} J _inst_3 C _inst_1)) (CategoryTheory.Functor.{u3, max u2 u3, u5, max (succ u2) (succ u3)} C _inst_1 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Functor.category.{u3, max u2 u3, u5, max (succ u2) (succ u3)} C _inst_1 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.cocones.{u1, u3, u2, u5} J _inst_3 C _inst_1)) (Opposite.op.{max (max (max (succ u2) (succ u5)) (succ u1)) (succ u3)} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1) K)))) Y) -> (Prefunctor.obj.{succ u4, max (succ u2) (succ u4), u6, max (succ u2) (succ u4)} D (CategoryTheory.CategoryStruct.toQuiver.{u4, u6} D (CategoryTheory.Category.toCategoryStruct.{u4, u6} D _inst_2)) Type.{max u2 u4} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u4, max (succ u2) (succ u4)} Type.{max u2 u4} (CategoryTheory.Category.toCategoryStruct.{max u2 u4, max (succ u2) (succ u4)} Type.{max u2 u4} CategoryTheory.types.{max u2 u4})) (CategoryTheory.Functor.toPrefunctor.{u4, max u2 u4, u6, max (succ u2) (succ u4)} D _inst_2 Type.{max u2 u4} CategoryTheory.types.{max u2 u4} (Prefunctor.obj.{max (succ u2) (succ u4), max (max (succ u2) (succ u6)) (succ u4), max (max (max u2 u6) u1) u4, max (max (succ u2) u6) (succ u4)} (Opposite.{max (max (max (succ u6) (succ u2)) (succ u4)) (succ u1)} (CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2)) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u4, max (max (max u2 u6) u1) u4} (Opposite.{max (max (max (succ u6) (succ u2)) (succ u4)) (succ u1)} (CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2)) (CategoryTheory.Category.toCategoryStruct.{max u2 u4, max (max (max u2 u6) u1) u4} (Opposite.{max (max (max (succ u6) (succ u2)) (succ u4)) (succ u1)} (CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2)) (CategoryTheory.Category.opposite.{max u2 u4, max (max (max u2 u6) u1) u4} (CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u4, u2, u6} J _inst_3 D _inst_2)))) (CategoryTheory.Functor.{u4, max u2 u4, u6, max (succ u2) (succ u4)} D _inst_2 Type.{max u2 u4} CategoryTheory.types.{max u2 u4}) (CategoryTheory.CategoryStruct.toQuiver.{max (max u2 u6) u4, max (max (succ u2) u6) (succ u4)} (CategoryTheory.Functor.{u4, max u2 u4, u6, max (succ u2) (succ u4)} D _inst_2 Type.{max u2 u4} CategoryTheory.types.{max u2 u4}) (CategoryTheory.Category.toCategoryStruct.{max (max u2 u6) u4, max (max (succ u2) u6) (succ u4)} (CategoryTheory.Functor.{u4, max u2 u4, u6, max (succ u2) (succ u4)} D _inst_2 Type.{max u2 u4} CategoryTheory.types.{max u2 u4}) (CategoryTheory.Functor.category.{u4, max u2 u4, u6, max (succ u2) (succ u4)} D _inst_2 Type.{max u2 u4} CategoryTheory.types.{max u2 u4}))) (CategoryTheory.Functor.toPrefunctor.{max u2 u4, max (max u2 u6) u4, max (max (max u2 u6) u1) u4, max (max (succ u2) u6) (succ u4)} (Opposite.{max (max (max (succ u6) (succ u2)) (succ u4)) (succ u1)} (CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2)) (CategoryTheory.Category.opposite.{max u2 u4, max (max (max u2 u6) u1) u4} (CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u4, u2, u6} J _inst_3 D _inst_2)) (CategoryTheory.Functor.{u4, max u2 u4, u6, max (succ u2) (succ u4)} D _inst_2 Type.{max u2 u4} CategoryTheory.types.{max u2 u4}) (CategoryTheory.Functor.category.{u4, max u2 u4, u6, max (succ u2) (succ u4)} D _inst_2 Type.{max u2 u4} CategoryTheory.types.{max u2 u4}) (CategoryTheory.cocones.{u1, u4, u2, u6} J _inst_3 D _inst_2)) (Opposite.op.{max (max (max (succ u2) (succ u6)) (succ u1)) (succ u4)} (CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2) (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)))) Y))
Case conversion may be inaccurate. Consider using '#align category_theory.adjunction.cocones_iso_component_inv CategoryTheory.Adjunction.coconesIsoComponentInvₓ'. -/
/-- auxiliary construction for `cocones_iso` -/
@[simps]
def coconesIsoComponentInv {J : Type u} [Category.{v} J] {K : J ⥤ C} (Y : D)
    (t : (G ⋙ (cocones J C).obj (op K)).obj Y) : ((cocones J D).obj (op (K ⋙ F))).obj Y
    where
  app j := (adj.homEquiv (K.obj j) Y).symm (t.app j)
  naturality' j j' f :=
    by
    erw [← adj.hom_equiv_naturality_left_symm, ← adj.hom_equiv_naturality_right_symm, t.naturality]
    dsimp; simp
#align category_theory.adjunction.cocones_iso_component_inv CategoryTheory.Adjunction.coconesIsoComponentInv

/- warning: category_theory.adjunction.cones_iso_component_hom -> CategoryTheory.Adjunction.conesIsoComponentHom is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u3, u5} C] {D : Type.{u6}} [_inst_2 : CategoryTheory.Category.{u4, u6} D] {F : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} {G : CategoryTheory.Functor.{u4, u3, u6, u5} D _inst_2 C _inst_1}, (CategoryTheory.Adjunction.{u3, u4, u5, u6} C _inst_1 D _inst_2 F G) -> (forall {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2} (X : Opposite.{succ u5} C), (CategoryTheory.Functor.obj.{u3, max u2 u4, u5, succ (max u2 u4)} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1) Type.{max u2 u4} CategoryTheory.types.{max u2 u4} (CategoryTheory.Functor.comp.{u3, u4, max u2 u4, u5, u6, succ (max u2 u4)} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1) (Opposite.{succ u6} D) (CategoryTheory.Category.opposite.{u4, u6} D _inst_2) Type.{max u2 u4} CategoryTheory.types.{max u2 u4} (CategoryTheory.Functor.op.{u3, u4, u5, u6} C _inst_1 D _inst_2 F) (CategoryTheory.Functor.obj.{max u2 u4, max u6 u2 u4, max u1 u4 u2 u6, max u4 (max u2 u4) u6 (succ (max u2 u4))} (CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u4, u2, u6} J _inst_3 D _inst_2) (CategoryTheory.Functor.{u4, max u2 u4, u6, succ (max u2 u4)} (Opposite.{succ u6} D) (CategoryTheory.Category.opposite.{u4, u6} D _inst_2) Type.{max u2 u4} CategoryTheory.types.{max u2 u4}) (CategoryTheory.Functor.category.{u4, max u2 u4, u6, succ (max u2 u4)} (Opposite.{succ u6} D) (CategoryTheory.Category.opposite.{u4, u6} D _inst_2) Type.{max u2 u4} CategoryTheory.types.{max u2 u4}) (CategoryTheory.cones.{u1, u4, u2, u6} J _inst_3 D _inst_2) K)) X) -> (CategoryTheory.Functor.obj.{u3, max u2 u3, u5, succ (max u2 u3)} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3} (CategoryTheory.Functor.obj.{max u2 u3, max u5 u2 u3, max u1 u3 u2 u5, max u3 (max u2 u3) u5 (succ (max u2 u3))} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1) (CategoryTheory.Functor.category.{u1, u3, u2, u5} J _inst_3 C _inst_1) (CategoryTheory.Functor.{u3, max u2 u3, u5, succ (max u2 u3)} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Functor.category.{u3, max u2 u3, u5, succ (max u2 u3)} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.cones.{u1, u3, u2, u5} J _inst_3 C _inst_1) (CategoryTheory.Functor.comp.{u1, u4, u3, u2, u6, u5} J _inst_3 D _inst_2 C _inst_1 K G)) X))
but is expected to have type
  forall {C : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u3, u5} C] {D : Type.{u6}} [_inst_2 : CategoryTheory.Category.{u4, u6} D] {F : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} {G : CategoryTheory.Functor.{u4, u3, u6, u5} D _inst_2 C _inst_1}, (CategoryTheory.Adjunction.{u3, u4, u5, u6} C _inst_1 D _inst_2 F G) -> (forall {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2} (X : Opposite.{succ u5} C), (Prefunctor.obj.{succ u3, max (succ u2) (succ u4), u5, max (succ u2) (succ u4)} (Opposite.{succ u5} C) (CategoryTheory.CategoryStruct.toQuiver.{u3, u5} (Opposite.{succ u5} C) (CategoryTheory.Category.toCategoryStruct.{u3, u5} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1))) Type.{max u2 u4} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u4, max (succ u2) (succ u4)} Type.{max u2 u4} (CategoryTheory.Category.toCategoryStruct.{max u2 u4, max (succ u2) (succ u4)} Type.{max u2 u4} CategoryTheory.types.{max u2 u4})) (CategoryTheory.Functor.toPrefunctor.{u3, max u2 u4, u5, max (succ u2) (succ u4)} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1) Type.{max u2 u4} CategoryTheory.types.{max u2 u4} (CategoryTheory.Functor.comp.{u3, u4, max u2 u4, u5, u6, max (succ u2) (succ u4)} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1) (Opposite.{succ u6} D) (CategoryTheory.Category.opposite.{u4, u6} D _inst_2) Type.{max u2 u4} CategoryTheory.types.{max u2 u4} (CategoryTheory.Functor.op.{u3, u4, u5, u6} C _inst_1 D _inst_2 F) (Prefunctor.obj.{max (succ u2) (succ u4), max (max (succ u2) (succ u6)) (succ u4), max (max (max u2 u6) u1) u4, max (max (succ u2) u6) (succ u4)} (CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u4, max (max (max u2 u6) u1) u4} (CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u2 u4, max (max (max u2 u6) u1) u4} (CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u4, u2, u6} J _inst_3 D _inst_2))) (CategoryTheory.Functor.{u4, max u2 u4, u6, max (succ u2) (succ u4)} (Opposite.{succ u6} D) (CategoryTheory.Category.opposite.{u4, u6} D _inst_2) Type.{max u2 u4} CategoryTheory.types.{max u2 u4}) (CategoryTheory.CategoryStruct.toQuiver.{max (max u2 u6) u4, max (max (succ u2) u6) (succ u4)} (CategoryTheory.Functor.{u4, max u2 u4, u6, max (succ u2) (succ u4)} (Opposite.{succ u6} D) (CategoryTheory.Category.opposite.{u4, u6} D _inst_2) Type.{max u2 u4} CategoryTheory.types.{max u2 u4}) (CategoryTheory.Category.toCategoryStruct.{max (max u2 u6) u4, max (max (succ u2) u6) (succ u4)} (CategoryTheory.Functor.{u4, max u2 u4, u6, max (succ u2) (succ u4)} (Opposite.{succ u6} D) (CategoryTheory.Category.opposite.{u4, u6} D _inst_2) Type.{max u2 u4} CategoryTheory.types.{max u2 u4}) (CategoryTheory.Functor.category.{u4, max u2 u4, u6, max (succ u2) (succ u4)} (Opposite.{succ u6} D) (CategoryTheory.Category.opposite.{u4, u6} D _inst_2) Type.{max u2 u4} CategoryTheory.types.{max u2 u4}))) (CategoryTheory.Functor.toPrefunctor.{max u2 u4, max (max u2 u6) u4, max (max (max u2 u6) u1) u4, max (max (succ u2) u6) (succ u4)} (CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u4, u2, u6} J _inst_3 D _inst_2) (CategoryTheory.Functor.{u4, max u2 u4, u6, max (succ u2) (succ u4)} (Opposite.{succ u6} D) (CategoryTheory.Category.opposite.{u4, u6} D _inst_2) Type.{max u2 u4} CategoryTheory.types.{max u2 u4}) (CategoryTheory.Functor.category.{u4, max u2 u4, u6, max (succ u2) (succ u4)} (Opposite.{succ u6} D) (CategoryTheory.Category.opposite.{u4, u6} D _inst_2) Type.{max u2 u4} CategoryTheory.types.{max u2 u4}) (CategoryTheory.cones.{u1, u4, u2, u6} J _inst_3 D _inst_2)) K))) X) -> (Prefunctor.obj.{succ u3, max (succ u2) (succ u3), u5, max (succ u2) (succ u3)} (Opposite.{succ u5} C) (CategoryTheory.CategoryStruct.toQuiver.{u3, u5} (Opposite.{succ u5} C) (CategoryTheory.Category.toCategoryStruct.{u3, u5} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1))) Type.{max u2 u3} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u3, max (succ u2) (succ u3)} Type.{max u2 u3} (CategoryTheory.Category.toCategoryStruct.{max u2 u3, max (succ u2) (succ u3)} Type.{max u2 u3} CategoryTheory.types.{max u2 u3})) (CategoryTheory.Functor.toPrefunctor.{u3, max u2 u3, u5, max (succ u2) (succ u3)} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3} (Prefunctor.obj.{max (succ u2) (succ u3), max (max (succ u2) (succ u5)) (succ u3), max (max (max u2 u5) u1) u3, max (max (succ u2) u5) (succ u3)} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u3, max (max (max u2 u5) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u2 u3, max (max (max u2 u5) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1) (CategoryTheory.Functor.category.{u1, u3, u2, u5} J _inst_3 C _inst_1))) (CategoryTheory.Functor.{u3, max u2 u3, u5, max (succ u2) (succ u3)} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.CategoryStruct.toQuiver.{max (max u2 u5) u3, max (max (succ u2) u5) (succ u3)} (CategoryTheory.Functor.{u3, max u2 u3, u5, max (succ u2) (succ u3)} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Category.toCategoryStruct.{max (max u2 u5) u3, max (max (succ u2) u5) (succ u3)} (CategoryTheory.Functor.{u3, max u2 u3, u5, max (succ u2) (succ u3)} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Functor.category.{u3, max u2 u3, u5, max (succ u2) (succ u3)} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}))) (CategoryTheory.Functor.toPrefunctor.{max u2 u3, max (max u2 u5) u3, max (max (max u2 u5) u1) u3, max (max (succ u2) u5) (succ u3)} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1) (CategoryTheory.Functor.category.{u1, u3, u2, u5} J _inst_3 C _inst_1) (CategoryTheory.Functor.{u3, max u2 u3, u5, max (succ u2) (succ u3)} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Functor.category.{u3, max u2 u3, u5, max (succ u2) (succ u3)} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.cones.{u1, u3, u2, u5} J _inst_3 C _inst_1)) (CategoryTheory.Functor.comp.{u1, u4, u3, u2, u6, u5} J _inst_3 D _inst_2 C _inst_1 K G))) X))
Case conversion may be inaccurate. Consider using '#align category_theory.adjunction.cones_iso_component_hom CategoryTheory.Adjunction.conesIsoComponentHomₓ'. -/
/-- auxiliary construction for `cones_iso` -/
@[simps]
def conesIsoComponentHom {J : Type u} [Category.{v} J] {K : J ⥤ D} (X : Cᵒᵖ)
    (t : (Functor.op F ⋙ (cones J D).obj K).obj X) : ((cones J C).obj (K ⋙ G)).obj X
    where
  app j := (adj.homEquiv (unop X) (K.obj j)) (t.app j)
  naturality' j j' f :=
    by
    erw [← adj.hom_equiv_naturality_right, ← t.naturality, category.id_comp, category.id_comp]
    rfl
#align category_theory.adjunction.cones_iso_component_hom CategoryTheory.Adjunction.conesIsoComponentHom

/- warning: category_theory.adjunction.cones_iso_component_inv -> CategoryTheory.Adjunction.conesIsoComponentInv is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u3, u5} C] {D : Type.{u6}} [_inst_2 : CategoryTheory.Category.{u4, u6} D] {F : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} {G : CategoryTheory.Functor.{u4, u3, u6, u5} D _inst_2 C _inst_1}, (CategoryTheory.Adjunction.{u3, u4, u5, u6} C _inst_1 D _inst_2 F G) -> (forall {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2} (X : Opposite.{succ u5} C), (CategoryTheory.Functor.obj.{u3, max u2 u3, u5, succ (max u2 u3)} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3} (CategoryTheory.Functor.obj.{max u2 u3, max u5 u2 u3, max u1 u3 u2 u5, max u3 (max u2 u3) u5 (succ (max u2 u3))} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1) (CategoryTheory.Functor.category.{u1, u3, u2, u5} J _inst_3 C _inst_1) (CategoryTheory.Functor.{u3, max u2 u3, u5, succ (max u2 u3)} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Functor.category.{u3, max u2 u3, u5, succ (max u2 u3)} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.cones.{u1, u3, u2, u5} J _inst_3 C _inst_1) (CategoryTheory.Functor.comp.{u1, u4, u3, u2, u6, u5} J _inst_3 D _inst_2 C _inst_1 K G)) X) -> (CategoryTheory.Functor.obj.{u3, max u2 u4, u5, succ (max u2 u4)} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1) Type.{max u2 u4} CategoryTheory.types.{max u2 u4} (CategoryTheory.Functor.comp.{u3, u4, max u2 u4, u5, u6, succ (max u2 u4)} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1) (Opposite.{succ u6} D) (CategoryTheory.Category.opposite.{u4, u6} D _inst_2) Type.{max u2 u4} CategoryTheory.types.{max u2 u4} (CategoryTheory.Functor.op.{u3, u4, u5, u6} C _inst_1 D _inst_2 F) (CategoryTheory.Functor.obj.{max u2 u4, max u6 u2 u4, max u1 u4 u2 u6, max u4 (max u2 u4) u6 (succ (max u2 u4))} (CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u4, u2, u6} J _inst_3 D _inst_2) (CategoryTheory.Functor.{u4, max u2 u4, u6, succ (max u2 u4)} (Opposite.{succ u6} D) (CategoryTheory.Category.opposite.{u4, u6} D _inst_2) Type.{max u2 u4} CategoryTheory.types.{max u2 u4}) (CategoryTheory.Functor.category.{u4, max u2 u4, u6, succ (max u2 u4)} (Opposite.{succ u6} D) (CategoryTheory.Category.opposite.{u4, u6} D _inst_2) Type.{max u2 u4} CategoryTheory.types.{max u2 u4}) (CategoryTheory.cones.{u1, u4, u2, u6} J _inst_3 D _inst_2) K)) X))
but is expected to have type
  forall {C : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u3, u5} C] {D : Type.{u6}} [_inst_2 : CategoryTheory.Category.{u4, u6} D] {F : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} {G : CategoryTheory.Functor.{u4, u3, u6, u5} D _inst_2 C _inst_1}, (CategoryTheory.Adjunction.{u3, u4, u5, u6} C _inst_1 D _inst_2 F G) -> (forall {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2} (X : Opposite.{succ u5} C), (Prefunctor.obj.{succ u3, max (succ u2) (succ u3), u5, max (succ u2) (succ u3)} (Opposite.{succ u5} C) (CategoryTheory.CategoryStruct.toQuiver.{u3, u5} (Opposite.{succ u5} C) (CategoryTheory.Category.toCategoryStruct.{u3, u5} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1))) Type.{max u2 u3} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u3, max (succ u2) (succ u3)} Type.{max u2 u3} (CategoryTheory.Category.toCategoryStruct.{max u2 u3, max (succ u2) (succ u3)} Type.{max u2 u3} CategoryTheory.types.{max u2 u3})) (CategoryTheory.Functor.toPrefunctor.{u3, max u2 u3, u5, max (succ u2) (succ u3)} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3} (Prefunctor.obj.{max (succ u2) (succ u3), max (max (succ u2) (succ u5)) (succ u3), max (max (max u2 u5) u1) u3, max (max (succ u2) u5) (succ u3)} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u3, max (max (max u2 u5) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u2 u3, max (max (max u2 u5) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1) (CategoryTheory.Functor.category.{u1, u3, u2, u5} J _inst_3 C _inst_1))) (CategoryTheory.Functor.{u3, max u2 u3, u5, max (succ u2) (succ u3)} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.CategoryStruct.toQuiver.{max (max u2 u5) u3, max (max (succ u2) u5) (succ u3)} (CategoryTheory.Functor.{u3, max u2 u3, u5, max (succ u2) (succ u3)} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Category.toCategoryStruct.{max (max u2 u5) u3, max (max (succ u2) u5) (succ u3)} (CategoryTheory.Functor.{u3, max u2 u3, u5, max (succ u2) (succ u3)} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Functor.category.{u3, max u2 u3, u5, max (succ u2) (succ u3)} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}))) (CategoryTheory.Functor.toPrefunctor.{max u2 u3, max (max u2 u5) u3, max (max (max u2 u5) u1) u3, max (max (succ u2) u5) (succ u3)} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1) (CategoryTheory.Functor.category.{u1, u3, u2, u5} J _inst_3 C _inst_1) (CategoryTheory.Functor.{u3, max u2 u3, u5, max (succ u2) (succ u3)} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Functor.category.{u3, max u2 u3, u5, max (succ u2) (succ u3)} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.cones.{u1, u3, u2, u5} J _inst_3 C _inst_1)) (CategoryTheory.Functor.comp.{u1, u4, u3, u2, u6, u5} J _inst_3 D _inst_2 C _inst_1 K G))) X) -> (Prefunctor.obj.{succ u3, max (succ u2) (succ u4), u5, max (succ u2) (succ u4)} (Opposite.{succ u5} C) (CategoryTheory.CategoryStruct.toQuiver.{u3, u5} (Opposite.{succ u5} C) (CategoryTheory.Category.toCategoryStruct.{u3, u5} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1))) Type.{max u2 u4} (CategoryTheory.CategoryStruct.toQuiver.{max u2 u4, max (succ u2) (succ u4)} Type.{max u2 u4} (CategoryTheory.Category.toCategoryStruct.{max u2 u4, max (succ u2) (succ u4)} Type.{max u2 u4} CategoryTheory.types.{max u2 u4})) (CategoryTheory.Functor.toPrefunctor.{u3, max u2 u4, u5, max (succ u2) (succ u4)} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1) Type.{max u2 u4} CategoryTheory.types.{max u2 u4} (CategoryTheory.Functor.comp.{u3, u4, max u2 u4, u5, u6, max (succ u2) (succ u4)} (Opposite.{succ u5} C) (CategoryTheory.Category.opposite.{u3, u5} C _inst_1) (Opposite.{succ u6} D) (CategoryTheory.Category.opposite.{u4, u6} D _inst_2) Type.{max u2 u4} CategoryTheory.types.{max u2 u4} (CategoryTheory.Functor.op.{u3, u4, u5, u6} C _inst_1 D _inst_2 F) (Prefunctor.obj.{max (succ u2) (succ u4), max (max (succ u2) (succ u6)) (succ u4), max (max (max u2 u6) u1) u4, max (max (succ u2) u6) (succ u4)} (CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u4, max (max (max u2 u6) u1) u4} (CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u2 u4, max (max (max u2 u6) u1) u4} (CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u4, u2, u6} J _inst_3 D _inst_2))) (CategoryTheory.Functor.{u4, max u2 u4, u6, max (succ u2) (succ u4)} (Opposite.{succ u6} D) (CategoryTheory.Category.opposite.{u4, u6} D _inst_2) Type.{max u2 u4} CategoryTheory.types.{max u2 u4}) (CategoryTheory.CategoryStruct.toQuiver.{max (max u2 u6) u4, max (max (succ u2) u6) (succ u4)} (CategoryTheory.Functor.{u4, max u2 u4, u6, max (succ u2) (succ u4)} (Opposite.{succ u6} D) (CategoryTheory.Category.opposite.{u4, u6} D _inst_2) Type.{max u2 u4} CategoryTheory.types.{max u2 u4}) (CategoryTheory.Category.toCategoryStruct.{max (max u2 u6) u4, max (max (succ u2) u6) (succ u4)} (CategoryTheory.Functor.{u4, max u2 u4, u6, max (succ u2) (succ u4)} (Opposite.{succ u6} D) (CategoryTheory.Category.opposite.{u4, u6} D _inst_2) Type.{max u2 u4} CategoryTheory.types.{max u2 u4}) (CategoryTheory.Functor.category.{u4, max u2 u4, u6, max (succ u2) (succ u4)} (Opposite.{succ u6} D) (CategoryTheory.Category.opposite.{u4, u6} D _inst_2) Type.{max u2 u4} CategoryTheory.types.{max u2 u4}))) (CategoryTheory.Functor.toPrefunctor.{max u2 u4, max (max u2 u6) u4, max (max (max u2 u6) u1) u4, max (max (succ u2) u6) (succ u4)} (CategoryTheory.Functor.{u1, u4, u2, u6} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u4, u2, u6} J _inst_3 D _inst_2) (CategoryTheory.Functor.{u4, max u2 u4, u6, max (succ u2) (succ u4)} (Opposite.{succ u6} D) (CategoryTheory.Category.opposite.{u4, u6} D _inst_2) Type.{max u2 u4} CategoryTheory.types.{max u2 u4}) (CategoryTheory.Functor.category.{u4, max u2 u4, u6, max (succ u2) (succ u4)} (Opposite.{succ u6} D) (CategoryTheory.Category.opposite.{u4, u6} D _inst_2) Type.{max u2 u4} CategoryTheory.types.{max u2 u4}) (CategoryTheory.cones.{u1, u4, u2, u6} J _inst_3 D _inst_2)) K))) X))
Case conversion may be inaccurate. Consider using '#align category_theory.adjunction.cones_iso_component_inv CategoryTheory.Adjunction.conesIsoComponentInvₓ'. -/
/-- auxiliary construction for `cones_iso` -/
@[simps]
def conesIsoComponentInv {J : Type u} [Category.{v} J] {K : J ⥤ D} (X : Cᵒᵖ)
    (t : ((cones J C).obj (K ⋙ G)).obj X) : (Functor.op F ⋙ (cones J D).obj K).obj X
    where
  app j := (adj.homEquiv (unop X) (K.obj j)).symm (t.app j)
  naturality' j j' f := by
    erw [← adj.hom_equiv_naturality_right_symm, ← t.naturality, category.id_comp, category.id_comp]
#align category_theory.adjunction.cones_iso_component_inv CategoryTheory.Adjunction.conesIsoComponentInv

end ArbitraryUniverse

variable {C : Type u₁} [Category.{v₀} C] {D : Type u₂} [Category.{v₀} D] {F : C ⥤ D} {G : D ⥤ C}
  (adj : F ⊣ G)

/- warning: category_theory.adjunction.cocones_iso -> CategoryTheory.Adjunction.coconesIso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u3, u4} C] {D : Type.{u5}} [_inst_2 : CategoryTheory.Category.{u3, u5} D] {F : CategoryTheory.Functor.{u3, u3, u4, u5} C _inst_1 D _inst_2} {G : CategoryTheory.Functor.{u3, u3, u5, u4} D _inst_2 C _inst_1}, (CategoryTheory.Adjunction.{u3, u3, u4, u5} C _inst_1 D _inst_2 F G) -> (forall {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_3 C _inst_1}, CategoryTheory.Iso.{max u5 u2 u3, max u3 (max u2 u3) u5 (succ (max u2 u3))} (CategoryTheory.Functor.{u3, max u2 u3, u5, succ (max u2 u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Functor.category.{u3, max u2 u3, u5, succ (max u2 u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Functor.obj.{max u2 u3, max u5 u2 u3, max u1 u3 u2 u5, max u3 (max u2 u3) u5 (succ (max u2 u3))} (Opposite.{succ (max u1 u3 u2 u5)} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 D _inst_2)) (CategoryTheory.Category.opposite.{max u2 u3, max u1 u3 u2 u5} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u5} J _inst_3 D _inst_2)) (CategoryTheory.Functor.{u3, max u2 u3, u5, succ (max u2 u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Functor.category.{u3, max u2 u3, u5, succ (max u2 u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.cocones.{u1, u3, u2, u5} J _inst_3 D _inst_2) (Opposite.op.{succ (max u1 u3 u2 u5)} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 D _inst_2) (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u4, u5} J _inst_3 C _inst_1 D _inst_2 K F))) (CategoryTheory.Functor.comp.{u3, u3, max u2 u3, u5, u4, succ (max u2 u3)} D _inst_2 C _inst_1 Type.{max u2 u3} CategoryTheory.types.{max u2 u3} G (CategoryTheory.Functor.obj.{max u2 u3, max u4 u2 u3, max u1 u3 u2 u4, max u3 (max u2 u3) u4 (succ (max u2 u3))} (Opposite.{succ (max u1 u3 u2 u4)} (CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_3 C _inst_1)) (CategoryTheory.Category.opposite.{max u2 u3, max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_3 C _inst_1) (CategoryTheory.Functor.category.{u1, u3, u2, u4} J _inst_3 C _inst_1)) (CategoryTheory.Functor.{u3, max u2 u3, u4, succ (max u2 u3)} C _inst_1 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Functor.category.{u3, max u2 u3, u4, succ (max u2 u3)} C _inst_1 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.cocones.{u1, u3, u2, u4} J _inst_3 C _inst_1) (Opposite.op.{succ (max u1 u3 u2 u4)} (CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_3 C _inst_1) K))))
but is expected to have type
  forall {C : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u3, u4} C] {D : Type.{u5}} [_inst_2 : CategoryTheory.Category.{u3, u5} D] {F : CategoryTheory.Functor.{u3, u3, u4, u5} C _inst_1 D _inst_2} {G : CategoryTheory.Functor.{u3, u3, u5, u4} D _inst_2 C _inst_1}, (CategoryTheory.Adjunction.{u3, u3, u4, u5} C _inst_1 D _inst_2 F G) -> (forall {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_3 C _inst_1}, CategoryTheory.Iso.{max (max u2 u5) u3, max (max (succ u2) u5) (succ u3)} (CategoryTheory.Functor.{u3, max u2 u3, u5, max (succ u2) (succ u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Functor.category.{u3, max u2 u3, u5, max (succ u2) (succ u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (Prefunctor.obj.{max (succ u2) (succ u3), max (max (succ u2) (succ u5)) (succ u3), max (max (max u2 u5) u1) u3, max (max (succ u2) u5) (succ u3)} (Opposite.{max (max (max (succ u5) (succ u2)) (succ u3)) (succ u1)} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 D _inst_2)) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u3, max (max (max u2 u5) u1) u3} (Opposite.{max (max (max (succ u5) (succ u2)) (succ u3)) (succ u1)} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 D _inst_2)) (CategoryTheory.Category.toCategoryStruct.{max u2 u3, max (max (max u2 u5) u1) u3} (Opposite.{max (max (max (succ u5) (succ u2)) (succ u3)) (succ u1)} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 D _inst_2)) (CategoryTheory.Category.opposite.{max u2 u3, max (max (max u2 u5) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u5} J _inst_3 D _inst_2)))) (CategoryTheory.Functor.{u3, max u2 u3, u5, max (succ u2) (succ u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.CategoryStruct.toQuiver.{max (max u2 u5) u3, max (max (succ u2) u5) (succ u3)} (CategoryTheory.Functor.{u3, max u2 u3, u5, max (succ u2) (succ u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Category.toCategoryStruct.{max (max u2 u5) u3, max (max (succ u2) u5) (succ u3)} (CategoryTheory.Functor.{u3, max u2 u3, u5, max (succ u2) (succ u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Functor.category.{u3, max u2 u3, u5, max (succ u2) (succ u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}))) (CategoryTheory.Functor.toPrefunctor.{max u2 u3, max (max u2 u5) u3, max (max (max u2 u5) u1) u3, max (max (succ u2) u5) (succ u3)} (Opposite.{max (max (max (succ u5) (succ u2)) (succ u3)) (succ u1)} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 D _inst_2)) (CategoryTheory.Category.opposite.{max u2 u3, max (max (max u2 u5) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u5} J _inst_3 D _inst_2)) (CategoryTheory.Functor.{u3, max u2 u3, u5, max (succ u2) (succ u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Functor.category.{u3, max u2 u3, u5, max (succ u2) (succ u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.cocones.{u1, u3, u2, u5} J _inst_3 D _inst_2)) (Opposite.op.{max (max (max (succ u2) (succ u5)) (succ u1)) (succ u3)} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 D _inst_2) (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u4, u5} J _inst_3 C _inst_1 D _inst_2 K F))) (CategoryTheory.Functor.comp.{u3, u3, max u2 u3, u5, u4, max (succ u2) (succ u3)} D _inst_2 C _inst_1 Type.{max u2 u3} CategoryTheory.types.{max u2 u3} G (Prefunctor.obj.{max (succ u2) (succ u3), max (max (succ u2) (succ u4)) (succ u3), max (max (max u2 u4) u1) u3, max (max (succ u2) u4) (succ u3)} (Opposite.{max (max (max (succ u4) (succ u2)) (succ u3)) (succ u1)} (CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_3 C _inst_1)) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u3, max (max (max u2 u4) u1) u3} (Opposite.{max (max (max (succ u4) (succ u2)) (succ u3)) (succ u1)} (CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_3 C _inst_1)) (CategoryTheory.Category.toCategoryStruct.{max u2 u3, max (max (max u2 u4) u1) u3} (Opposite.{max (max (max (succ u4) (succ u2)) (succ u3)) (succ u1)} (CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_3 C _inst_1)) (CategoryTheory.Category.opposite.{max u2 u3, max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_3 C _inst_1) (CategoryTheory.Functor.category.{u1, u3, u2, u4} J _inst_3 C _inst_1)))) (CategoryTheory.Functor.{u3, max u2 u3, u4, max (succ u2) (succ u3)} C _inst_1 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.CategoryStruct.toQuiver.{max (max u2 u4) u3, max (max (succ u2) u4) (succ u3)} (CategoryTheory.Functor.{u3, max u2 u3, u4, max (succ u2) (succ u3)} C _inst_1 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Category.toCategoryStruct.{max (max u2 u4) u3, max (max (succ u2) u4) (succ u3)} (CategoryTheory.Functor.{u3, max u2 u3, u4, max (succ u2) (succ u3)} C _inst_1 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Functor.category.{u3, max u2 u3, u4, max (succ u2) (succ u3)} C _inst_1 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}))) (CategoryTheory.Functor.toPrefunctor.{max u2 u3, max (max u2 u4) u3, max (max (max u2 u4) u1) u3, max (max (succ u2) u4) (succ u3)} (Opposite.{max (max (max (succ u4) (succ u2)) (succ u3)) (succ u1)} (CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_3 C _inst_1)) (CategoryTheory.Category.opposite.{max u2 u3, max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_3 C _inst_1) (CategoryTheory.Functor.category.{u1, u3, u2, u4} J _inst_3 C _inst_1)) (CategoryTheory.Functor.{u3, max u2 u3, u4, max (succ u2) (succ u3)} C _inst_1 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Functor.category.{u3, max u2 u3, u4, max (succ u2) (succ u3)} C _inst_1 Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.cocones.{u1, u3, u2, u4} J _inst_3 C _inst_1)) (Opposite.op.{max (max (max (succ u2) (succ u4)) (succ u1)) (succ u3)} (CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_3 C _inst_1) K))))
Case conversion may be inaccurate. Consider using '#align category_theory.adjunction.cocones_iso CategoryTheory.Adjunction.coconesIsoₓ'. -/
-- Note: this is natural in K, but we do not yet have the tools to formulate that.
/-- When `F ⊣ G`,
the functor associating to each `Y` the cocones over `K ⋙ F` with cone point `Y`
is naturally isomorphic to
the functor associating to each `Y` the cocones over `K` with cone point `G.obj Y`.
-/
def coconesIso {J : Type u} [Category.{v} J] {K : J ⥤ C} :
    (cocones J D).obj (op (K ⋙ F)) ≅ G ⋙ (cocones J C).obj (op K) :=
  NatIso.ofComponents
    (fun Y =>
      { Hom := coconesIsoComponentHom adj Y
        inv := coconesIsoComponentInv adj Y })
    (by tidy)
#align category_theory.adjunction.cocones_iso CategoryTheory.Adjunction.coconesIso

/- warning: category_theory.adjunction.cones_iso -> CategoryTheory.Adjunction.conesIso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u3, u4} C] {D : Type.{u5}} [_inst_2 : CategoryTheory.Category.{u3, u5} D] {F : CategoryTheory.Functor.{u3, u3, u4, u5} C _inst_1 D _inst_2} {G : CategoryTheory.Functor.{u3, u3, u5, u4} D _inst_2 C _inst_1}, (CategoryTheory.Adjunction.{u3, u3, u4, u5} C _inst_1 D _inst_2 F G) -> (forall {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 D _inst_2}, CategoryTheory.Iso.{max u4 u2 u3, max u3 (max u2 u3) u4 (succ (max u2 u3))} (CategoryTheory.Functor.{u3, max u2 u3, u4, succ (max u2 u3)} (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u3, u4} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Functor.category.{u3, max u2 u3, u4, succ (max u2 u3)} (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u3, u4} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Functor.comp.{u3, u3, max u2 u3, u4, u5, succ (max u2 u3)} (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u3, u4} C _inst_1) (Opposite.{succ u5} D) (CategoryTheory.Category.opposite.{u3, u5} D _inst_2) Type.{max u2 u3} CategoryTheory.types.{max u2 u3} (CategoryTheory.Functor.op.{u3, u3, u4, u5} C _inst_1 D _inst_2 F) (CategoryTheory.Functor.obj.{max u2 u3, max u5 u2 u3, max u1 u3 u2 u5, max u3 (max u2 u3) u5 (succ (max u2 u3))} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u5} J _inst_3 D _inst_2) (CategoryTheory.Functor.{u3, max u2 u3, u5, succ (max u2 u3)} (Opposite.{succ u5} D) (CategoryTheory.Category.opposite.{u3, u5} D _inst_2) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Functor.category.{u3, max u2 u3, u5, succ (max u2 u3)} (Opposite.{succ u5} D) (CategoryTheory.Category.opposite.{u3, u5} D _inst_2) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.cones.{u1, u3, u2, u5} J _inst_3 D _inst_2) K)) (CategoryTheory.Functor.obj.{max u2 u3, max u4 u2 u3, max u1 u3 u2 u4, max u3 (max u2 u3) u4 (succ (max u2 u3))} (CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_3 C _inst_1) (CategoryTheory.Functor.category.{u1, u3, u2, u4} J _inst_3 C _inst_1) (CategoryTheory.Functor.{u3, max u2 u3, u4, succ (max u2 u3)} (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u3, u4} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Functor.category.{u3, max u2 u3, u4, succ (max u2 u3)} (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u3, u4} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.cones.{u1, u3, u2, u4} J _inst_3 C _inst_1) (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u5, u4} J _inst_3 D _inst_2 C _inst_1 K G)))
but is expected to have type
  forall {C : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u3, u4} C] {D : Type.{u5}} [_inst_2 : CategoryTheory.Category.{u3, u5} D] {F : CategoryTheory.Functor.{u3, u3, u4, u5} C _inst_1 D _inst_2} {G : CategoryTheory.Functor.{u3, u3, u5, u4} D _inst_2 C _inst_1}, (CategoryTheory.Adjunction.{u3, u3, u4, u5} C _inst_1 D _inst_2 F G) -> (forall {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 D _inst_2}, CategoryTheory.Iso.{max (max u2 u4) u3, max (max (max (max (succ u2) (succ u3)) u4) u2 u3) u3} (CategoryTheory.Functor.{u3, max u2 u3, u4, max (succ u2) (succ u3)} (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u3, u4} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Functor.category.{u3, max u2 u3, u4, max (succ u2) (succ u3)} (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u3, u4} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Functor.comp.{u3, u3, max u2 u3, u4, u5, max (succ u2) (succ u3)} (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u3, u4} C _inst_1) (Opposite.{succ u5} D) (CategoryTheory.Category.opposite.{u3, u5} D _inst_2) Type.{max u2 u3} CategoryTheory.types.{max u2 u3} (CategoryTheory.Functor.op.{u3, u3, u4, u5} C _inst_1 D _inst_2 F) (Prefunctor.obj.{max (succ u2) (succ u3), max (max (succ u2) (succ u5)) (succ u3), max (max (max u2 u5) u1) u3, max (max (succ u2) u5) (succ u3)} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u3, max (max (max u2 u5) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u2 u3, max (max (max u2 u5) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u5} J _inst_3 D _inst_2))) (CategoryTheory.Functor.{u3, max u2 u3, u5, max (succ u2) (succ u3)} (Opposite.{succ u5} D) (CategoryTheory.Category.opposite.{u3, u5} D _inst_2) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.CategoryStruct.toQuiver.{max (max u2 u5) u3, max (max (succ u2) u5) (succ u3)} (CategoryTheory.Functor.{u3, max u2 u3, u5, max (succ u2) (succ u3)} (Opposite.{succ u5} D) (CategoryTheory.Category.opposite.{u3, u5} D _inst_2) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Category.toCategoryStruct.{max (max u2 u5) u3, max (max (succ u2) u5) (succ u3)} (CategoryTheory.Functor.{u3, max u2 u3, u5, max (succ u2) (succ u3)} (Opposite.{succ u5} D) (CategoryTheory.Category.opposite.{u3, u5} D _inst_2) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Functor.category.{u3, max u2 u3, u5, max (succ u2) (succ u3)} (Opposite.{succ u5} D) (CategoryTheory.Category.opposite.{u3, u5} D _inst_2) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}))) (CategoryTheory.Functor.toPrefunctor.{max u2 u3, max (max u2 u5) u3, max (max (max u2 u5) u1) u3, max (max (succ u2) u5) (succ u3)} (CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u5} J _inst_3 D _inst_2) (CategoryTheory.Functor.{u3, max u2 u3, u5, max (succ u2) (succ u3)} (Opposite.{succ u5} D) (CategoryTheory.Category.opposite.{u3, u5} D _inst_2) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Functor.category.{u3, max u2 u3, u5, max (succ u2) (succ u3)} (Opposite.{succ u5} D) (CategoryTheory.Category.opposite.{u3, u5} D _inst_2) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.cones.{u1, u3, u2, u5} J _inst_3 D _inst_2)) K)) (Prefunctor.obj.{max (succ u2) (succ u3), max (max (succ u2) (succ u4)) (succ u3), max (max (max u2 u4) u1) u3, max (max (succ u2) u4) (succ u3)} (CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_3 C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u3, max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_3 C _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u2 u3, max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_3 C _inst_1) (CategoryTheory.Functor.category.{u1, u3, u2, u4} J _inst_3 C _inst_1))) (CategoryTheory.Functor.{u3, max u2 u3, u4, max (succ u2) (succ u3)} (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u3, u4} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.CategoryStruct.toQuiver.{max (max u2 u4) u3, max (max (succ u2) u4) (succ u3)} (CategoryTheory.Functor.{u3, max u2 u3, u4, max (succ u2) (succ u3)} (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u3, u4} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Category.toCategoryStruct.{max (max u2 u4) u3, max (max (succ u2) u4) (succ u3)} (CategoryTheory.Functor.{u3, max u2 u3, u4, max (succ u2) (succ u3)} (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u3, u4} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Functor.category.{u3, max u2 u3, u4, max (succ u2) (succ u3)} (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u3, u4} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}))) (CategoryTheory.Functor.toPrefunctor.{max u2 u3, max (max u2 u4) u3, max (max (max u2 u4) u1) u3, max (max (succ u2) u4) (succ u3)} (CategoryTheory.Functor.{u1, u3, u2, u4} J _inst_3 C _inst_1) (CategoryTheory.Functor.category.{u1, u3, u2, u4} J _inst_3 C _inst_1) (CategoryTheory.Functor.{u3, max u2 u3, u4, max (succ u2) (succ u3)} (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u3, u4} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.Functor.category.{u3, max u2 u3, u4, max (succ u2) (succ u3)} (Opposite.{succ u4} C) (CategoryTheory.Category.opposite.{u3, u4} C _inst_1) Type.{max u2 u3} CategoryTheory.types.{max u2 u3}) (CategoryTheory.cones.{u1, u3, u2, u4} J _inst_3 C _inst_1)) (CategoryTheory.Functor.comp.{u1, u3, u3, u2, u5, u4} J _inst_3 D _inst_2 C _inst_1 K G)))
Case conversion may be inaccurate. Consider using '#align category_theory.adjunction.cones_iso CategoryTheory.Adjunction.conesIsoₓ'. -/
-- Note: this is natural in K, but we do not yet have the tools to formulate that.
/-- When `F ⊣ G`,
the functor associating to each `X` the cones over `K` with cone point `F.op.obj X`
is naturally isomorphic to
the functor associating to each `X` the cones over `K ⋙ G` with cone point `X`.
-/
def conesIso {J : Type u} [Category.{v} J] {K : J ⥤ D} :
    F.op ⋙ (cones J D).obj K ≅ (cones J C).obj (K ⋙ G) :=
  NatIso.ofComponents
    (fun X =>
      { Hom := conesIsoComponentHom adj X
        inv := conesIsoComponentInv adj X })
    (by tidy)
#align category_theory.adjunction.cones_iso CategoryTheory.Adjunction.conesIso

end CategoryTheory.Adjunction

