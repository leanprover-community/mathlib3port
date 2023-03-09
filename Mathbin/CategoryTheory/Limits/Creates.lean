/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.limits.creates
! leanprover-community/mathlib commit f47581155c818e6361af4e4fda60d27d020c226b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Preserves.Basic

/-!
# Creating (co)limits

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We say that `F` creates limits of `K` if, given any limit cone `c` for `K ⋙ F`
(i.e. below) we can lift it to a cone "above", and further that `F` reflects
limits for `K`.
-/


open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace CategoryTheory

universe w' w v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]

section Creates

variable {D : Type u₂} [Category.{v₂} D]

variable {J : Type w} [Category.{w'} J] {K : J ⥤ C}

#print CategoryTheory.LiftableCone /-
/-- Define the lift of a cone: For a cone `c` for `K ⋙ F`, give a cone for `K`
which is a lift of `c`, i.e. the image of it under `F` is (iso) to `c`.

We will then use this as part of the definition of creation of limits:
every limit cone has a lift.

Note this definition is really only useful when `c` is a limit already.
-/
structure LiftableCone (K : J ⥤ C) (F : C ⥤ D) (c : Cone (K ⋙ F)) where
  liftedCone : Cone K
  validLift : F.mapCone lifted_cone ≅ c
#align category_theory.liftable_cone CategoryTheory.LiftableCone
-/

#print CategoryTheory.LiftableCocone /-
/-- Define the lift of a cocone: For a cocone `c` for `K ⋙ F`, give a cocone for
`K` which is a lift of `c`, i.e. the image of it under `F` is (iso) to `c`.

We will then use this as part of the definition of creation of colimits:
every limit cocone has a lift.

Note this definition is really only useful when `c` is a colimit already.
-/
structure LiftableCocone (K : J ⥤ C) (F : C ⥤ D) (c : Cocone (K ⋙ F)) where
  liftedCocone : Cocone K
  validLift : F.mapCocone lifted_cocone ≅ c
#align category_theory.liftable_cocone CategoryTheory.LiftableCocone
-/

#print CategoryTheory.CreatesLimit /-
/-- Definition 3.3.1 of [Riehl].
We say that `F` creates limits of `K` if, given any limit cone `c` for `K ⋙ F`
(i.e. below) we can lift it to a cone "above", and further that `F` reflects
limits for `K`.

If `F` reflects isomorphisms, it suffices to show only that the lifted cone is
a limit - see `creates_limit_of_reflects_iso`.
-/
class CreatesLimit (K : J ⥤ C) (F : C ⥤ D) extends ReflectsLimit K F where
  lifts : ∀ c, IsLimit c → LiftableCone K F c
#align category_theory.creates_limit CategoryTheory.CreatesLimit
-/

#print CategoryTheory.CreatesLimitsOfShape /-
/-- `F` creates limits of shape `J` if `F` creates the limit of any diagram
`K : J ⥤ C`.
-/
class CreatesLimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) where
  CreatesLimit : ∀ {K : J ⥤ C}, CreatesLimit K F := by infer_instance
#align category_theory.creates_limits_of_shape CategoryTheory.CreatesLimitsOfShape
-/

#print CategoryTheory.CreatesLimitsOfSize /-
-- This should be used with explicit universe variables.
/-- `F` creates limits if it creates limits of shape `J` for any `J`. -/
@[nolint check_univs]
class CreatesLimitsOfSize (F : C ⥤ D) where
  CreatesLimitsOfShape : ∀ {J : Type w} [Category.{w'} J], CreatesLimitsOfShape J F := by
    infer_instance
#align category_theory.creates_limits_of_size CategoryTheory.CreatesLimitsOfSize
-/

#print CategoryTheory.CreatesLimits /-
/-- `F` creates small limits if it creates limits of shape `J` for any small `J`. -/
abbrev CreatesLimits (F : C ⥤ D) :=
  CreatesLimitsOfSize.{v₂, v₂} F
#align category_theory.creates_limits CategoryTheory.CreatesLimits
-/

#print CategoryTheory.CreatesColimit /-
/-- Dual of definition 3.3.1 of [Riehl].
We say that `F` creates colimits of `K` if, given any limit cocone `c` for
`K ⋙ F` (i.e. below) we can lift it to a cocone "above", and further that `F`
reflects limits for `K`.

If `F` reflects isomorphisms, it suffices to show only that the lifted cocone is
a limit - see `creates_limit_of_reflects_iso`.
-/
class CreatesColimit (K : J ⥤ C) (F : C ⥤ D) extends ReflectsColimit K F where
  lifts : ∀ c, IsColimit c → LiftableCocone K F c
#align category_theory.creates_colimit CategoryTheory.CreatesColimit
-/

#print CategoryTheory.CreatesColimitsOfShape /-
/-- `F` creates colimits of shape `J` if `F` creates the colimit of any diagram
`K : J ⥤ C`.
-/
class CreatesColimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) where
  CreatesColimit : ∀ {K : J ⥤ C}, CreatesColimit K F := by infer_instance
#align category_theory.creates_colimits_of_shape CategoryTheory.CreatesColimitsOfShape
-/

#print CategoryTheory.CreatesColimitsOfSize /-
-- This should be used with explicit universe variables.
/-- `F` creates colimits if it creates colimits of shape `J` for any small `J`. -/
@[nolint check_univs]
class CreatesColimitsOfSize (F : C ⥤ D) where
  CreatesColimitsOfShape : ∀ {J : Type w} [Category.{w'} J], CreatesColimitsOfShape J F := by
    infer_instance
#align category_theory.creates_colimits_of_size CategoryTheory.CreatesColimitsOfSize
-/

#print CategoryTheory.CreatesColimits /-
/-- `F` creates small colimits if it creates colimits of shape `J` for any small `J`. -/
abbrev CreatesColimits (F : C ⥤ D) :=
  CreatesColimitsOfSize.{v₂, v₂} F
#align category_theory.creates_colimits CategoryTheory.CreatesColimits
-/

attribute [instance]
  creates_limits_of_shape.creates_limit creates_limits_of_size.creates_limits_of_shape creates_colimits_of_shape.creates_colimit creates_colimits_of_size.creates_colimits_of_shape

#print CategoryTheory.liftLimit /-
-- see Note [lower instance priority]
-- Interface to the `creates_limit` class.
/-- `lift_limit t` is the cone for `K` given by lifting the limit `t` for `K ⋙ F`. -/
def liftLimit {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)} (t : IsLimit c) :
    Cone K :=
  (CreatesLimit.lifts c t).liftedCone
#align category_theory.lift_limit CategoryTheory.liftLimit
-/

/- warning: category_theory.lifted_limit_maps_to_original -> CategoryTheory.liftedLimitMapsToOriginal is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u3, u5} C] {D : Type.{u6}} [_inst_2 : CategoryTheory.Category.{u4, u6} D] {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1} {F : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} [_inst_4 : CategoryTheory.CreatesLimit.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 J _inst_3 K F] {c : CategoryTheory.Limits.Cone.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)} (t : CategoryTheory.Limits.IsLimit.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F) c), CategoryTheory.Iso.{u4, max u2 u6 u4} (CategoryTheory.Limits.Cone.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.Limits.Cone.category.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.Functor.mapCone.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F (CategoryTheory.liftLimit.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 J _inst_3 K F _inst_4 c t)) c
but is expected to have type
  forall {C : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u3, u5} C] {D : Type.{u6}} [_inst_2 : CategoryTheory.Category.{u4, u6} D] {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1} {F : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} [_inst_4 : CategoryTheory.CreatesLimit.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 J _inst_3 K F] {c : CategoryTheory.Limits.Cone.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)} (t : CategoryTheory.Limits.IsLimit.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F) c), CategoryTheory.Iso.{u4, max (max u6 u4) u2} (CategoryTheory.Limits.Cone.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.Limits.Cone.category.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.Functor.mapCone.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 F K (CategoryTheory.liftLimit.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 J _inst_3 K F _inst_4 c t)) c
Case conversion may be inaccurate. Consider using '#align category_theory.lifted_limit_maps_to_original CategoryTheory.liftedLimitMapsToOriginalₓ'. -/
/-- The lifted cone has an image isomorphic to the original cone. -/
def liftedLimitMapsToOriginal {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)}
    (t : IsLimit c) : F.mapCone (liftLimit t) ≅ c :=
  (CreatesLimit.lifts c t).validLift
#align category_theory.lifted_limit_maps_to_original CategoryTheory.liftedLimitMapsToOriginal

#print CategoryTheory.liftedLimitIsLimit /-
/-- The lifted cone is a limit. -/
def liftedLimitIsLimit {K : J ⥤ C} {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)}
    (t : IsLimit c) : IsLimit (liftLimit t) :=
  ReflectsLimit.reflects (IsLimit.ofIsoLimit t (liftedLimitMapsToOriginal t).symm)
#align category_theory.lifted_limit_is_limit CategoryTheory.liftedLimitIsLimit
-/

#print CategoryTheory.hasLimit_of_created /-
/-- If `F` creates the limit of `K` and `K ⋙ F` has a limit, then `K` has a limit. -/
theorem hasLimit_of_created (K : J ⥤ C) (F : C ⥤ D) [HasLimit (K ⋙ F)] [CreatesLimit K F] :
    HasLimit K :=
  HasLimit.mk
    { Cone := liftLimit (limit.isLimit (K ⋙ F))
      IsLimit := liftedLimitIsLimit _ }
#align category_theory.has_limit_of_created CategoryTheory.hasLimit_of_created
-/

#print CategoryTheory.hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape /-
/-- If `F` creates limits of shape `J`, and `D` has limits of shape `J`, then
`C` has limits of shape `J`.
-/
theorem hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (F : C ⥤ D) [HasLimitsOfShape J D]
    [CreatesLimitsOfShape J F] : HasLimitsOfShape J C :=
  ⟨fun G => hasLimit_of_created G F⟩
#align category_theory.has_limits_of_shape_of_has_limits_of_shape_creates_limits_of_shape CategoryTheory.hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
-/

#print CategoryTheory.has_limits_of_has_limits_creates_limits /-
/-- If `F` creates limits, and `D` has all limits, then `C` has all limits. -/
theorem has_limits_of_has_limits_creates_limits (F : C ⥤ D) [HasLimitsOfSize.{w, w'} D]
    [CreatesLimitsOfSize.{w, w'} F] : HasLimitsOfSize.{w, w'} C :=
  ⟨fun J I => has_limits_of_shape_of_has_limits_of_shape_creates_limits_of_shape F⟩
#align category_theory.has_limits_of_has_limits_creates_limits CategoryTheory.has_limits_of_has_limits_creates_limits
-/

#print CategoryTheory.liftColimit /-
-- Interface to the `creates_colimit` class.
/-- `lift_colimit t` is the cocone for `K` given by lifting the colimit `t` for `K ⋙ F`. -/
def liftColimit {K : J ⥤ C} {F : C ⥤ D} [CreatesColimit K F] {c : Cocone (K ⋙ F)}
    (t : IsColimit c) : Cocone K :=
  (CreatesColimit.lifts c t).liftedCocone
#align category_theory.lift_colimit CategoryTheory.liftColimit
-/

/- warning: category_theory.lifted_colimit_maps_to_original -> CategoryTheory.liftedColimitMapsToOriginal is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u3, u5} C] {D : Type.{u6}} [_inst_2 : CategoryTheory.Category.{u4, u6} D] {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1} {F : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} [_inst_4 : CategoryTheory.CreatesColimit.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 J _inst_3 K F] {c : CategoryTheory.Limits.Cocone.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)} (t : CategoryTheory.Limits.IsColimit.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F) c), CategoryTheory.Iso.{u4, max u2 u6 u4} (CategoryTheory.Limits.Cocone.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.Limits.Cocone.category.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.Functor.mapCocone.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F (CategoryTheory.liftColimit.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 J _inst_3 K F _inst_4 c t)) c
but is expected to have type
  forall {C : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u3, u5} C] {D : Type.{u6}} [_inst_2 : CategoryTheory.Category.{u4, u6} D] {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1} {F : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} [_inst_4 : CategoryTheory.CreatesColimit.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 J _inst_3 K F] {c : CategoryTheory.Limits.Cocone.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)} (t : CategoryTheory.Limits.IsColimit.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F) c), CategoryTheory.Iso.{u4, max (max u6 u4) u2} (CategoryTheory.Limits.Cocone.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.Limits.Cocone.category.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.Functor.mapCocone.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 F K (CategoryTheory.liftColimit.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 J _inst_3 K F _inst_4 c t)) c
Case conversion may be inaccurate. Consider using '#align category_theory.lifted_colimit_maps_to_original CategoryTheory.liftedColimitMapsToOriginalₓ'. -/
/-- The lifted cocone has an image isomorphic to the original cocone. -/
def liftedColimitMapsToOriginal {K : J ⥤ C} {F : C ⥤ D} [CreatesColimit K F] {c : Cocone (K ⋙ F)}
    (t : IsColimit c) : F.mapCocone (liftColimit t) ≅ c :=
  (CreatesColimit.lifts c t).validLift
#align category_theory.lifted_colimit_maps_to_original CategoryTheory.liftedColimitMapsToOriginal

#print CategoryTheory.liftedColimitIsColimit /-
/-- The lifted cocone is a colimit. -/
def liftedColimitIsColimit {K : J ⥤ C} {F : C ⥤ D} [CreatesColimit K F] {c : Cocone (K ⋙ F)}
    (t : IsColimit c) : IsColimit (liftColimit t) :=
  ReflectsColimit.reflects (IsColimit.ofIsoColimit t (liftedColimitMapsToOriginal t).symm)
#align category_theory.lifted_colimit_is_colimit CategoryTheory.liftedColimitIsColimit
-/

#print CategoryTheory.hasColimit_of_created /-
/-- If `F` creates the limit of `K` and `K ⋙ F` has a limit, then `K` has a limit. -/
theorem hasColimit_of_created (K : J ⥤ C) (F : C ⥤ D) [HasColimit (K ⋙ F)] [CreatesColimit K F] :
    HasColimit K :=
  HasColimit.mk
    { Cocone := liftColimit (colimit.isColimit (K ⋙ F))
      IsColimit := liftedColimitIsColimit _ }
#align category_theory.has_colimit_of_created CategoryTheory.hasColimit_of_created
-/

#print CategoryTheory.hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape /-
/-- If `F` creates colimits of shape `J`, and `D` has colimits of shape `J`, then
`C` has colimits of shape `J`.
-/
theorem hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (F : C ⥤ D)
    [HasColimitsOfShape J D] [CreatesColimitsOfShape J F] : HasColimitsOfShape J C :=
  ⟨fun G => hasColimit_of_created G F⟩
#align category_theory.has_colimits_of_shape_of_has_colimits_of_shape_creates_colimits_of_shape CategoryTheory.hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape
-/

#print CategoryTheory.has_colimits_of_has_colimits_creates_colimits /-
/-- If `F` creates colimits, and `D` has all colimits, then `C` has all colimits. -/
theorem has_colimits_of_has_colimits_creates_colimits (F : C ⥤ D) [HasColimitsOfSize.{w, w'} D]
    [CreatesColimitsOfSize.{w, w'} F] : HasColimitsOfSize.{w, w'} C :=
  ⟨fun J I => has_colimits_of_shape_of_has_colimits_of_shape_creates_colimits_of_shape F⟩
#align category_theory.has_colimits_of_has_colimits_creates_colimits CategoryTheory.has_colimits_of_has_colimits_creates_colimits
-/

#print CategoryTheory.reflectsLimitsOfShapeOfCreatesLimitsOfShape /-
instance (priority := 10) reflectsLimitsOfShapeOfCreatesLimitsOfShape (F : C ⥤ D)
    [CreatesLimitsOfShape J F] : ReflectsLimitsOfShape J F where
#align category_theory.reflects_limits_of_shape_of_creates_limits_of_shape CategoryTheory.reflectsLimitsOfShapeOfCreatesLimitsOfShape
-/

#print CategoryTheory.reflectsLimitsOfCreatesLimits /-
instance (priority := 10) reflectsLimitsOfCreatesLimits (F : C ⥤ D)
    [CreatesLimitsOfSize.{w, w'} F] : ReflectsLimitsOfSize.{w, w'} F where
#align category_theory.reflects_limits_of_creates_limits CategoryTheory.reflectsLimitsOfCreatesLimits
-/

#print CategoryTheory.reflectsColimitsOfShapeOfCreatesColimitsOfShape /-
instance (priority := 10) reflectsColimitsOfShapeOfCreatesColimitsOfShape (F : C ⥤ D)
    [CreatesColimitsOfShape J F] : ReflectsColimitsOfShape J F where
#align category_theory.reflects_colimits_of_shape_of_creates_colimits_of_shape CategoryTheory.reflectsColimitsOfShapeOfCreatesColimitsOfShape
-/

#print CategoryTheory.reflectsColimitsOfCreatesColimits /-
instance (priority := 10) reflectsColimitsOfCreatesColimits (F : C ⥤ D)
    [CreatesColimitsOfSize.{w, w'} F] : ReflectsColimitsOfSize.{w, w'} F where
#align category_theory.reflects_colimits_of_creates_colimits CategoryTheory.reflectsColimitsOfCreatesColimits
-/

#print CategoryTheory.LiftsToLimit /-
/-- A helper to show a functor creates limits. In particular, if we can show
that for any limit cone `c` for `K ⋙ F`, there is a lift of it which is
a limit and `F` reflects isomorphisms, then `F` creates limits.
Usually, `F` creating limits says that _any_ lift of `c` is a limit, but
here we only need to show that our particular lift of `c` is a limit.
-/
structure LiftsToLimit (K : J ⥤ C) (F : C ⥤ D) (c : Cone (K ⋙ F)) (t : IsLimit c) extends
  LiftableCone K F c where
  makesLimit : IsLimit lifted_cone
#align category_theory.lifts_to_limit CategoryTheory.LiftsToLimit
-/

#print CategoryTheory.LiftsToColimit /-
/-- A helper to show a functor creates colimits. In particular, if we can show
that for any limit cocone `c` for `K ⋙ F`, there is a lift of it which is
a limit and `F` reflects isomorphisms, then `F` creates colimits.
Usually, `F` creating colimits says that _any_ lift of `c` is a colimit, but
here we only need to show that our particular lift of `c` is a colimit.
-/
structure LiftsToColimit (K : J ⥤ C) (F : C ⥤ D) (c : Cocone (K ⋙ F)) (t : IsColimit c) extends
  LiftableCocone K F c where
  makesColimit : IsColimit lifted_cocone
#align category_theory.lifts_to_colimit CategoryTheory.LiftsToColimit
-/

#print CategoryTheory.createsLimitOfReflectsIso /-
/-- If `F` reflects isomorphisms and we can lift any limit cone to a limit cone,
then `F` creates limits.
In particular here we don't need to assume that F reflects limits.
-/
def createsLimitOfReflectsIso {K : J ⥤ C} {F : C ⥤ D} [ReflectsIsomorphisms F]
    (h : ∀ c t, LiftsToLimit K F c t) : CreatesLimit K F
    where
  lifts c t := (h c t).toLiftableCone
  toReflectsLimit :=
    {
      reflects := fun (d : Cone K) (hd : IsLimit (F.mapCone d)) =>
        by
        let d' : cone K := (h (F.map_cone d) hd).toLiftableCone.liftedCone
        let i : F.map_cone d' ≅ F.map_cone d := (h (F.map_cone d) hd).toLiftableCone.validLift
        let hd' : is_limit d' := (h (F.map_cone d) hd).makesLimit
        let f : d ⟶ d' := hd'.lift_cone_morphism d
        have : (cones.functoriality K F).map f = i.inv :=
          (hd.of_iso_limit i.symm).uniq_cone_morphism
        haveI : is_iso ((cones.functoriality K F).map f) :=
          by
          rw [this]
          infer_instance
        haveI : is_iso f := is_iso_of_reflects_iso f (cones.functoriality K F)
        exact is_limit.of_iso_limit hd' (as_iso f).symm }
#align category_theory.creates_limit_of_reflects_iso CategoryTheory.createsLimitOfReflectsIso
-/

/- warning: category_theory.creates_limit_of_fully_faithful_of_lift' -> CategoryTheory.createsLimitOfFullyFaithfulOfLift' is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u3, u5} C] {D : Type.{u6}} [_inst_2 : CategoryTheory.Category.{u4, u6} D] {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1} {F : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} [_inst_4 : CategoryTheory.Full.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] [_inst_5 : CategoryTheory.Faithful.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] {l : CategoryTheory.Limits.Cone.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)}, (CategoryTheory.Limits.IsLimit.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F) l) -> (forall (c : CategoryTheory.Limits.Cone.{u1, u3, u2, u5} J _inst_3 C _inst_1 K), (CategoryTheory.Iso.{u4, max u2 u6 u4} (CategoryTheory.Limits.Cone.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.Limits.Cone.category.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.Functor.mapCone.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F c) l) -> (CategoryTheory.CreatesLimit.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 J _inst_3 K F))
but is expected to have type
  forall {C : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u3, u5} C] {D : Type.{u6}} [_inst_2 : CategoryTheory.Category.{u4, u6} D] {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1} {F : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} [_inst_4 : CategoryTheory.Full.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] [_inst_5 : CategoryTheory.Faithful.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] {l : CategoryTheory.Limits.Cone.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)}, (CategoryTheory.Limits.IsLimit.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F) l) -> (forall (c : CategoryTheory.Limits.Cone.{u1, u3, u2, u5} J _inst_3 C _inst_1 K), (CategoryTheory.Iso.{u4, max (max u6 u4) u2} (CategoryTheory.Limits.Cone.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.Limits.Cone.category.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.Functor.mapCone.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 F K c) l) -> (CategoryTheory.CreatesLimit.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 J _inst_3 K F))
Case conversion may be inaccurate. Consider using '#align category_theory.creates_limit_of_fully_faithful_of_lift' CategoryTheory.createsLimitOfFullyFaithfulOfLift'ₓ'. -/
-- Notice however that even if the isomorphism is `iso.refl _`,
-- this construction will insert additional identity morphisms in the cone maps,
-- so the constructed limits may not be ideal, definitionally.
/--
When `F` is fully faithful, to show that `F` creates the limit for `K` it suffices to exhibit a lift
of a limit cone for `K ⋙ F`.
-/
def createsLimitOfFullyFaithfulOfLift' {K : J ⥤ C} {F : C ⥤ D} [Full F] [Faithful F]
    {l : Cone (K ⋙ F)} (hl : IsLimit l) (c : Cone K) (i : F.mapCone c ≅ l) : CreatesLimit K F :=
  createsLimitOfReflectsIso fun c' t =>
    { liftedCone := c
      validLift := i ≪≫ IsLimit.uniqueUpToIso hl t
      makesLimit :=
        IsLimit.ofFaithful F (IsLimit.ofIsoLimit hl i.symm) _ fun s => F.image_preimage _ }
#align category_theory.creates_limit_of_fully_faithful_of_lift' CategoryTheory.createsLimitOfFullyFaithfulOfLift'

/- warning: category_theory.creates_limit_of_fully_faithful_of_lift -> CategoryTheory.createsLimitOfFullyFaithfulOfLift is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u3, u5} C] {D : Type.{u6}} [_inst_2 : CategoryTheory.Category.{u4, u6} D] {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1} {F : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} [_inst_4 : CategoryTheory.Full.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] [_inst_5 : CategoryTheory.Faithful.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] [_inst_6 : CategoryTheory.Limits.HasLimit.{u1, u2, u4, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)] (c : CategoryTheory.Limits.Cone.{u1, u3, u2, u5} J _inst_3 C _inst_1 K), (CategoryTheory.Iso.{u4, max u2 u6 u4} (CategoryTheory.Limits.Cone.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.Limits.Cone.category.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.Functor.mapCone.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F c) (CategoryTheory.Limits.limit.cone.{u1, u2, u4, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F) _inst_6)) -> (CategoryTheory.CreatesLimit.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 J _inst_3 K F)
but is expected to have type
  forall {C : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u3, u5} C] {D : Type.{u6}} [_inst_2 : CategoryTheory.Category.{u4, u6} D] {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1} {F : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} [_inst_4 : CategoryTheory.Full.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] [_inst_5 : CategoryTheory.Faithful.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] [_inst_6 : CategoryTheory.Limits.HasLimit.{u1, u2, u4, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)] (c : CategoryTheory.Limits.Cone.{u1, u3, u2, u5} J _inst_3 C _inst_1 K), (CategoryTheory.Iso.{u4, max (max u6 u4) u2} (CategoryTheory.Limits.Cone.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.Limits.Cone.category.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.Functor.mapCone.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 F K c) (CategoryTheory.Limits.limit.cone.{u1, u2, u4, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F) _inst_6)) -> (CategoryTheory.CreatesLimit.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 J _inst_3 K F)
Case conversion may be inaccurate. Consider using '#align category_theory.creates_limit_of_fully_faithful_of_lift CategoryTheory.createsLimitOfFullyFaithfulOfLiftₓ'. -/
-- Notice however that even if the isomorphism is `iso.refl _`,
-- this construction will insert additional identity morphisms in the cone maps,
-- so the constructed limits may not be ideal, definitionally.
/-- When `F` is fully faithful, and `has_limit (K ⋙ F)`, to show that `F` creates the limit for `K`
it suffices to exhibit a lift of the chosen limit cone for `K ⋙ F`.
-/
def createsLimitOfFullyFaithfulOfLift {K : J ⥤ C} {F : C ⥤ D} [Full F] [Faithful F]
    [HasLimit (K ⋙ F)] (c : Cone K) (i : F.mapCone c ≅ limit.cone (K ⋙ F)) : CreatesLimit K F :=
  createsLimitOfFullyFaithfulOfLift' (limit.isLimit _) c i
#align category_theory.creates_limit_of_fully_faithful_of_lift CategoryTheory.createsLimitOfFullyFaithfulOfLift

/- warning: category_theory.creates_limit_of_fully_faithful_of_iso' -> CategoryTheory.createsLimitOfFullyFaithfulOfIso' is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u3, u5} C] {D : Type.{u6}} [_inst_2 : CategoryTheory.Category.{u4, u6} D] {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1} {F : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} [_inst_4 : CategoryTheory.Full.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] [_inst_5 : CategoryTheory.Faithful.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] {l : CategoryTheory.Limits.Cone.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)}, (CategoryTheory.Limits.IsLimit.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F) l) -> (forall (X : C), (CategoryTheory.Iso.{u4, u6} D _inst_2 (CategoryTheory.Functor.obj.{u3, u4, u5, u6} C _inst_1 D _inst_2 F X) (CategoryTheory.Limits.Cone.pt.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F) l)) -> (CategoryTheory.CreatesLimit.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 J _inst_3 K F))
but is expected to have type
  forall {C : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u3, u5} C] {D : Type.{u6}} [_inst_2 : CategoryTheory.Category.{u4, u6} D] {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1} {F : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} [_inst_4 : CategoryTheory.Full.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] [_inst_5 : CategoryTheory.Faithful.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] {l : CategoryTheory.Limits.Cone.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)}, (CategoryTheory.Limits.IsLimit.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F) l) -> (forall (X : C), (CategoryTheory.Iso.{u4, u6} D _inst_2 (Prefunctor.obj.{succ u3, succ u4, u5, u6} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u5} C (CategoryTheory.Category.toCategoryStruct.{u3, u5} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u6} D (CategoryTheory.Category.toCategoryStruct.{u4, u6} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u3, u4, u5, u6} C _inst_1 D _inst_2 F) X) (CategoryTheory.Limits.Cone.pt.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F) l)) -> (CategoryTheory.CreatesLimit.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 J _inst_3 K F))
Case conversion may be inaccurate. Consider using '#align category_theory.creates_limit_of_fully_faithful_of_iso' CategoryTheory.createsLimitOfFullyFaithfulOfIso'ₓ'. -/
-- Notice however that even if the isomorphism is `iso.refl _`,
-- this construction will insert additional identity morphisms in the cone maps,
-- so the constructed limits may not be ideal, definitionally.
/--
When `F` is fully faithful, to show that `F` creates the limit for `K` it suffices to show that a
limit point is in the essential image of `F`.
-/
def createsLimitOfFullyFaithfulOfIso' {K : J ⥤ C} {F : C ⥤ D} [Full F] [Faithful F]
    {l : Cone (K ⋙ F)} (hl : IsLimit l) (X : C) (i : F.obj X ≅ l.pt) : CreatesLimit K F :=
  createsLimitOfFullyFaithfulOfLift' hl
    { pt
      π :=
        { app := fun j => F.preimage (i.Hom ≫ l.π.app j)
          naturality' := fun Y Z f =>
            F.map_injective <| by
              dsimp
              simpa using (l.w f).symm } }
    (Cones.ext i fun j => by simp only [functor.image_preimage, functor.map_cone_π_app])
#align category_theory.creates_limit_of_fully_faithful_of_iso' CategoryTheory.createsLimitOfFullyFaithfulOfIso'

/- warning: category_theory.creates_limit_of_fully_faithful_of_iso -> CategoryTheory.createsLimitOfFullyFaithfulOfIso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u3, u5} C] {D : Type.{u6}} [_inst_2 : CategoryTheory.Category.{u4, u6} D] {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1} {F : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} [_inst_4 : CategoryTheory.Full.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] [_inst_5 : CategoryTheory.Faithful.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] [_inst_6 : CategoryTheory.Limits.HasLimit.{u1, u2, u4, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)] (X : C), (CategoryTheory.Iso.{u4, u6} D _inst_2 (CategoryTheory.Functor.obj.{u3, u4, u5, u6} C _inst_1 D _inst_2 F X) (CategoryTheory.Limits.limit.{u1, u2, u4, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F) _inst_6)) -> (CategoryTheory.CreatesLimit.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 J _inst_3 K F)
but is expected to have type
  forall {C : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u3, u5} C] {D : Type.{u6}} [_inst_2 : CategoryTheory.Category.{u4, u6} D] {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1} {F : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} [_inst_4 : CategoryTheory.Full.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] [_inst_5 : CategoryTheory.Faithful.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] [_inst_6 : CategoryTheory.Limits.HasLimit.{u1, u2, u4, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)] (X : C), (CategoryTheory.Iso.{u4, u6} D _inst_2 (Prefunctor.obj.{succ u3, succ u4, u5, u6} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u5} C (CategoryTheory.Category.toCategoryStruct.{u3, u5} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u6} D (CategoryTheory.Category.toCategoryStruct.{u4, u6} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u3, u4, u5, u6} C _inst_1 D _inst_2 F) X) (CategoryTheory.Limits.limit.{u1, u2, u4, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F) _inst_6)) -> (CategoryTheory.CreatesLimit.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 J _inst_3 K F)
Case conversion may be inaccurate. Consider using '#align category_theory.creates_limit_of_fully_faithful_of_iso CategoryTheory.createsLimitOfFullyFaithfulOfIsoₓ'. -/
-- Notice however that even if the isomorphism is `iso.refl _`,
-- this construction will insert additional identity morphisms in the cone maps,
-- so the constructed limits may not be ideal, definitionally.
/-- When `F` is fully faithful, and `has_limit (K ⋙ F)`, to show that `F` creates the limit for `K`
it suffices to show that the chosen limit point is in the essential image of `F`.
-/
def createsLimitOfFullyFaithfulOfIso {K : J ⥤ C} {F : C ⥤ D} [Full F] [Faithful F]
    [HasLimit (K ⋙ F)] (X : C) (i : F.obj X ≅ limit (K ⋙ F)) : CreatesLimit K F :=
  createsLimitOfFullyFaithfulOfIso' (limit.isLimit _) X i
#align category_theory.creates_limit_of_fully_faithful_of_iso CategoryTheory.createsLimitOfFullyFaithfulOfIso

#print CategoryTheory.preservesLimitOfCreatesLimitAndHasLimit /-
-- see Note [lower instance priority]
/-- `F` preserves the limit of `K` if it creates the limit and `K ⋙ F` has the limit. -/
instance (priority := 100) preservesLimitOfCreatesLimitAndHasLimit (K : J ⥤ C) (F : C ⥤ D)
    [CreatesLimit K F] [HasLimit (K ⋙ F)] : PreservesLimit K F
    where preserves c t :=
    IsLimit.ofIsoLimit (limit.isLimit _)
      ((liftedLimitMapsToOriginal (limit.isLimit _)).symm ≪≫
        (Cones.functoriality K F).mapIso ((liftedLimitIsLimit (limit.isLimit _)).uniqueUpToIso t))
#align category_theory.preserves_limit_of_creates_limit_and_has_limit CategoryTheory.preservesLimitOfCreatesLimitAndHasLimit
-/

#print CategoryTheory.preservesLimitOfShapeOfCreatesLimitsOfShapeAndHasLimitsOfShape /-
-- see Note [lower instance priority]
/-- `F` preserves the limit of shape `J` if it creates these limits and `D` has them. -/
instance (priority := 100) preservesLimitOfShapeOfCreatesLimitsOfShapeAndHasLimitsOfShape
    (F : C ⥤ D) [CreatesLimitsOfShape J F] [HasLimitsOfShape J D] : PreservesLimitsOfShape J F where
#align category_theory.preserves_limit_of_shape_of_creates_limits_of_shape_and_has_limits_of_shape CategoryTheory.preservesLimitOfShapeOfCreatesLimitsOfShapeAndHasLimitsOfShape
-/

#print CategoryTheory.preservesLimitsOfCreatesLimitsAndHasLimits /-
-- see Note [lower instance priority]
/-- `F` preserves limits if it creates limits and `D` has limits. -/
instance (priority := 100) preservesLimitsOfCreatesLimitsAndHasLimits (F : C ⥤ D)
    [CreatesLimitsOfSize.{w, w'} F] [HasLimitsOfSize.{w, w'} D] : PreservesLimitsOfSize.{w, w'} F
    where
#align category_theory.preserves_limits_of_creates_limits_and_has_limits CategoryTheory.preservesLimitsOfCreatesLimitsAndHasLimits
-/

#print CategoryTheory.createsColimitOfReflectsIso /-
/-- If `F` reflects isomorphisms and we can lift any colimit cocone to a colimit cocone,
then `F` creates colimits.
In particular here we don't need to assume that F reflects colimits.
-/
def createsColimitOfReflectsIso {K : J ⥤ C} {F : C ⥤ D} [ReflectsIsomorphisms F]
    (h : ∀ c t, LiftsToColimit K F c t) : CreatesColimit K F
    where
  lifts c t := (h c t).toLiftableCocone
  toReflectsColimit :=
    {
      reflects := fun (d : Cocone K) (hd : IsColimit (F.mapCocone d)) =>
        by
        let d' : cocone K := (h (F.map_cocone d) hd).toLiftableCocone.liftedCocone
        let i : F.map_cocone d' ≅ F.map_cocone d :=
          (h (F.map_cocone d) hd).toLiftableCocone.validLift
        let hd' : is_colimit d' := (h (F.map_cocone d) hd).makesColimit
        let f : d' ⟶ d := hd'.desc_cocone_morphism d
        have : (cocones.functoriality K F).map f = i.hom :=
          (hd.of_iso_colimit i.symm).uniq_cocone_morphism
        haveI : is_iso ((cocones.functoriality K F).map f) :=
          by
          rw [this]
          infer_instance
        haveI := is_iso_of_reflects_iso f (cocones.functoriality K F)
        exact is_colimit.of_iso_colimit hd' (as_iso f) }
#align category_theory.creates_colimit_of_reflects_iso CategoryTheory.createsColimitOfReflectsIso
-/

/- warning: category_theory.creates_colimit_of_fully_faithful_of_lift' -> CategoryTheory.createsColimitOfFullyFaithfulOfLift' is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u3, u5} C] {D : Type.{u6}} [_inst_2 : CategoryTheory.Category.{u4, u6} D] {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1} {F : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} [_inst_4 : CategoryTheory.Full.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] [_inst_5 : CategoryTheory.Faithful.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] {l : CategoryTheory.Limits.Cocone.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)}, (CategoryTheory.Limits.IsColimit.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F) l) -> (forall (c : CategoryTheory.Limits.Cocone.{u1, u3, u2, u5} J _inst_3 C _inst_1 K), (CategoryTheory.Iso.{u4, max u2 u6 u4} (CategoryTheory.Limits.Cocone.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.Limits.Cocone.category.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.Functor.mapCocone.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F c) l) -> (CategoryTheory.CreatesColimit.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 J _inst_3 K F))
but is expected to have type
  forall {C : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u3, u5} C] {D : Type.{u6}} [_inst_2 : CategoryTheory.Category.{u4, u6} D] {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1} {F : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} [_inst_4 : CategoryTheory.Full.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] [_inst_5 : CategoryTheory.Faithful.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] {l : CategoryTheory.Limits.Cocone.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)}, (CategoryTheory.Limits.IsColimit.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F) l) -> (forall (c : CategoryTheory.Limits.Cocone.{u1, u3, u2, u5} J _inst_3 C _inst_1 K), (CategoryTheory.Iso.{u4, max (max u6 u4) u2} (CategoryTheory.Limits.Cocone.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.Limits.Cocone.category.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.Functor.mapCocone.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 F K c) l) -> (CategoryTheory.CreatesColimit.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 J _inst_3 K F))
Case conversion may be inaccurate. Consider using '#align category_theory.creates_colimit_of_fully_faithful_of_lift' CategoryTheory.createsColimitOfFullyFaithfulOfLift'ₓ'. -/
-- Notice however that even if the isomorphism is `iso.refl _`,
-- this construction will insert additional identity morphisms in the cocone maps,
-- so the constructed colimits may not be ideal, definitionally.
/--
When `F` is fully faithful, to show that `F` creates the colimit for `K` it suffices to exhibit a
lift of a colimit cocone for `K ⋙ F`.
-/
def createsColimitOfFullyFaithfulOfLift' {K : J ⥤ C} {F : C ⥤ D} [Full F] [Faithful F]
    {l : Cocone (K ⋙ F)} (hl : IsColimit l) (c : Cocone K) (i : F.mapCocone c ≅ l) :
    CreatesColimit K F :=
  createsColimitOfReflectsIso fun c' t =>
    { liftedCocone := c
      validLift := i ≪≫ IsColimit.uniqueUpToIso hl t
      makesColimit :=
        IsColimit.ofFaithful F (IsColimit.ofIsoColimit hl i.symm) _ fun s => F.image_preimage _ }
#align category_theory.creates_colimit_of_fully_faithful_of_lift' CategoryTheory.createsColimitOfFullyFaithfulOfLift'

/- warning: category_theory.creates_colimit_of_fully_faithful_of_lift -> CategoryTheory.createsColimitOfFullyFaithfulOfLift is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u3, u5} C] {D : Type.{u6}} [_inst_2 : CategoryTheory.Category.{u4, u6} D] {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1} {F : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} [_inst_4 : CategoryTheory.Full.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] [_inst_5 : CategoryTheory.Faithful.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] [_inst_6 : CategoryTheory.Limits.HasColimit.{u1, u2, u4, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)] (c : CategoryTheory.Limits.Cocone.{u1, u3, u2, u5} J _inst_3 C _inst_1 K), (CategoryTheory.Iso.{u4, max u2 u6 u4} (CategoryTheory.Limits.Cocone.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.Limits.Cocone.category.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.Functor.mapCocone.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F c) (CategoryTheory.Limits.colimit.cocone.{u1, u2, u4, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F) _inst_6)) -> (CategoryTheory.CreatesColimit.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 J _inst_3 K F)
but is expected to have type
  forall {C : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u3, u5} C] {D : Type.{u6}} [_inst_2 : CategoryTheory.Category.{u4, u6} D] {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1} {F : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} [_inst_4 : CategoryTheory.Full.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] [_inst_5 : CategoryTheory.Faithful.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] [_inst_6 : CategoryTheory.Limits.HasColimit.{u1, u2, u4, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)] (c : CategoryTheory.Limits.Cocone.{u1, u3, u2, u5} J _inst_3 C _inst_1 K), (CategoryTheory.Iso.{u4, max (max u6 u4) u2} (CategoryTheory.Limits.Cocone.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.Limits.Cocone.category.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.Functor.mapCocone.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 F K c) (CategoryTheory.Limits.colimit.cocone.{u1, u2, u4, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F) _inst_6)) -> (CategoryTheory.CreatesColimit.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 J _inst_3 K F)
Case conversion may be inaccurate. Consider using '#align category_theory.creates_colimit_of_fully_faithful_of_lift CategoryTheory.createsColimitOfFullyFaithfulOfLiftₓ'. -/
-- Notice however that even if the isomorphism is `iso.refl _`,
-- this construction will insert additional identity morphisms in the cocone maps,
-- so the constructed colimits may not be ideal, definitionally.
/--
When `F` is fully faithful, and `has_colimit (K ⋙ F)`, to show that `F` creates the colimit for `K`
it suffices to exhibit a lift of the chosen colimit cocone for `K ⋙ F`.
-/
def createsColimitOfFullyFaithfulOfLift {K : J ⥤ C} {F : C ⥤ D} [Full F] [Faithful F]
    [HasColimit (K ⋙ F)] (c : Cocone K) (i : F.mapCocone c ≅ colimit.cocone (K ⋙ F)) :
    CreatesColimit K F :=
  createsColimitOfFullyFaithfulOfLift' (colimit.isColimit _) c i
#align category_theory.creates_colimit_of_fully_faithful_of_lift CategoryTheory.createsColimitOfFullyFaithfulOfLift

/- warning: category_theory.creates_colimit_of_fully_faithful_of_iso' -> CategoryTheory.createsColimitOfFullyFaithfulOfIso' is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u3, u5} C] {D : Type.{u6}} [_inst_2 : CategoryTheory.Category.{u4, u6} D] {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1} {F : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} [_inst_4 : CategoryTheory.Full.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] [_inst_5 : CategoryTheory.Faithful.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] {l : CategoryTheory.Limits.Cocone.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)}, (CategoryTheory.Limits.IsColimit.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F) l) -> (forall (X : C), (CategoryTheory.Iso.{u4, u6} D _inst_2 (CategoryTheory.Functor.obj.{u3, u4, u5, u6} C _inst_1 D _inst_2 F X) (CategoryTheory.Limits.Cocone.pt.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F) l)) -> (CategoryTheory.CreatesColimit.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 J _inst_3 K F))
but is expected to have type
  forall {C : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u3, u5} C] {D : Type.{u6}} [_inst_2 : CategoryTheory.Category.{u4, u6} D] {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1} {F : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} [_inst_4 : CategoryTheory.Full.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] [_inst_5 : CategoryTheory.Faithful.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] {l : CategoryTheory.Limits.Cocone.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)}, (CategoryTheory.Limits.IsColimit.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F) l) -> (forall (X : C), (CategoryTheory.Iso.{u4, u6} D _inst_2 (Prefunctor.obj.{succ u3, succ u4, u5, u6} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u5} C (CategoryTheory.Category.toCategoryStruct.{u3, u5} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u6} D (CategoryTheory.Category.toCategoryStruct.{u4, u6} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u3, u4, u5, u6} C _inst_1 D _inst_2 F) X) (CategoryTheory.Limits.Cocone.pt.{u1, u4, u2, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F) l)) -> (CategoryTheory.CreatesColimit.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 J _inst_3 K F))
Case conversion may be inaccurate. Consider using '#align category_theory.creates_colimit_of_fully_faithful_of_iso' CategoryTheory.createsColimitOfFullyFaithfulOfIso'ₓ'. -/
-- Notice however that even if the isomorphism is `iso.refl _`,
-- this construction will insert additional identity morphisms in the cocone maps,
-- so the constructed colimits may not be ideal, definitionally.
/--
When `F` is fully faithful, to show that `F` creates the colimit for `K` it suffices to show that
a colimit point is in the essential image of `F`.
-/
def createsColimitOfFullyFaithfulOfIso' {K : J ⥤ C} {F : C ⥤ D} [Full F] [Faithful F]
    {l : Cocone (K ⋙ F)} (hl : IsColimit l) (X : C) (i : F.obj X ≅ l.pt) : CreatesColimit K F :=
  createsColimitOfFullyFaithfulOfLift' hl
    { pt
      ι :=
        { app := fun j => F.preimage (l.ι.app j ≫ i.inv)
          naturality' := fun Y Z f =>
            F.map_injective <| by
              dsimp
              simpa [← cancel_mono i.hom] using l.w f } }
    (Cocones.ext i fun j => by simp)
#align category_theory.creates_colimit_of_fully_faithful_of_iso' CategoryTheory.createsColimitOfFullyFaithfulOfIso'

/- warning: category_theory.creates_colimit_of_fully_faithful_of_iso -> CategoryTheory.createsColimitOfFullyFaithfulOfIso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u3, u5} C] {D : Type.{u6}} [_inst_2 : CategoryTheory.Category.{u4, u6} D] {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1} {F : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} [_inst_4 : CategoryTheory.Full.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] [_inst_5 : CategoryTheory.Faithful.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] [_inst_6 : CategoryTheory.Limits.HasColimit.{u1, u2, u4, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)] (X : C), (CategoryTheory.Iso.{u4, u6} D _inst_2 (CategoryTheory.Functor.obj.{u3, u4, u5, u6} C _inst_1 D _inst_2 F X) (CategoryTheory.Limits.colimit.{u1, u2, u4, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F) _inst_6)) -> (CategoryTheory.CreatesColimit.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 J _inst_3 K F)
but is expected to have type
  forall {C : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u3, u5} C] {D : Type.{u6}} [_inst_2 : CategoryTheory.Category.{u4, u6} D] {J : Type.{u2}} [_inst_3 : CategoryTheory.Category.{u1, u2} J] {K : CategoryTheory.Functor.{u1, u3, u2, u5} J _inst_3 C _inst_1} {F : CategoryTheory.Functor.{u3, u4, u5, u6} C _inst_1 D _inst_2} [_inst_4 : CategoryTheory.Full.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] [_inst_5 : CategoryTheory.Faithful.{u3, u4, u5, u6} C _inst_1 D _inst_2 F] [_inst_6 : CategoryTheory.Limits.HasColimit.{u1, u2, u4, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F)] (X : C), (CategoryTheory.Iso.{u4, u6} D _inst_2 (Prefunctor.obj.{succ u3, succ u4, u5, u6} C (CategoryTheory.CategoryStruct.toQuiver.{u3, u5} C (CategoryTheory.Category.toCategoryStruct.{u3, u5} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u4, u6} D (CategoryTheory.Category.toCategoryStruct.{u4, u6} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u3, u4, u5, u6} C _inst_1 D _inst_2 F) X) (CategoryTheory.Limits.colimit.{u1, u2, u4, u6} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u3, u4, u2, u5, u6} J _inst_3 C _inst_1 D _inst_2 K F) _inst_6)) -> (CategoryTheory.CreatesColimit.{u1, u2, u3, u4, u5, u6} C _inst_1 D _inst_2 J _inst_3 K F)
Case conversion may be inaccurate. Consider using '#align category_theory.creates_colimit_of_fully_faithful_of_iso CategoryTheory.createsColimitOfFullyFaithfulOfIsoₓ'. -/
-- Notice however that even if the isomorphism is `iso.refl _`,
-- this construction will insert additional identity morphisms in the cocone maps,
-- so the constructed colimits may not be ideal, definitionally.
/--
When `F` is fully faithful, and `has_colimit (K ⋙ F)`, to show that `F` creates the colimit for `K`
it suffices to show that the chosen colimit point is in the essential image of `F`.
-/
def createsColimitOfFullyFaithfulOfIso {K : J ⥤ C} {F : C ⥤ D} [Full F] [Faithful F]
    [HasColimit (K ⋙ F)] (X : C) (i : F.obj X ≅ colimit (K ⋙ F)) : CreatesColimit K F :=
  createsColimitOfFullyFaithfulOfIso' (colimit.isColimit _) X i
#align category_theory.creates_colimit_of_fully_faithful_of_iso CategoryTheory.createsColimitOfFullyFaithfulOfIso

#print CategoryTheory.preservesColimitOfCreatesColimitAndHasColimit /-
-- see Note [lower instance priority]
/-- `F` preserves the colimit of `K` if it creates the colimit and `K ⋙ F` has the colimit. -/
instance (priority := 100) preservesColimitOfCreatesColimitAndHasColimit (K : J ⥤ C) (F : C ⥤ D)
    [CreatesColimit K F] [HasColimit (K ⋙ F)] : PreservesColimit K F
    where preserves c t :=
    IsColimit.ofIsoColimit (colimit.isColimit _)
      ((liftedColimitMapsToOriginal (colimit.isColimit _)).symm ≪≫
        (Cocones.functoriality K F).mapIso
          ((liftedColimitIsColimit (colimit.isColimit _)).uniqueUpToIso t))
#align category_theory.preserves_colimit_of_creates_colimit_and_has_colimit CategoryTheory.preservesColimitOfCreatesColimitAndHasColimit
-/

#print CategoryTheory.preservesColimitOfShapeOfCreatesColimitsOfShapeAndHasColimitsOfShape /-
-- see Note [lower instance priority]
/-- `F` preserves the colimit of shape `J` if it creates these colimits and `D` has them. -/
instance (priority := 100) preservesColimitOfShapeOfCreatesColimitsOfShapeAndHasColimitsOfShape
    (F : C ⥤ D) [CreatesColimitsOfShape J F] [HasColimitsOfShape J D] : PreservesColimitsOfShape J F
    where
#align category_theory.preserves_colimit_of_shape_of_creates_colimits_of_shape_and_has_colimits_of_shape CategoryTheory.preservesColimitOfShapeOfCreatesColimitsOfShapeAndHasColimitsOfShape
-/

#print CategoryTheory.preservesColimitsOfCreatesColimitsAndHasColimits /-
-- see Note [lower instance priority]
/-- `F` preserves limits if it creates limits and `D` has limits. -/
instance (priority := 100) preservesColimitsOfCreatesColimitsAndHasColimits (F : C ⥤ D)
    [CreatesColimitsOfSize.{w, w'} F] [HasColimitsOfSize.{w, w'} D] :
    PreservesColimitsOfSize.{w, w'} F where
#align category_theory.preserves_colimits_of_creates_colimits_and_has_colimits CategoryTheory.preservesColimitsOfCreatesColimitsAndHasColimits
-/

#print CategoryTheory.createsLimitOfIsoDiagram /-
/-- Transfer creation of limits along a natural isomorphism in the diagram. -/
def createsLimitOfIsoDiagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [CreatesLimit K₁ F] :
    CreatesLimit K₂ F :=
  { reflectsLimitOfIsoDiagram F h with
    lifts := fun c t =>
      let t' := (IsLimit.postcomposeInvEquiv (isoWhiskerRight h F : _) c).symm t
      { liftedCone := (Cones.postcompose h.Hom).obj (liftLimit t')
        validLift :=
          F.mapConePostcompose ≪≫
            (Cones.postcompose (isoWhiskerRight h F).Hom).mapIso (liftedLimitMapsToOriginal t') ≪≫
              Cones.ext (Iso.refl _) fun j => by
                dsimp
                rw [category.assoc, ← F.map_comp]
                simp } }
#align category_theory.creates_limit_of_iso_diagram CategoryTheory.createsLimitOfIsoDiagram
-/

#print CategoryTheory.createsLimitOfNatIso /-
/-- If `F` creates the limit of `K` and `F ≅ G`, then `G` creates the limit of `K`. -/
def createsLimitOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesLimit K F] : CreatesLimit K G
    where
  lifts c t :=
    { liftedCone := liftLimit ((IsLimit.postcomposeInvEquiv (isoWhiskerLeft K h : _) c).symm t)
      validLift := by
        refine' (is_limit.map_cone_equiv h _).uniqueUpToIso t
        apply is_limit.of_iso_limit _ (lifted_limit_maps_to_original _).symm
        apply (is_limit.postcompose_inv_equiv _ _).symm t }
  toReflectsLimit := reflectsLimitOfNatIso _ h
#align category_theory.creates_limit_of_nat_iso CategoryTheory.createsLimitOfNatIso
-/

#print CategoryTheory.createsLimitsOfShapeOfNatIso /-
/-- If `F` creates limits of shape `J` and `F ≅ G`, then `G` creates limits of shape `J`. -/
def createsLimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesLimitsOfShape J F] :
    CreatesLimitsOfShape J G where CreatesLimit K := createsLimitOfNatIso h
#align category_theory.creates_limits_of_shape_of_nat_iso CategoryTheory.createsLimitsOfShapeOfNatIso
-/

#print CategoryTheory.createsLimitsOfNatIso /-
/-- If `F` creates limits and `F ≅ G`, then `G` creates limits. -/
def createsLimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesLimitsOfSize.{w, w'} F] :
    CreatesLimitsOfSize.{w, w'} G
    where CreatesLimitsOfShape J 𝒥₁ := creates_limits_of_shape_of_nat_iso h
#align category_theory.creates_limits_of_nat_iso CategoryTheory.createsLimitsOfNatIso
-/

#print CategoryTheory.createsColimitOfIsoDiagram /-
/-- Transfer creation of colimits along a natural isomorphism in the diagram. -/
def createsColimitOfIsoDiagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [CreatesColimit K₁ F] :
    CreatesColimit K₂ F :=
  { reflectsColimitOfIsoDiagram F h with
    lifts := fun c t =>
      let t' := (IsColimit.precomposeHomEquiv (isoWhiskerRight h F : _) c).symm t
      { liftedCocone := (Cocones.precompose h.inv).obj (liftColimit t')
        validLift :=
          F.mapCoconePrecompose ≪≫
            (Cocones.precompose (isoWhiskerRight h F).inv).mapIso
                (liftedColimitMapsToOriginal t') ≪≫
              Cocones.ext (Iso.refl _) fun j => by
                dsimp
                rw [← F.map_comp_assoc]
                simp } }
#align category_theory.creates_colimit_of_iso_diagram CategoryTheory.createsColimitOfIsoDiagram
-/

#print CategoryTheory.createsColimitOfNatIso /-
/-- If `F` creates the colimit of `K` and `F ≅ G`, then `G` creates the colimit of `K`. -/
def createsColimitOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesColimit K F] : CreatesColimit K G
    where
  lifts c t :=
    { liftedCocone := liftColimit ((IsColimit.precomposeHomEquiv (isoWhiskerLeft K h : _) c).symm t)
      validLift := by
        refine' (is_colimit.map_cocone_equiv h _).uniqueUpToIso t
        apply is_colimit.of_iso_colimit _ (lifted_colimit_maps_to_original _).symm
        apply (is_colimit.precompose_hom_equiv _ _).symm t }
  toReflectsColimit := reflectsColimitOfNatIso _ h
#align category_theory.creates_colimit_of_nat_iso CategoryTheory.createsColimitOfNatIso
-/

#print CategoryTheory.createsColimitsOfShapeOfNatIso /-
/-- If `F` creates colimits of shape `J` and `F ≅ G`, then `G` creates colimits of shape `J`. -/
def createsColimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesColimitsOfShape J F] :
    CreatesColimitsOfShape J G where CreatesColimit K := createsColimitOfNatIso h
#align category_theory.creates_colimits_of_shape_of_nat_iso CategoryTheory.createsColimitsOfShapeOfNatIso
-/

#print CategoryTheory.createsColimitsOfNatIso /-
/-- If `F` creates colimits and `F ≅ G`, then `G` creates colimits. -/
def createsColimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [CreatesColimitsOfSize.{w, w'} F] :
    CreatesColimitsOfSize.{w, w'} G
    where CreatesColimitsOfShape J 𝒥₁ := creates_colimits_of_shape_of_nat_iso h
#align category_theory.creates_colimits_of_nat_iso CategoryTheory.createsColimitsOfNatIso
-/

#print CategoryTheory.liftsToLimitOfCreates /-
-- For the inhabited linter later.
/-- If F creates the limit of K, any cone lifts to a limit. -/
def liftsToLimitOfCreates (K : J ⥤ C) (F : C ⥤ D) [CreatesLimit K F] (c : Cone (K ⋙ F))
    (t : IsLimit c) : LiftsToLimit K F c t
    where
  liftedCone := liftLimit t
  validLift := liftedLimitMapsToOriginal t
  makesLimit := liftedLimitIsLimit t
#align category_theory.lifts_to_limit_of_creates CategoryTheory.liftsToLimitOfCreates
-/

#print CategoryTheory.liftsToColimitOfCreates /-
-- For the inhabited linter later.
/-- If F creates the colimit of K, any cocone lifts to a colimit. -/
def liftsToColimitOfCreates (K : J ⥤ C) (F : C ⥤ D) [CreatesColimit K F] (c : Cocone (K ⋙ F))
    (t : IsColimit c) : LiftsToColimit K F c t
    where
  liftedCocone := liftColimit t
  validLift := liftedColimitMapsToOriginal t
  makesColimit := liftedColimitIsColimit t
#align category_theory.lifts_to_colimit_of_creates CategoryTheory.liftsToColimitOfCreates
-/

#print CategoryTheory.idLiftsCone /-
/-- Any cone lifts through the identity functor. -/
def idLiftsCone (c : Cone (K ⋙ 𝟭 C)) : LiftableCone K (𝟭 C) c
    where
  liftedCone :=
    { pt := c.pt
      π := c.π ≫ K.rightUnitor.Hom }
  validLift := Cones.ext (Iso.refl _) (by tidy)
#align category_theory.id_lifts_cone CategoryTheory.idLiftsCone
-/

#print CategoryTheory.idCreatesLimits /-
/-- The identity functor creates all limits. -/
instance idCreatesLimits : CreatesLimitsOfSize.{w, w'} (𝟭 C)
    where CreatesLimitsOfShape J 𝒥 :=
    { CreatesLimit := fun F => { lifts := fun c t => id_lifts_cone c } }
#align category_theory.id_creates_limits CategoryTheory.idCreatesLimits
-/

#print CategoryTheory.idLiftsCocone /-
/-- Any cocone lifts through the identity functor. -/
def idLiftsCocone (c : Cocone (K ⋙ 𝟭 C)) : LiftableCocone K (𝟭 C) c
    where
  liftedCocone :=
    { pt := c.pt
      ι := K.rightUnitor.inv ≫ c.ι }
  validLift := Cocones.ext (Iso.refl _) (by tidy)
#align category_theory.id_lifts_cocone CategoryTheory.idLiftsCocone
-/

#print CategoryTheory.idCreatesColimits /-
/-- The identity functor creates all colimits. -/
instance idCreatesColimits : CreatesColimitsOfSize.{w, w'} (𝟭 C)
    where CreatesColimitsOfShape J 𝒥 :=
    { CreatesColimit := fun F => { lifts := fun c t => id_lifts_cocone c } }
#align category_theory.id_creates_colimits CategoryTheory.idCreatesColimits
-/

#print CategoryTheory.inhabitedLiftableCone /-
/-- Satisfy the inhabited linter -/
instance inhabitedLiftableCone (c : Cone (K ⋙ 𝟭 C)) : Inhabited (LiftableCone K (𝟭 C) c) :=
  ⟨idLiftsCone c⟩
#align category_theory.inhabited_liftable_cone CategoryTheory.inhabitedLiftableCone
-/

#print CategoryTheory.inhabitedLiftableCocone /-
instance inhabitedLiftableCocone (c : Cocone (K ⋙ 𝟭 C)) : Inhabited (LiftableCocone K (𝟭 C) c) :=
  ⟨idLiftsCocone c⟩
#align category_theory.inhabited_liftable_cocone CategoryTheory.inhabitedLiftableCocone
-/

#print CategoryTheory.inhabitedLiftsToLimit /-
/-- Satisfy the inhabited linter -/
instance inhabitedLiftsToLimit (K : J ⥤ C) (F : C ⥤ D) [CreatesLimit K F] (c : Cone (K ⋙ F))
    (t : IsLimit c) : Inhabited (LiftsToLimit _ _ _ t) :=
  ⟨liftsToLimitOfCreates K F c t⟩
#align category_theory.inhabited_lifts_to_limit CategoryTheory.inhabitedLiftsToLimit
-/

#print CategoryTheory.inhabitedLiftsToColimit /-
instance inhabitedLiftsToColimit (K : J ⥤ C) (F : C ⥤ D) [CreatesColimit K F] (c : Cocone (K ⋙ F))
    (t : IsColimit c) : Inhabited (LiftsToColimit _ _ _ t) :=
  ⟨liftsToColimitOfCreates K F c t⟩
#align category_theory.inhabited_lifts_to_colimit CategoryTheory.inhabitedLiftsToColimit
-/

section Comp

variable {E : Type u₃} [ℰ : Category.{v₃} E]

variable (F : C ⥤ D) (G : D ⥤ E)

#print CategoryTheory.compCreatesLimit /-
instance compCreatesLimit [CreatesLimit K F] [CreatesLimit (K ⋙ F) G] : CreatesLimit K (F ⋙ G)
    where lifts c t :=
    { liftedCone := liftLimit (liftedLimitIsLimit t)
      validLift :=
        (Cones.functoriality (K ⋙ F) G).mapIso (liftedLimitMapsToOriginal (liftedLimitIsLimit t)) ≪≫
          liftedLimitMapsToOriginal t }
#align category_theory.comp_creates_limit CategoryTheory.compCreatesLimit
-/

#print CategoryTheory.compCreatesLimitsOfShape /-
instance compCreatesLimitsOfShape [CreatesLimitsOfShape J F] [CreatesLimitsOfShape J G] :
    CreatesLimitsOfShape J (F ⋙ G) where CreatesLimit := inferInstance
#align category_theory.comp_creates_limits_of_shape CategoryTheory.compCreatesLimitsOfShape
-/

#print CategoryTheory.compCreatesLimits /-
instance compCreatesLimits [CreatesLimitsOfSize.{w, w'} F] [CreatesLimitsOfSize.{w, w'} G] :
    CreatesLimitsOfSize.{w, w'} (F ⋙ G) where CreatesLimitsOfShape := inferInstance
#align category_theory.comp_creates_limits CategoryTheory.compCreatesLimits
-/

#print CategoryTheory.compCreatesColimit /-
instance compCreatesColimit [CreatesColimit K F] [CreatesColimit (K ⋙ F) G] :
    CreatesColimit K (F ⋙ G)
    where lifts c t :=
    { liftedCocone := liftColimit (liftedColimitIsColimit t)
      validLift :=
        (Cocones.functoriality (K ⋙ F) G).mapIso
            (liftedColimitMapsToOriginal (liftedColimitIsColimit t)) ≪≫
          liftedColimitMapsToOriginal t }
#align category_theory.comp_creates_colimit CategoryTheory.compCreatesColimit
-/

#print CategoryTheory.compCreatesColimitsOfShape /-
instance compCreatesColimitsOfShape [CreatesColimitsOfShape J F] [CreatesColimitsOfShape J G] :
    CreatesColimitsOfShape J (F ⋙ G) where CreatesColimit := inferInstance
#align category_theory.comp_creates_colimits_of_shape CategoryTheory.compCreatesColimitsOfShape
-/

#print CategoryTheory.compCreatesColimits /-
instance compCreatesColimits [CreatesColimitsOfSize.{w, w'} F] [CreatesColimitsOfSize.{w, w'} G] :
    CreatesColimitsOfSize.{w, w'} (F ⋙ G) where CreatesColimitsOfShape := inferInstance
#align category_theory.comp_creates_colimits CategoryTheory.compCreatesColimits
-/

end Comp

end Creates

end CategoryTheory

